import Huffman.Codec
import Mathlib

set_option linter.unusedSectionVars false

namespace Huffman

abbrev PackedByteStream := ByteArray

private def magicHeader : List UInt8 :=
  [0x4c, 0x48, 0x55, 0x46] -- "LHUF"

private def byteArrayOfList (xs : List UInt8) : ByteArray :=
  xs.foldl (fun out b => out.push b) ByteArray.empty

private def u16ToBytes (n : Nat) : List UInt8 :=
  [UInt8.ofNat (n / 256), UInt8.ofNat n]

private def u32ToBytes (n : Nat) : List UInt8 :=
  [ UInt8.ofNat (n / 16777216)
  , UInt8.ofNat (n / 65536)
  , UInt8.ofNat (n / 256)
  , UInt8.ofNat n
  ]

private def readByte : List UInt8 → Except String (UInt8 × List UInt8)
  | [] => .error "Unexpected end of archive while reading byte."
  | b :: bs => .ok (b, bs)

private def takeN : Nat → List UInt8 → Except String (List UInt8 × List UInt8)
  | 0, bs => .ok ([], bs)
  | n + 1, [] => .error "Unexpected end of archive while taking bytes."
  | n + 1, b :: bs => do
      let (xs, rest) <- takeN n bs
      pure (b :: xs, rest)

private def readU16 : List UInt8 → Except String (Nat × List UInt8) := fun bs => do
  let (raw, rest) <- takeN 2 bs
  match raw with
  | [b1, b2] => pure (b1.toNat * 256 + b2.toNat, rest)
  | _ => .error "Invalid archive while reading UInt16."

private def readU32 : List UInt8 → Except String (Nat × List UInt8) := fun bs => do
  let (raw, rest) <- takeN 4 bs
  match raw with
  | [b1, b2, b3, b4] =>
      pure
        ( b1.toNat * 16777216
        + b2.toNat * 65536
        + b3.toNat * 256
        + b4.toNat
        , rest
        )
  | _ => .error "Invalid archive while reading UInt32."

private def packBitsAux : List Bool → Nat → Nat → List UInt8 → List UInt8
  | [], curr, count, acc =>
      if count = 0 then
        acc.reverse
      else
        let finalByte := UInt8.ofNat (curr * (2 ^ (8 - count)))
        (finalByte :: acc).reverse
  | bit :: bits, curr, count, acc =>
      let bitNat := if bit then 1 else 0
      let curr' := curr * 2 + bitNat
      let count' := count + 1
      if count' = 8 then
        packBitsAux bits 0 0 (UInt8.ofNat curr' :: acc)
      else
        packBitsAux bits curr' count' acc

private def packBits (bits : BitStream) : List UInt8 :=
  packBitsAux bits 0 0 []

private def bitsOfByte (b : UInt8) : List Bool :=
  let n := b.toNat
  [ (n / 128) % 2 = 1
  , (n / 64) % 2 = 1
  , (n / 32) % 2 = 1
  , (n / 16) % 2 = 1
  , (n / 8) % 2 = 1
  , (n / 4) % 2 = 1
  , (n / 2) % 2 = 1
  , n % 2 = 1
  ]

private def bitsFromBytes (bytes : List UInt8) : List Bool :=
  bytes.bind bitsOfByte

private def readTableEntries :
    Nat → List UInt8 → Except String (FrequencyTable UInt8 × List UInt8)
  | 0, bs => .ok ([], bs)
  | n + 1, bs => do
      let (sym, rest1) <- readByte bs
      let (freq, rest2) <- readU32 rest1
      if freq = 0 then
        throw "Archive contains invalid zero-frequency symbol."
      let (tailEntries, rest3) <- readTableEntries n rest2
      pure ((sym, freq) :: tailEntries, rest3)

private def encodeTableEntries : FrequencyTable UInt8 → Except String (List UInt8)
  | [] => .ok []
  | (sym, freq) :: xs => do
      if freq > 4294967295 then
        throw "Frequency exceeds archive UInt32 limit."
      let rest <- encodeTableEntries xs
      pure (sym :: (u32ToBytes freq ++ rest))

/--
Pack raw bytes into a `.z`-style archive payload.
Format:
`magic(4) | originalLen(u32) | tableSize(u16) | (symbol,u32freq)* | bitLen(u32) | bitPayload`
-/
def packBytes (input : ByteArray) : Except String PackedByteStream := do
  let symbols := input.toList
  if symbols.isEmpty then
    let header := magicHeader ++ u32ToBytes 0 ++ u16ToBytes 0 ++ u32ToBytes 0
    pure (byteArrayOfList header)
  else
    let codec <- buildCodecFromSymbols symbols
    let bits <- encodeSymbols codec symbols
    if symbols.length > 4294967295 then
      throw "Input exceeds archive UInt32 length limit."
    if bits.length > 4294967295 then
      throw "Encoded bitstream exceeds archive UInt32 length limit."
    if codec.table.length > 65535 then
      throw "Frequency table exceeds archive UInt16 count limit."
    let tableBytes <- encodeTableEntries codec.table
    let payload := packBits bits
    let archive :=
      magicHeader
      ++ u32ToBytes symbols.length
      ++ u16ToBytes codec.table.length
      ++ tableBytes
      ++ u32ToBytes bits.length
      ++ payload
    pure (byteArrayOfList archive)

/--
Unpack a `.z`-style archive payload produced by `packBytes`.
-/
def unpackBytes (archive : ByteArray) : Except String ByteArray := do
  let raw := archive.toList
  let (magic, rest0) <- takeN 4 raw
  if magic ≠ magicHeader then
    throw "Invalid archive magic header."
  let (originalLen, rest1) <- readU32 rest0
  let (tableSize, rest2) <- readU16 rest1
  let (table, rest3) <- readTableEntries tableSize rest2
  let (bitLen, payloadBytes) <- readU32 rest3
  let allBits := bitsFromBytes payloadBytes
  if allBits.length < bitLen then
    throw "Archive payload too short for declared bit length."
  let bits := allBits.take bitLen
  if originalLen = 0 then
    if tableSize = 0 ∧ bitLen = 0 then
      pure ByteArray.empty
    else
      throw "Invalid empty archive metadata."
  else
    if tableSize = 0 then
      throw "Non-empty archive has empty frequency table."
    let codec <- buildCodec table
    let decoded <- decodeBits codec bits
    if decoded.length ≠ originalLen then
      throw "Decoded symbol count does not match archive metadata."
    pure (byteArrayOfList decoded)

/--
Pack a file into a `.z` archive file.
-/
def packFile (inputPath outputPath : System.FilePath) : IO (Except String Unit) := do
  let input <- IO.FS.readBinFile inputPath
  match packBytes input with
  | .error e => pure (.error e)
  | .ok packed =>
      IO.FS.writeBinFile outputPath packed
      pure (.ok ())

/--
Unpack a `.z` archive file.
-/
def unpackFile (inputPath outputPath : System.FilePath) : IO (Except String Unit) := do
  let archive <- IO.FS.readBinFile inputPath
  match unpackBytes archive with
  | .error e => pure (.error e)
  | .ok unpacked =>
      IO.FS.writeBinFile outputPath unpacked
      pure (.ok ())

end Huffman
