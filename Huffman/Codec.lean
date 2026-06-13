import Huffman.HfmnTree_Compression
import Huffman.BitIO
import Mathlib

set_option linter.unusedSectionVars false

abbrev FrequencyTable (α : Type) := AlphaNumList α
abbrev BitStream := BoolList

namespace Huffman

variable {α : Type} [DecidableEq α] [Inhabited α] [Ord α] [HfmnType α]

/-- Runtime codec object for production-style use. -/
structure Codec (α : Type) [DecidableEq α] [Inhabited α] [Ord α] [HfmnType α] where
  tree : HfmnTree α
  table : FrequencyTable α
  codebook : BoolEncList α
deriving Inhabited, Repr

private def hasZeroFreq : FrequencyTable α → Bool
  | [] => false
  | (_, f) :: xs => (f == 0) || hasZeroFreq xs

/--
Validate a frequency table before building a codec:
1. non-empty,
2. no duplicate symbols,
3. strictly positive frequencies.
-/
def validateFrequencyTable (table : FrequencyTable α) : Except String Unit := do
  if table.isEmpty then
    throw "Huffman frequency table must be non-empty."
  if decide (¬ table.symbols.Nodup) then
    throw "Huffman frequency table has duplicate symbols."
  if hasZeroFreq table then
    throw "Huffman frequency table has non-positive frequencies."
  pure ()

/-- Internal codebook builder, exposed for the round-trip correctness proof. -/
def codebookAux (t : HfmnTree α) (pref : BitStream) : BoolEncList α :=
  match t with
  | .Leaf a _ =>
      let effectivePrefix := if pref.isEmpty then [false] else pref
      [(a, effectivePrefix)]
  | .Node l r =>
      codebookAux l (pref ++ [false]) ++ codebookAux r (pref ++ [true])

/--
Extract a runtime codebook from a Huffman tree.
For a single-symbol tree, we force `[false]` instead of `[]`
to keep stream encoding/decoding progress-safe.
-/
def runtimeCodebook (t : HfmnTree α) : BoolEncList α :=
  codebookAux t []

/-- Build a runtime codec from a validated frequency table. -/
def buildCodec (table : FrequencyTable α) : Except String (Codec α) := do
  validateFrequencyTable table
  let tree := HfmnTree.tree table
  let codebook := runtimeCodebook tree
  pure { tree := tree, table := table, codebook := codebook }

/-- Lookup bit-code for a symbol in a codec codebook. -/
def lookupCode (codec : Codec α) (symbol : α) : Option BitStream :=
  (codec.codebook.find? (fun entry => entry.1 == symbol)).map Prod.snd

/-- Public `(symbol, bitLength)` view used by external serializers/headers. -/
def codeLengths (codec : Codec α) : List (α × Nat) :=
  codec.codebook.map (fun (a, code) => (a, code.length))

/-- Encode one symbol with explicit error on unknown symbol. -/
def encodeSymbol (codec : Codec α) (symbol : α) : Except String BitStream :=
  match lookupCode codec symbol with
  | some code => .ok code
  | none =>
      .error "Symbol is not present in codec alphabet."

/-- Encode a symbol stream into a bit stream. -/
def encodeSymbols (codec : Codec α) : List α → Except String BitStream
  | [] => .ok []
  | x :: xs => do
      let head <- encodeSymbol codec x
      let tail <- encodeSymbols codec xs
      pure (head ++ tail)

/-- Decode one symbol by walking the code tree (`false`→left, `true`→right).
Exposed for the round-trip correctness proof. -/
def decodeOne (root : HfmnTree α) :
    Nat → HfmnTree α → BitStream → Except String (α × BitStream)
  | 0, _, _ => .error "Invalid bitstream: code longer than tree."
  | fuel + 1, cur, bits =>
      match cur with
      | .Leaf a _ => .ok (a, bits)
      | .Node l r =>
          match bits with
          | [] => .error "Invalid bitstream: incomplete code at end of stream."
          | b :: rest => decodeOne root fuel (if b then r else l) rest

/-- Decode a whole bit stream via repeated tree walks — O(total bits), no
per-symbol codebook scan. Exposed for the round-trip correctness proof. -/
def decodeMany (root : HfmnTree α) :
    Nat → BitStream → List α → Except String (List α)
  | 0, _, _ => .error "Invalid bitstream: decoder did not converge."
  | fuel + 1, bits, acc =>
      match bits with
      | [] => .ok acc.reverse
      | _ =>
          match decodeOne root (bits.length + 1) root bits with
          | .error e => .error e
          | .ok (sym, rest) => decodeMany root fuel rest (sym :: acc)

/--
Decode a bit stream to symbols.
Returns an error if the stream is malformed for this codec.
-/
def decodeBits (codec : Codec α) (bits : BitStream) : Except String (List α) :=
  match codec.tree with
  | .Leaf a _ => .ok (bits.map (fun _ => a))  -- degenerate single-symbol tree
  | node => decodeMany node (bits.length + 1) bits []

/-- Total encoded bit length of a symbol stream under this codec. -/
def encodedBitLength (codec : Codec α) (xs : List α) : Except String Nat := do
  let bits <- encodeSymbols codec xs
  pure bits.length

private def bumpCount (a : α) : FrequencyTable α → FrequencyTable α
  | [] => [(a, 1)]
  | (b, n) :: rest =>
      if a = b then
        (b, n + 1) :: rest
      else
        (b, n) :: bumpCount a rest

/-- Build a frequency table from raw symbols (first-occurrence order).
Tail-recursive over the input length (safe for large streams). -/
def frequenciesOf (xs : List α) : FrequencyTable α :=
  xs.foldl (fun tbl a => bumpCount a tbl) []

/-- Build codec directly from a raw symbol stream. -/
def buildCodecFromSymbols (xs : List α) : Except String (Codec α) :=
  buildCodec (frequenciesOf xs)

def encodeString (codec : Codec Char) (s : String) : Except String BitStream :=
  encodeSymbols codec s.toList

def decodeToString (codec : Codec Char) (bits : BitStream) : Except String String := do
  let chars <- decodeBits codec bits
  pure (String.ofList chars)

/-- Build a `ByteArray` from a list of bytes. Shared with `FileCodec`. -/
def byteArrayOfList (xs : List UInt8) : ByteArray :=
  xs.foldl (fun out b => out.push b) ByteArray.empty

def encodeBytes (codec : Codec UInt8) (bytes : ByteArray) : Except String BitStream :=
  encodeSymbols codec bytes.toList

def decodeToBytes (codec : Codec UInt8) (bits : BitStream) : Except String ByteArray := do
  let out <- decodeBits codec bits
  pure (byteArrayOfList out)

/-! ### ByteArray bit I/O (performance path)

These avoid materializing a `List Bool` of every bit. Because raw Huffman has no
end-of-stream marker, the encoder returns the exact bit count, which the decoder
needs to ignore the final byte's padding. -/

/-- One step of the ByteArray encoder: append symbol `x`'s code to the writer. -/
def baStep (codec : Codec α) (w : BitWriter) (x : α) : Except String BitWriter :=
  match lookupCode codec x with
  | some code => .ok (w.pushBits code)
  | none => .error "Symbol is not present in codec alphabet."

/-- Encode a symbol stream into MSB-first packed bytes plus the exact bit count. -/
def encodeSymbolsBA (codec : Codec α) (xs : List α) : Except String (ByteArray × Nat) := do
  let w ← xs.foldlM (baStep codec) ({} : BitWriter)
  pure (w.finish, w.bitCount)

/-- Decode one symbol from a `BitReader`, bounded by a remaining-bit budget. -/
private def decodeOneR (root : HfmnTree α) :
    Nat → HfmnTree α → BitReader → Nat → Except String (α × BitReader × Nat)
  | 0, _, _, _ => .error "Invalid bitstream: code longer than tree."
  | fuel + 1, cur, r, budget =>
      match cur with
      | .Leaf a _ => .ok (a, r, budget)
      | .Node l rt =>
          if budget = 0 then .error "Invalid bitstream: incomplete code at end of stream."
          else match r.nextBit with
            | none => .error "Invalid bitstream: unexpected end of reader."
            | some (b, r') => decodeOneR root fuel (if b then rt else l) r' (budget - 1)

private def decodeManyR (root : HfmnTree α) :
    Nat → BitReader → Nat → List α → Except String (List α)
  | 0, _, _, _ => .error "Invalid bitstream: decoder did not converge."
  | fuel + 1, r, budget, acc =>
      if budget = 0 then .ok acc.reverse
      else match decodeOneR root (budget + 1) root r budget with
        | .error e => .error e
        | .ok (sym, r', budget') => decodeManyR root fuel r' budget' (sym :: acc)

/-- Decode the first `bitCount` bits of packed bytes (inverse of `encodeSymbolsBA`). -/
def decodeBA (codec : Codec α) (bytes : ByteArray) (bitCount : Nat) : Except String (List α) :=
  match codec.tree with
  | .Leaf a _ => .ok (List.replicate bitCount a)  -- degenerate single-symbol tree
  | node => decodeManyR node (bitCount + 1) { bytes := bytes } bitCount []

/-- Encode bytes into MSB-first packed bytes plus the exact bit count. -/
def encodeBytesBA (codec : Codec UInt8) (bytes : ByteArray) : Except String (ByteArray × Nat) :=
  encodeSymbolsBA codec bytes.toList

/-- Decode `bitCount` bits of packed bytes back into bytes. -/
def decodeBytesBA (codec : Codec UInt8) (bytes : ByteArray) (bitCount : Nat) :
    Except String ByteArray := do
  let xs ← decodeBA codec bytes bitCount
  pure (byteArrayOfList xs)

end Huffman
