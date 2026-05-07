import Huffman.HfmnTree_Compression
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

private def codebookAux (t : HfmnTree α) (pref : BitStream) : BoolEncList α :=
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

private def findPrefixMatch (codebook : BoolEncList α) (bits : BitStream) :
    Option (α × BitStream) :=
  match codebook with
  | [] => none
  | (a, code) :: rest =>
      if code.isPrefixOf bits then
        some (a, bits.drop code.length)
      else
        findPrefixMatch rest bits

private def decodeWithFuel
    (codebook : BoolEncList α) :
    Nat → BitStream → List α → Except String (List α)
  | 0, _, _ => .error "Invalid bitstream: decoder did not converge."
  | fuel + 1, bits, acc =>
      if bits.isEmpty then
        .ok acc.reverse
      else
        match findPrefixMatch codebook bits with
        | none => .error "Invalid bitstream: no code matches current prefix."
        | some (sym, rest) => decodeWithFuel codebook fuel rest (sym :: acc)

/--
Decode a bit stream to symbols.
Returns an error if the stream is malformed for this codec.
-/
def decodeBits (codec : Codec α) (bits : BitStream) : Except String (List α) :=
  decodeWithFuel codec.codebook (bits.length + 1) bits []

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

/-- Build a frequency table from raw symbols. -/
def frequenciesOf : List α → FrequencyTable α
  | [] => []
  | x :: xs => bumpCount x (frequenciesOf xs)

/-- Build codec directly from a raw symbol stream. -/
def buildCodecFromSymbols (xs : List α) : Except String (Codec α) :=
  buildCodec (frequenciesOf xs)

def encodeString (codec : Codec Char) (s : String) : Except String BitStream :=
  encodeSymbols codec s.toList

def decodeToString (codec : Codec Char) (bits : BitStream) : Except String String := do
  let chars <- decodeBits codec bits
  pure (String.ofList chars)

private def byteArrayOfList (xs : List UInt8) : ByteArray :=
  xs.foldl (fun out b => out.push b) ByteArray.empty

def encodeBytes (codec : Codec UInt8) (bytes : ByteArray) : Except String BitStream :=
  encodeSymbols codec bytes.toList

def decodeToBytes (codec : Codec UInt8) (bits : BitStream) : Except String ByteArray := do
  let out <- decodeBits codec bits
  pure (byteArrayOfList out)

end Huffman
