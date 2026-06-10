import Huffman

/-!
# HuffmanTest

Compile-time round-trip and golden checks for the runtime API. Built in CI as a
`lean_lib` target; a failing `#guard` is a build error. Kept to small inputs so
elaboration stays fast — large-file / deep-tree stress is exercised by the
`scripts/` runners, not here.
-/

open Huffman

/-! ## pack / unpack `.z` round-trips -/

private def packRoundtrips (s : String) : Bool :=
  match packBytes s.toUTF8 with
  | .ok p => match unpackBytes p with
             | .ok o => o.toList == s.toUTF8.toList
             | .error _ => false
  | .error _ => false

#guard ["", "a", "aaaa", "ab", "abracadabra", "hello world",
        "mississippi river", "the quick brown fox jumps over the lazy dog",
        "aaaaaaaaaabbbbbccd"].all packRoundtrips

-- Byte-exact Unix `pack` golden for "aaaa".
#guard
  (match packBytes "aaaa".toUTF8 with
   | .ok ba => ba.toList == [0x1f, 0x1e, 0x00, 0x00, 0x00, 0x04, 0x01, 0x00, 0x61, 0x08]
   | .error _ => false)

-- Empty input: magic + zero length, no tree.
#guard
  (match packBytes "".toUTF8 with
   | .ok ba => ba.toList == [0x1f, 0x1e, 0x00, 0x00, 0x00, 0x00]
   | .error _ => false)

/-! ## Codec round-trips (List Bool and ByteArray paths) -/

private def codecRoundtrips (s : String) : Bool :=
  match buildCodecFromSymbols s.toList with
  | .ok c =>
      (match (do let b ← encodeSymbols c s.toList; decodeBits c b) with
       | .ok o => o == s.toList | .error _ => false)
  | .error _ => false

private def codecBARoundtrips (s : String) : Bool :=
  match buildCodecFromSymbols s.toList with
  | .ok c =>
      (match (do let (ba, n) ← encodeSymbolsBA c s.toList; decodeBA c ba n) with
       | .ok o => o == s.toList | .error _ => false)
  | .error _ => false

#guard ["a", "aaaa", "abracadabra", "hello world", "mississippi"].all codecRoundtrips
#guard ["a", "aaaa", "abracadabra", "hello world", "mississippi"].all codecBARoundtrips

/-! ## Frequency table and bit packing -/

#guard frequenciesOf "abracadabra".toList
        == [('a', 5), ('b', 2), ('r', 2), ('c', 1), ('d', 1)]

-- BitWriter is MSB-first and left-justifies the final partial byte.
#guard (BitWriter.pushBits {} [false, false, false, false, true]).finish.toList == [0x08]
#guard (BitWriter.pushCode {} 5 3).finish.toList == [0xA0]  -- 101 ⇒ 0b10100000
#guard (BitWriter.pushBits {} []).finish.toList == []
