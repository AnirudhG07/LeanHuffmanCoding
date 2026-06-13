import Huffman.Codec

/-!
# Correctness of the runtime fast path

The optimality theorems (`HfmnProofs/HfmnTree_optimality_lemma.lean`) are stated
about the **spec-layer** `List Bool` encoder `encodeSymbols`. This file proves the
**ByteArray fast path** (`encodeSymbolsBA`, on top of `Huffman/BitIO.lean`) emits
exactly the same bits as that spec encoder — so the fast path is correct *by
equality* to the proven implementation, and inherits everything proven about it.

Main result: `encodeSymbolsBA_eq`.
-/

namespace Huffman

variable {α : Type} [DecidableEq α] [Inhabited α] [Ord α] [HfmnType α]

namespace BitWriter

@[simp] lemma pushBits_nil (w : BitWriter) : w.pushBits [] = w := rfl

@[simp] lemma pushBits_cons (w : BitWriter) (b : Bool) (bs : List Bool) :
    w.pushBits (b :: bs) = (w.pushBit b).pushBits bs := rfl

/-- Writing two bit lists in sequence is writing their concatenation. -/
lemma pushBits_append (w : BitWriter) (a b : List Bool) :
    (w.pushBits a).pushBits b = w.pushBits (a ++ b) := by
  simp [pushBits, List.foldl_append]

/-- Each bit written advances the total bit count by exactly one. -/
@[simp] lemma bitCount_pushBit (w : BitWriter) (bit : Bool) :
    (w.pushBit bit).bitCount = w.bitCount + 1 := by
  simp only [pushBit, bitCount]
  split <;> simp_all [ByteArray.size_push] <;> omega

@[simp] lemma bitCount_pushBits (w : BitWriter) (bs : List Bool) :
    (w.pushBits bs).bitCount = w.bitCount + bs.length := by
  induction bs generalizing w with
  | nil => simp
  | cons b bs ih => simp [ih]; omega

@[simp] lemma bitCount_empty : ({} : BitWriter).bitCount = 0 := by
  simp [bitCount]

end BitWriter

/-- The `BitWriter` fold inside `encodeSymbolsBA`, generalized over the starting
writer, equals writing the spec encoder's bits onto that writer. -/
private lemma encodeBA_foldlM_eq (codec : Codec α) (xs : List α) (w : BitWriter) :
    xs.foldlM (baStep codec) w
      = match encodeSymbols codec xs with
        | .ok bs => .ok (w.pushBits bs)
        | .error e => .error e := by
  induction xs generalizing w with
  | nil => rfl
  | cons x xs ih =>
      rw [List.foldlM_cons]
      cases h : lookupCode codec x with
      | none =>
          have hstep : baStep codec w x =
              .error "Symbol is not present in codec alphabet." := by simp only [baStep, h]
          rw [hstep]
          simp only [encodeSymbols, encodeSymbol, h]
          rfl
      | some code =>
          have hstep : baStep codec w x = .ok (w.pushBits code) := by simp only [baStep, h]
          rw [hstep]
          show xs.foldlM (baStep codec) (w.pushBits code)
              = match encodeSymbols codec (x :: xs) with
                | .ok bs => .ok (w.pushBits bs) | .error e => .error e
          rw [ih]
          simp only [encodeSymbols, encodeSymbol, h]
          cases encodeSymbols codec xs with
          | error e => rfl
          | ok tail =>
              show (Except.ok ((w.pushBits code).pushBits tail) : Except String BitWriter)
                  = Except.ok (w.pushBits (code ++ tail))
              rw [BitWriter.pushBits_append]

/--
**Fast-path correctness.** `encodeSymbolsBA` produces exactly the bits of the
spec encoder `encodeSymbols`, packed MSB-first, together with their exact count.
The new ByteArray encoder is therefore equal to the proven `List Bool` encoder.
-/
theorem encodeSymbolsBA_eq (codec : Codec α) (xs : List α) :
    encodeSymbolsBA codec xs
      = match encodeSymbols codec xs with
        | .ok bs => .ok ((BitWriter.pushBits {} bs).finish, bs.length)
        | .error e => .error e := by
  show (do let w ← xs.foldlM (baStep codec) {}; pure (w.finish, w.bitCount)) = _
  rw [encodeBA_foldlM_eq]
  cases encodeSymbols codec xs with
  | error e => rfl
  | ok bs =>
      show (Except.ok ((BitWriter.pushBits {} bs).finish, (BitWriter.pushBits {} bs).bitCount)
              : Except String (ByteArray × Nat))
          = Except.ok ((BitWriter.pushBits {} bs).finish, bs.length)
      rw [BitWriter.bitCount_pushBits, BitWriter.bitCount_empty, Nat.zero_add]

/-- The fast path's reported bit length equals the spec `encodedBitLength`. -/
theorem encodeSymbolsBA_length (codec : Codec α) (xs : List α) :
    (encodeSymbolsBA codec xs).map (·.2) = encodedBitLength codec xs := by
  rw [encodeSymbolsBA_eq]
  show _ = (do let bits ← encodeSymbols codec xs; pure bits.length)
  cases encodeSymbols codec xs <;> rfl

end Huffman
