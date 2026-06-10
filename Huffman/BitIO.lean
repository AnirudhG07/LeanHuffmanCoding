/-!
# ByteArray-backed bit I/O

A `BitWriter` accumulates bits into a `ByteArray` (one byte at a time, no
`List Bool` materialization), and a `BitReader` consumes bits from a `ByteArray`.

Both use **MSB-first** ordering within each byte, byte-identical to the original
`packBitsAux`/`bitsOfByte` so the Unix `pack` `.z` payload layout is preserved:
the first bit written lands in bit 7 of the first byte, and the final partial
byte is left-justified (low bits zero-padded).

This module is plain core Lean (no Mathlib) and is imported by the runtime codecs
but never by the proof stack.
-/

namespace Huffman

/-- Accumulates bits MSB-first into a `ByteArray`. -/
structure BitWriter where
  /-- Completed bytes. -/
  bytes : ByteArray := ByteArray.empty
  /-- Partial byte under construction (MSB-aligned via `*2`), holding `count` bits. -/
  cur : Nat := 0
  /-- Number of bits currently buffered in `cur` (0–7). -/
  count : Nat := 0
  deriving Inhabited

namespace BitWriter

/-- Append a single bit (MSB-first). -/
@[inline] def pushBit (w : BitWriter) (b : Bool) : BitWriter :=
  let cur := w.cur * 2 + (if b then 1 else 0)
  let count := w.count + 1
  if count == 8 then
    { bytes := w.bytes.push (UInt8.ofNat cur), cur := 0, count := 0 }
  else
    { w with cur := cur, count := count }

/-- Append a list of bits (MSB-first). -/
@[inline] def pushBits (w : BitWriter) (bs : List Bool) : BitWriter :=
  bs.foldl pushBit w

/-- Append the low `len` bits of `value`, MSB-first (bit `len-1` first). -/
def pushCode (w : BitWriter) (value len : Nat) : BitWriter :=
  let rec go (w : BitWriter) (i : Nat) : BitWriter :=
    match i with
    | 0 => w
    | i + 1 => go (w.pushBit (value.testBit i)) i
  go w len

/-- Finalize, left-justifying any partial final byte (low bits zero-padded). -/
def finish (w : BitWriter) : ByteArray :=
  if w.count == 0 then w.bytes
  else w.bytes.push (UInt8.ofNat (w.cur * (2 ^ (8 - w.count))))

/-- Total number of bits written so far (completed + buffered). -/
@[inline] def bitCount (w : BitWriter) : Nat := w.bytes.size * 8 + w.count

end BitWriter

/-- Reads bits MSB-first from a `ByteArray`. -/
structure BitReader where
  /-- Underlying bytes. -/
  bytes : ByteArray
  /-- Current bit position (0-based, MSB-first within each byte). -/
  pos : Nat := 0
  deriving Inhabited

namespace BitReader

/-- Total number of readable bits. -/
@[inline] def size (r : BitReader) : Nat := r.bytes.size * 8

/-- `true` once all bits have been consumed. -/
@[inline] def atEnd (r : BitReader) : Bool := r.pos ≥ r.size

/-- Read the next bit (MSB-first), or `none` at end of stream. -/
@[inline] def nextBit (r : BitReader) : Option (Bool × BitReader) :=
  if r.pos < r.size then
    let byte := r.bytes.get! (r.pos / 8)
    let bit := byte.toNat.testBit (7 - r.pos % 8)
    some (bit, { r with pos := r.pos + 1 })
  else
    none

end BitReader

end Huffman
