import Huffman.Codec
import Huffman.BitIO
import Mathlib

set_option linter.unusedSectionVars false

/-!
# Unix `pack` / `unpack` `.z` archive format

This module emits and consumes the classic Unix `pack` Huffman format (magic
`0x1f 0x1e`), as decoded by GNU gzip's reference `unpack.c`. See `PACK_FORMAT.md`
for the verified byte-level layout and sources.

On-disk layout (all multi-byte integers big-endian, bits packed MSB-first):

```
magic 0x1F 0x1E | origLen:u32 | maxlev:u8 | leafCount[1..maxlev]:u8
               | literalSymbols (top→bottom, left→right) | packed code bits
```

The deepest level's leaf count is stored **minus 2** and the EOF (`eob`) leaf is
omitted from the symbol list — it is the implicit rightmost-deepest leaf.

Codes are the canonical pack assignment: the `k`-th leaf at bit-length `len`
gets integer code `parents[len] + k` written MSB-first, where
`parents[len] = nodes(len+1) / 2` computed bottom-up. This is exactly gzip's
reconstruction, so any valid file we emit round-trips through the system
`unpack`, and we decode any valid file the system `pack` emits.

Bit I/O goes through `Huffman.BitWriter`/`BitReader` (ByteArray-backed,
MSB-first) so large files do not materialize a `List Bool` of every bit.

Code lengths come from the optimal Huffman tree, then `limitCodeLengths` caps the
maximum depth at 25 (`pack`'s limit) using the standard JPEG/zlib histogram
procedure, which preserves the complete-tree Kraft equality. So any valid input
produces a valid file. The optimal tree is untouched, so the optimality proof is
unaffected.
-/

namespace Huffman

/-- A pack alphabet symbol: an input byte, or the end-of-block marker. -/
inductive PackSym where
  | lit (b : UInt8)
  | eob
deriving DecidableEq, Repr, Inhabited

namespace PackSym

/-- Sort key used to lay symbols out canonically within a bit-length group:
input bytes by value, with `eob` forced last (rightmost). -/
def sortKey : PackSym → Nat
  | .lit b => b.toNat
  | .eob   => 256

instance : Ord PackSym where
  compare a b := compare a.sortKey b.sortKey

end PackSym

instance : HfmnType PackSym where
  default := PackSym.eob

private def magicHeader : List UInt8 := [0x1f, 0x1e]

private def u32ToBytes (n : Nat) : List UInt8 :=
  [ UInt8.ofNat (n / 16777216)
  , UInt8.ofNat (n / 65536)
  , UInt8.ofNat (n / 256)
  , UInt8.ofNat n ]

private def takeN : Nat → List UInt8 → Except String (List UInt8 × List UInt8)
  | 0, bs => .ok ([], bs)
  | _ + 1, [] => .error "Unexpected end of archive."
  | n + 1, b :: bs => do
      let (xs, rest) ← takeN n bs
      pure (b :: xs, rest)

private def readU32 (bs : List UInt8) : Except String (Nat × List UInt8) := do
  let (raw, rest) ← takeN 4 bs
  match raw with
  | [b1, b2, b3, b4] =>
      pure (b1.toNat * 16777216 + b2.toNat * 65536 + b3.toNat * 256 + b4.toNat, rest)
  | _ => .error "Invalid archive while reading UInt32."

/-! ### Tree → canonical pack code lengths -/

/-- Depth of symbol `c` in a runtime tree (`none` if absent). -/
private def treeDepth (t : HfmnTree PackSym) (c : PackSym) : Option Nat :=
  match t with
  | .Leaf v _ => if v = c then some 0 else none
  | .Node l r =>
      match treeDepth l c with
      | some d => some (d + 1)
      | none => (treeDepth r c).map (· + 1)

/-- Insertion sort by a `Nat` key (stable, small lists). -/
private def insByKey {β} (key : β → Nat) (x : β) : List β → List β
  | [] => [x]
  | y :: ys => if key x ≤ key y then x :: y :: ys else y :: insByKey key x ys

private def sortByKey {β} (key : β → Nat) : List β → List β
  | [] => []
  | x :: xs => insByKey key x (sortByKey key xs)

/-- Add `k` to the last element of a non-empty `Nat` list. -/
private def bumpLast (xs : List Nat) (k : Nat) : List Nat :=
  xs.dropLast ++ [xs.getLastD 0 + k]

/--
`parents[len]` for `len = 1..maxlev` (1-indexed by list position).

Bottom-up recurrence matching gzip's `build_tree`:
`nodes := nodes/2; parents[len] := nodes; nodes := nodes + leaves[len]`.
`leavesByLen` is indexed by position (0 ⇒ `len = 1`) and must already include
the `eob` leaf at the deepest level.
-/
private def computeParents (leavesByLen : List Nat) : List Nat :=
  (leavesByLen.reverse.foldl
    (fun (st : Nat × List Nat) (lv : Nat) =>
      let nodes := st.1 / 2
      (nodes + lv, nodes :: st.2))
    (0, [])).2

/-- The canonical code layout derived from per-symbol bit lengths. -/
private structure Layout where
  maxlev : Nat
  /-- Total leaf count per level (1-indexed), including `eob` at the deepest level. -/
  leavesByLen : List Nat
  /-- Symbols per level in canonical left→right order (`eob` last at deepest). -/
  groups : List (List PackSym)
  /-- Canonical bit code for every symbol, as `(value, bitLength)` (MSB-first value). -/
  codebook : List (PackSym × Nat × Nat)

/--
Compute the canonical layout from `lengths` (one `(sym, bitLength)` per symbol,
`eob` included). Forces `eob` to sit at the deepest level (swapping its length
with some deepest symbol if needed — a length swap preserves the complete-tree
Kraft equality), then assigns canonical codes.
-/
private def buildLayout (lengths : List (PackSym × Nat)) : Except String Layout := do
  let maxlev := lengths.foldl (fun m p => max m p.2) 0
  if maxlev = 0 then
    throw "Pack tree is degenerate (need at least two symbols)."
  if maxlev > 25 then
    throw "Internal error: code length exceeds pack limit of 25 after limiting."
  -- Force eob to the deepest level via a length swap if necessary.
  let eobLen := (lengths.find? (·.1 = .eob)).map (·.2) |>.getD maxlev
  let lengths :=
    if eobLen = maxlev then lengths
    else
      match lengths.find? (fun p => p.2 = maxlev ∧ p.1 ≠ .eob) with
      | some (victim, _) =>
          lengths.map (fun p =>
            if p.1 = .eob then (p.1, maxlev)
            else if p.1 = victim then (p.1, eobLen)
            else p)
      | none => lengths
  -- Group symbols by level (1..maxlev), canonical order within each group.
  let groups : List (List PackSym) :=
    (List.range' 1 maxlev).map (fun len =>
      sortByKey PackSym.sortKey
        ((lengths.filter (·.2 = len)).map (·.1)))
  let leavesByLen := groups.map (·.length)
  let parents := computeParents leavesByLen
  -- Assign codes: k-th leaf at level `len` ⇒ parents[len] + k.
  let codebook : List (PackSym × Nat × Nat) :=
    (groups.zipIdx).flatMap (fun (grp, i) =>
      let len := i + 1
      let p := parents.getD i 0
      grp.zipIdx.map (fun (sym, k) => (sym, (p + k, len))))
  pure { maxlev, leavesByLen, groups, codebook }

/--
Limit Huffman code lengths to `maxLen`, preserving the symbol set and the
complete-tree Kraft equality (`Σ 2^(-lᵢ) = 1`).

Uses the standard JPEG/zlib histogram procedure: repeatedly move a pair of
deepest leaves up one level and push a shallower leaf down, which keeps both the
leaf count and the Kraft sum invariant while reducing the maximum depth. New
lengths are then re-assigned to symbols shortest-first by current length (a
frequency proxy), so frequent symbols keep short codes.

The optimal Huffman tree (`HfmnTree.tree`) is untouched — this only post-processes
the *emitted* pack code lengths, so the optimality proof is unaffected.
-/
private def limitCodeLengths (maxLen : Nat) (lengths : List (PackSym × Nat)) :
    List (PackSym × Nat) :=
  let maxOld := lengths.foldl (fun m p => max m p.2) 0
  if maxOld ≤ maxLen then lengths
  else Id.run do
    -- Histogram of current code lengths, indexed 0..maxOld.
    let mut bits : Array Nat := Array.replicate (maxOld + 1) 0
    for entry in lengths do
      bits := bits.set! entry.2 (bits[entry.2]! + 1)
    let nSyms := lengths.length
    -- For each over-deep level (deepest first), move its leaves up.
    for i in (List.range' (maxLen + 1) (maxOld - maxLen)).reverse do
      -- At most `nSyms` moves drain level `i` (each move removes 2 from it).
      for _ in List.range nSyms do
        if bits[i]! > 0 then
          -- Find the deepest level `j < i-1` that still has a leaf to push down.
          let mut j := i - 2
          for _ in List.range i do
            if j ≥ 1 ∧ bits[j]! == 0 then j := j - 1
          bits := bits.set! i (bits[i]! - 2)
          bits := bits.set! (i - 1) (bits[i - 1]! + 1)
          bits := bits.set! (j + 1) (bits[j + 1]! + 2)
          bits := bits.set! j (bits[j]! - 1)
    -- Re-assign lengths to symbols, shortest current length first.
    let sorted := sortByKey (fun p => p.2 * 257 + p.1.sortKey) lengths
    let mut out : List (PackSym × Nat) := []
    let mut rest := sorted
    for l in List.range' 1 maxLen do
      let (grp, tail) := rest.splitAt bits[l]!
      out := out ++ grp.map (fun p => (p.1, l))
      rest := tail
    pure out

/-! ### Encoder -/

/--
Pack raw bytes into a Unix `pack` `.z` archive payload.
-/
def packBytes (input : ByteArray) : Except String ByteArray := do
  let bytes := input.toList
  if bytes.isEmpty then
    -- Empty input: magic + origLen 0, no tree. (Our own round-trip; the system
    -- `pack` rejects empty input, so this branch is not interoperable.)
    pure (byteArrayOfList (magicHeader ++ u32ToBytes 0))
  else
    -- Frequencies over bytes, plus eob with weight 1.
    let byteFreqs : FrequencyTable PackSym := frequenciesOf (bytes.map PackSym.lit)
    let table : FrequencyTable PackSym := (PackSym.eob, 1) :: byteFreqs
    let tree := HfmnTree.tree table
    -- Per-symbol code lengths from the optimal tree.
    let symbols := tree.chars
    let lengths : List (PackSym × Nat) ←
      symbols.foldrM (fun s acc =>
        match treeDepth tree s with
        | some d => pure ((s, d) :: acc)
        | none => throw "Internal error: tree symbol has no depth.") []
    let layout ← buildLayout (limitCodeLengths 25 lengths)
    -- Header: deepest level count stored minus 2 (the eob + its sibling).
    let storedCounts :=
      layout.leavesByLen.dropLast ++ [layout.leavesByLen.getLastD 0 - 2]
    for c in storedCounts do
      if c > 255 then throw "Level leaf count exceeds 255 (unsupported by pack header)."
    let countBytes := storedCounts.map UInt8.ofNat
    -- Literal symbol bytes: every group in order, excluding eob.
    let literalBytes : List UInt8 :=
      layout.groups.flatMap (fun grp =>
        grp.filterMap (fun s => match s with | .lit b => some b | .eob => none))
    -- O(1) code table indexed by byte value, plus the eob code.
    let mut litCodes : Array (Nat × Nat) := Array.replicate 256 ((0, 0) : Nat × Nat)
    let mut eobCode : Nat × Nat := (0, 0)
    for entry in layout.codebook do
      match entry.1 with
      | .lit b => litCodes := litCodes.set! b.toNat entry.2
      | .eob   => eobCode := entry.2
    -- Payload bits: each input byte's code (MSB-first), then the eob code.
    let payload : ByteArray := Id.run do
      let mut w : BitWriter := {}
      for b in bytes do
        let (v, l) := litCodes[b.toNat]!
        w := w.pushCode v l
      w := w.pushCode eobCode.1 eobCode.2
      pure w.finish
    let header : ByteArray := byteArrayOfList
      (magicHeader
        ++ u32ToBytes bytes.length
        ++ [UInt8.ofNat layout.maxlev]
        ++ countBytes
        ++ literalBytes)
    pure (header ++ payload)

/-! ### Decoder -/

/-- Split `xs` into consecutive chunks of the given sizes. -/
private def chunkBy : List Nat → List UInt8 → Except String (List (List UInt8))
  | [], _ => .ok []
  | n :: ns, xs => do
      let (grp, rest) ← takeN n xs
      let tail ← chunkBy ns rest
      pure (grp :: tail)

/-- Walk the canonical tree consuming bits MSB-first, returning `(len, ordinal, reader)`. -/
private def walk (parents : List Nat) : Nat → Nat → Nat → BitReader →
    Except String (Nat × Nat × BitReader)
  | 0, _, _, _ => .error "Invalid pack stream: code longer than tree depth."
  | fuel + 1, len, v, r =>
      let p := parents.getD (len - 1) 0
      if v < p then
        match r.nextBit with
        | none => .error "Invalid pack stream: ended mid-code."
        | some (b, r') => walk parents fuel (len + 1) (v * 2 + (if b then 1 else 0)) r'
      else
        .ok (len, v - p, r)

private def decodeLoop
    (parents : List Nat) (maxlev eobOrd : Nat) (litGroups : List (List UInt8)) :
    Nat → BitReader → ByteArray → Except String ByteArray
  | 0, _, _ => .error "Invalid pack stream: decoder did not converge."
  | fuel + 1, r, acc =>
      match r.nextBit with
      | none => .error "Invalid pack stream: ended before EOF marker."
      | some (b, r1) => do
          let (len, ord, r2) ← walk parents (maxlev + 1) 1 (if b then 1 else 0) r1
          if len = maxlev ∧ ord = eobOrd then
            pure acc
          else
            match (litGroups.getD (len - 1) [])[ord]? with
            | some byte => decodeLoop parents maxlev eobOrd litGroups fuel r2 (acc.push byte)
            | none => .error "Invalid pack stream: symbol index out of range."

/--
Unpack a Unix `pack` `.z` archive payload.
-/
def unpackBytes (archive : ByteArray) : Except String ByteArray := do
  let raw := archive.toList
  let (magic, rest0) ← takeN 2 raw
  if magic ≠ magicHeader then
    throw "Invalid pack magic (expected 0x1f 0x1e)."
  let (origLen, rest1) ← readU32 rest0
  if origLen = 0 then
    pure ByteArray.empty
  else do
    let (maxlevByte, rest2) ← match rest1 with
      | b :: bs => pure (b, bs)
      | [] => throw "Unexpected end of archive while reading max level."
    let maxlev := maxlevByte.toNat
    if maxlev = 0 ∨ maxlev > 25 then
      throw "Invalid pack max code length."
    let (countBytes, rest3) ← takeN maxlev rest2
    let stored := countBytes.map UInt8.toNat
    -- leavesA: deepest +1 ⇒ number of literal bytes per level (eob excluded).
    let leavesA := bumpLast stored 1
    -- leavesB: deepest +2 ⇒ tree leaf counts (eob included).
    let leavesB := bumpLast stored 2
    let literalCount := leavesA.foldl (· + ·) 0
    let (literals, rest4) ← takeN literalCount rest3
    let litGroups ← chunkBy leavesA literals
    let parents := computeParents leavesB
    let eobOrd := leavesA.getLastD 0  -- = deepest leaf count - 1
    let reader : BitReader := { bytes := byteArrayOfList rest4 }
    let decoded ← decodeLoop parents maxlev eobOrd litGroups (reader.size + 1) reader ByteArray.empty
    if decoded.size ≠ origLen then
      throw "Decoded length does not match archive metadata."
    pure decoded

/-! ### File helpers -/

/-- Pack a file into a `pack` `.z` archive. -/
def packFile (inputPath outputPath : System.FilePath) : IO (Except String Unit) := do
  let input ← IO.FS.readBinFile inputPath
  match packBytes input with
  | .error e => pure (.error e)
  | .ok packed => IO.FS.writeBinFile outputPath packed; pure (.ok ())

/-- Unpack a `pack` `.z` archive file. -/
def unpackFile (inputPath outputPath : System.FilePath) : IO (Except String Unit) := do
  let archive ← IO.FS.readBinFile inputPath
  match unpackBytes archive with
  | .error e => pure (.error e)
  | .ok unpacked => IO.FS.writeBinFile outputPath unpacked; pure (.ok ())

end Huffman
