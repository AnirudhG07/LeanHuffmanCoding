# Unix `pack` / `unpack` `.z` Format — Implementation Notes

Target for real Linux `pack`/`unpack` compatibility. This is the **classic Huffman
`pack` format** (magic `1f 1e`), distinct from `compress` (`.Z`, LZW, `1f 9d`) and
`gzip` (`.gz`, DEFLATE, `1f 8b`). Sources verified June 2026 — see bottom.

## On-disk layout

```
offset  size  field
0       2     magic: 0x1F 0x1E
2       4     original (uncompressed) length, BIG-ENDIAN uint32
6       1     maxlev  — maximum tree depth (number of code-length levels)
7       N     per-level leaf counts, one byte per level 1..maxlev.
              The LAST level's count is stored MINUS 2 (the deepest level holds
              between 2 and 257 leaves, which won't fit in a byte; -2 makes it fit).
...     M     leaf symbol bytes, listed top→bottom, left→right (one byte each).
              Total = (sum of level counts) - 1, because the EOF leaf is NOT
              written — it is implicitly the deepest, right-most leaf.
...     ...   packed code bits, MSB-first within each byte.
```

### Canonical-code reconstruction (decoder side, must match encoder)
- The tree is **complete and left-aligned**, with the EOF symbol occupying the
  single deepest right-most position. Knowing the leaf count per level + the
  symbol list is enough to rebuild the exact tree and code assignment.
- Codes are assigned by walking levels: `0` for every left branch, `1` for every
  right branch; left-aligned canonical assignment per level.
- EOF is appended as an extra symbol at the deepest level so it can be omitted
  from the on-disk symbol list (it's always the last/rightmost).

### Bit packing
- Payload is the concatenation of each input byte's code, then the EOF code,
  packed **MSB-first**: the first code bit goes into bit 7 of the first output
  byte. Trailing bits in the final byte are pad (decoder stops at EOF code, so
  padding is ignored).

## What this requires beyond the current code

The existing `HfmnTree.tree` produces an optimal tree but NOT in pack's canonical
left-aligned-by-level form, and has **no EOF symbol**. Pack compatibility is a
serialization layer driven by **code lengths**, not by the tree's pointer shape:

1. Compute Huffman **code lengths** per symbol (can reuse the optimal tree:
   `depth` gives lengths; optimality already proven).
2. Add an EOF symbol at the max depth.
3. Build the canonical left-aligned code assignment from the length multiset.
4. Serialize header (magic, BE length, maxlev, level counts w/ last −2, symbols).
5. Bit-pack codes MSB-first; emit EOF last.
6. Decoder: parse header, rebuild canonical tree, walk bits to EOF.

## Implementation status (done)

`Huffman/FileCodec.lean` now implements this format, replacing the old "LHUF"
container. `packBytes`/`unpackBytes`/`packFile`/`unpackFile` are wired into
`Huffman.lean`. Code lengths come from the proven-optimal `HfmnTree.tree`; the
canonical code assignment mirrors gzip's `unpack.c` exactly (`parents[len]`
recurrence, `eob = leaves[maxlen]-1`, deepest count stored −2). `eob` is forced
to the deepest level via a length swap when the optimal tree would place it
shallower (a length swap preserves the complete-tree Kraft equality).

Bit I/O goes through `Huffman/BitIO.lean` (`BitWriter`/`BitReader`, ByteArray-
backed, MSB-first) so large files never materialize a `List Bool`.

**Code-length limiting is implemented**: `limitCodeLengths 25` post-processes the
optimal tree's lengths with the standard JPEG/zlib histogram procedure (move a
pair of deepest leaves up, push a shallower leaf down — leaf count and Kraft sum
preserved). So inputs whose optimal tree exceeds 25 levels still produce a valid
file instead of erroring. The optimal tree itself is untouched, so the optimality
proof is unaffected.

Verified: self round-trip on empty/single/repeated/skewed/long (1 MB) inputs and
on Fibonacci-weighted inputs forcing natural depth 26–28 (limited to 25); the
`"aaaa"` archive is byte-exact `1f 1e 00 00 00 04 01 00 61 08`. These are encoded
as `#guard` checks in `HuffmanTest.lean` (CI-gated).

### Realistic compatibility bar
We do **not** reproduce real `pack`'s exact tie-breaking, so our `.z` for a given
input need not be byte-identical to the system `pack`'s. Both are *valid* pack
files. What must hold (and the canonical algorithm guarantees):
- our `pack` output decodes with the system `unpack` / `gzip -d`;
- our `unpack` decodes the system `pack`'s output.

### Verification recipe (once `pack` is installed)
```sh
# our pack → system unpack
printf 'mississippi river' > t.in
lake env lean --run scripts/PackFile.lean t.in t.in.z   # (helper that calls packFile)
unpack t.in.z && diff t.in t          # system unpack must reproduce the input
# system pack → our unpack
pack -f t.in && # produces t.in.z
lake env lean --run scripts/UnpackFile.lean t.in.z out.bin && diff out.bin t.in
```

## Testing constraints (this machine)
- **No `pack`/`unpack` binaries installed** — only `gzip 1.10`. Modern gzip has
  *dropped* pack-`.z` decompression, so we cannot assume `gzip -d` validates our
  output. Options: (a) install GNU `pack` (part of older `gzip`/`ncompress`-era
  tooling) to round-trip; (b) commit a known-good reference `.z` file produced by
  a real `pack` and test decode against it; (c) self-round-trip (encode→decode)
  for internal correctness, plus byte-exact comparison to a checked-in golden.
- Minimum bar before claiming compatibility: byte-exact match to a real
  `pack`-produced `.z` for at least one non-trivial input, both directions.

## Sources
- pack (Unix) — Just Solve the File Format Problem: http://fileformats.archiveteam.org/wiki/Pack_(Unix)
- "An ode to pack: gzip's forgotten decompressor" — Vidar Holen: https://www.vidarholen.net/contents/blog/?p=691
- MKS Toolkit `pack(1)` / `unpack(1)` man pages: https://www.mkssoftware.com/docs/man1/pack.1.asp
