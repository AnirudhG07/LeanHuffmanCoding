# CLAUDE.md

Guidance for working in this repository.

## What this is

A **Lean 4** library that implements Huffman coding *and* formally proves the
algorithm correct and optimal in the same codebase. Originally a course project
for IISc Proofs & Programs 2025. The goal is to grow it into an industry-grade
Huffman compression library with a runtime-focused API and `pack`/`unpack`
(Linux `gzip`-family) compatibility.

The defining characteristic: every runtime function has a proof-side
counterpart, and the two are bridged so the executable code inherits the
optimality/correctness theorems. Do not let runtime code and proof code drift
apart — when you change one, update the bridge.

## Toolchain & build

- Lean `leanprover/lean4:v4.29.0` (see `lean-toolchain`), Mathlib pinned to
  `v4.29.0` (see `lakefile.toml`). Do **not** bump these casually — Mathlib
  upgrades routinely break proofs; the last commit was a deliberate downgrade to
  the stable pin.
- Build everything: `lake build`
- Build just the library: `lake build Huffman`
- The build depends on the prebuilt Mathlib cache in `.lake/`. A cold build of
  Mathlib is very slow; prefer `lake exe cache get` if the cache is missing.
- CI (`.github/workflows/lean_action_ci.yml`) greps for `sorry`/`admit` then runs
  `lean-action`, i.e. a bare `lake build`. The default targets are `Huffman`,
  `HuffmanProofs`, and `HuffmanTest`, so **a PR is only green if the runtime
  library, the optimality proofs, and the `#guard` tests all build with zero
  `sorry` and no errors.** Verify locally (`lake build`) before pushing.
- `lake build Huffman` builds just the runtime library (what consumers depend on).
  `lake build HuffmanProofs` / `HuffmanTest` build the proofs / tests in isolation.

## Module layout

Public entrypoint is `Huffman.lean`, which re-exports the runtime modules.
`HuffmanProofs.lean` (proof aggregator) and `HuffmanTest.lean` (`#guard` tests)
are separate `lean_lib` targets built in CI but not imported by consumers.

| File | Role |
|------|------|
| `Huffman/HfmnTree_Construction.lean` | **Proof-side** core: the abstract `HuffmanTree α` inductive, `alphabet`, `consistent`, `depth`, `height`, `freq`, `weight`, `cost` (weighted path length), `optimum`, `minima`. This is the source of truth for the abstract model. |
| `Huffman/HfmnTree_Compression.lean` | Proof-side `huffman` construction algorithm (`insortTree`/`uniteTrees`), **and** the runtime `HfmnTree α` inductive (`Node`/`Leaf`), plus the bridge (`ofProofTree`, `toProofTree`, `proofForest`, `HfmnTree.tree`). Also `BoolList`/`AlphaNumList` abbrevs, `HfmnType` class, and the total `HfmnTree.encode?` (panic-free runtime encoder; the proof-used `HfmnTree.encode` is kept frozen). |
| `Huffman/BitIO.lean` | ByteArray-backed `BitWriter`/`BitReader` (MSB-first, byte-identical to the pack layout). Plain core Lean (no Mathlib); the perf path so large files never materialize a `List Bool`. |
| `Huffman/Codec.lean` | Production runtime API in `namespace Huffman`: `Codec` struct, `buildCodec`, `encodeSymbols`/`decodeBits` (List Bool), the faster `encodeSymbolsBA`/`decodeBA`/`encodeBytesBA`/`decodeBytesBA` (ByteArray + bit count), codebook lookup, `String`/`ByteArray` wrappers. Decoder is a tree walk (O(total bits)); `frequenciesOf` is tail-recursive. |
| `Huffman/FileCodec.lean` | **Real Unix `pack`/`unpack` `.z` format** (magic `0x1f 0x1e`): `packBytes`/`unpackBytes`, `packFile`/`unpackFile`. Imported by `Huffman.lean`. Canonical code-length serialization with EOF + MSB packing via `BitIO`, plus JPEG-style code-length limiting (`limitCodeLengths`, ≤25). See `PACK_FORMAT.md`. |
| `Huffman/HfmnProofs/*.lean` | Optimality, prefix-freeness, and uniqueness proofs, plus the bridge theorems connecting the runtime API to the abstract optimality result. |

### Proof files (`HfmnProofs/`)
- `HfmnTree_transformations.lean` — structural ops (sibling, merge/split, swaps) used in the optimality argument.
- `HfmnTree_optimality.lean` — abstract optimality: `optimum_huffman`.
- `HfmnTree_uniqueness.lean` — `Vertex` abstraction; all codes/leaves distinct.
- `HfmnTree_prefixfreeness.lean` — prefix-freeness of the code.
- `HfmnTree_optimality_lemma.lean` — the **runtime bridge**. Key public theorems:
  - `leastEncodedData_eq_wpl` — encoded bit count = weighted path length.
  - `HfmnTree.weightedPathLength_optimal` — `HfmnTree.tree` is optimal among admissible runtime trees.
  - `Huffman.leastEncodedData_optimal` — the public bit-count API is minimal.

Trust the filesystem layout above as the source of truth for file names.

## Architecture: the runtime↔proof bridge

- Abstract `HuffmanTree` (lowercase constructors `leaf`/`node`, carries weights
  everywhere) lives in Construction; it's what the proofs reason about.
- Runtime `HfmnTree` (uppercase `Leaf`/`Node`) is what executable code uses.
- `HfmnTree.tree : AlphaNumList α → HfmnTree α` is the canonical public
  constructor. It runs the proof-side `huffman` algorithm then `ofProofTree`s the
  result, so the runtime tree *is* the proven-optimal tree by construction.
- `toProofTree` converts back (using an input frequency table) so runtime trees
  can be stated about in proof-land.

When adding runtime functionality that should be "optimal" or "correct", define
it on `HfmnTree`/`Codec`, then prove the property by transporting along this
bridge — don't re-prove from scratch.

## Conventions

- `autoImplicit false` and `pp.unicode.fun true` are set globally.
- Proofs lean heavily on `grind`, `aesop`, `simp`, and `@[simp]`/`@[grind .]`
  attributes on definitions and lemmas. Follow the surrounding style.
- `set_option linter.unusedSectionVars false` is used in several files;
  trimming linter warnings is open cleanup work (see TODO).
- Runtime APIs return `Except String _` with human-readable error messages
  rather than panicking. Preserve that pattern. (`HfmnTree.encode` has a
  `panic!` on an unreachable branch and is kept only for the proofs; runtime code
  should use the total `HfmnTree.encode?`.)
- Decoders stay total via explicit fuel (`bits.length + 1` / `reader.size + 1`).

## pack/unpack compatibility (implemented)

`FileCodec.lean` emits/consumes the **real Unix `pack` `.z` format** (magic
`0x1f 0x1e`, big-endian original length, per-level leaf counts with the deepest
count stored −2, canonical MSB-first codes, implicit rightmost-deepest EOF),
mirroring gzip's reference `unpack.c`. Code lengths come from the proven-optimal
`HfmnTree.tree`, then `limitCodeLengths` caps depth at 25 (JPEG-style, Kraft-
preserving) so any valid input produces a valid file. `PACK_FORMAT.md` has the
verified byte layout, the compatibility bar, and the verification recipe.

Compatibility bar (we do NOT replicate `pack`'s exact tie-breaking): our output
must decode with the system `unpack`, and our decoder must read system `pack`
output. **Interop against the system binary is still unverified** — this machine
has no `pack` (only `gzip`, which dropped pack support). When `pack` is installed,
run the recipe in `PACK_FORMAT.md` and add golden `.z` round-trip tests.

## Gotchas

- Don't add a second copy of the optimality proof under a new filename.
- A passing-looking edit can still leave `sorry`/`admit`; grep for them before
  declaring a proof done (CI also greps).
- The `eg₁` example and commented `#eval`s are sanity checks; keep them working.
- The optimality proofs depend on the **spec-layer** defs in
  `HfmnTree_Compression.lean` (`HfmnTree.encode`, `encodedList`,
  `Huffman.leastEncodedData`, `HfmnTree.depth`). Treat those as frozen — add
  parallel runtime defs (as `encode?`/`*BA`/`BitIO` do) rather than changing them,
  or you'll break `HuffmanProofs`.
