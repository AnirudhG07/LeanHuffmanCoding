# Changelog

All notable changes to this project are documented here.

## [Unreleased]

### Added
- **Unix `pack` `.z` format** (`Huffman/FileCodec.lean`): `packBytes`/`unpackBytes`
  and `packFile`/`unpackFile` emit/consume the real classic Huffman `pack` format
  (magic `0x1f 0x1e`), mirroring gzip's reference `unpack.c`. Replaces the previous
  bespoke "LHUF" container.
- **Code-length limiting** (`limitCodeLengths`, ≤25 levels, JPEG/zlib histogram
  method) so any input produces a valid `.z` file.
- **`Huffman/BitIO.lean`**: ByteArray-backed `BitWriter`/`BitReader` (MSB-first).
- **ByteArray codec fast path**: `encodeSymbolsBA`/`decodeBA`/`encodeBytesBA`/
  `decodeBytesBA` (returns/takes the exact bit count).
- **`HfmnTree.encode?`**: total, panic-free runtime encoder.
- **`HuffmanProofs` and `HuffmanTest` `lean_lib` targets**: the optimality proofs
  and `#guard` round-trip/golden tests now build by default and are CI-gated.
- CI now greps for `sorry`/`admit` and builds proofs + tests.
- `scripts/PackFile.lean`, `scripts/UnpackFile.lean` shell runners.
- `PACK_FORMAT.md` documenting the verified byte layout, compatibility bar, and
  verification recipe.

### Changed
- `Codec` decoder is now an O(total-bits) tree walk (was a per-symbol linear
  codebook scan).
- `frequenciesOf` is tail-recursive (safe for large streams).
- `lakefile.toml`: removed the duplicate Mathlib `require`; added `description`
  and meaningful `keywords`; default targets build library + proofs + tests.
- `FileCodec` is now imported by `Huffman.lean`; `byteArrayOfList` de-duplicated.

### Pending
- Verify interop against the system `pack`/`unpack` binary; add golden `.z` tests.
- Trim remaining linter warnings.
