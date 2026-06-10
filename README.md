# LeanHuffmanCoding

A **Lean 4** library that implements Huffman coding *and* formally proves the
algorithm optimal in the same codebase. Originally a course project for
[IISc, Proofs and Programs 2025](https://github.com/proofs-and-programs/proofs-and-programs-25).

The defining feature: every runtime function is bridged to a proof-side
counterpart, so the executable code inherits the optimality theorem. It also
emits/consumes the classic Unix `pack` `.z` format.

> [!Note]
> Work in progress. Interop against the system `pack`/`unpack` binary is not yet
> verified (see *Status* below).

## Features

- Huffman tree construction from `(symbol, frequency)` tables.
- **Formal proof of optimality** of the Huffman algorithm (`HuffmanProofs`), bridged
  to the runtime API (`Huffman.leastEncodedData_optimal`).
- A reusable `Codec` with symbol↔code lookup, stream encode/decode, and explicit
  `Except String` errors. Two bit representations:
  - `List Bool` (spec-faithful): `encodeSymbols` / `decodeBits`.
  - ByteArray (fast, for large data): `encodeBytesBA` / `decodeBytesBA`.
- Convenience wrappers for `String` and `ByteArray`.
- **Unix `pack` `.z` archive format** (`packBytes`/`unpackBytes`,
  `packFile`/`unpackFile`): real magic `0x1f 0x1e`, canonical MSB-first codes,
  implicit EOF, and JPEG-style code-length limiting (≤25) so any input is valid.

## Build

```sh
lake exe cache get   # fetch the prebuilt Mathlib cache (first time)
lake build           # runtime library + proofs + tests (CI default)
lake build Huffman   # just the runtime library
```

Toolchain is pinned (`lean-toolchain` = `v4.29.0`, Mathlib `v4.29.0`).

## Quick start (library)

```lean
import Huffman
open Huffman

def table : FrequencyTable Char := [('a', 5), ('b', 2), ('c', 1)]

def run : Except String (List Char) := do
  let codec ← buildCodec table
  let bits  ← encodeSymbols codec ['a', 'b', 'a', 'c']
  decodeBits codec bits
```

## pack / unpack `.z`

```lean
import Huffman
open Huffman

#eval packFile "input.txt" "input.txt.z"     -- → IO (Except String Unit)
#eval unpackFile "input.txt.z" "out.txt"
```

Or from the shell via the helper scripts:

```sh
lake env lean --run scripts/PackFile.lean   input.txt input.txt.z
lake env lean --run scripts/UnpackFile.lean input.txt.z out.txt
```

See [`PACK_FORMAT.md`](PACK_FORMAT.md) for the byte-level format and sources.

## Using it as a dependency

In your `lakefile.toml`:

```toml
[[require]]
name = "huffman"
git  = "https://github.com/<owner>/LeanHuffmanCoding"
rev  = "main"
```

Depending on the `Huffman` library does **not** pull in the proof stack
(`HuffmanProofs`) or tests.

## Status / future work

- ✅ Optimality proof, runtime bridge, ByteArray fast path, `pack` `.z` format,
  code-length limiting, `#guard` test suite + CI gating (incl. `sorry` check).
- ⏳ **Verify interop with the system `pack`/`unpack` binary** and add golden `.z`
  round-trip tests (blocked on installing `pack`).
- ⏳ Trim remaining linter warnings.

## Acknowledgements

Thanks to Professor Siddhartha Gadgil, IISc for guidance throughout the project.
