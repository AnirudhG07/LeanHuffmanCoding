# LeanHuffmanCoding

Lean 4 Huffman coding library with a runtime-focused API for integration into real compressors.

## What this library provides

- Huffman tree construction from `(symbol, frequency)` tables.
- A reusable `Codec` object with:
  - symbol-to-code lookup,
  - stream encoding (`List α -> List Bool`),
  - stream decoding (`List Bool -> List α`) with explicit errors.
- Convenience APIs for `String` and `ByteArray` pipelines.

Main modules:

- `Huffman.HuffmanTree` — core tree and construction utilities.
- `Huffman.Codec` — production-style codec build/encode/decode API.
- `Huffman` — top-level import for consumers.

## Quick start

```lean
import Huffman

open Huffman

def table : FrequencyTable Char := [('a', 5), ('b', 2), ('c', 1)]

def run : Except String (List Char) := do
  let codec <- buildCodec table
  let bits <- encodeSymbols codec ['a', 'b', 'a', 'c']
  decodeBits codec bits
```

## Design notes

- APIs return `Except String` for failure cases (invalid table, unknown symbol, malformed bitstream).
- Single-symbol alphabets are encoded with a non-empty runtime code to keep decoding progress-safe.
- `codeLengths` exposes `(symbol, bitLength)` values for downstream serialization/header formats.
