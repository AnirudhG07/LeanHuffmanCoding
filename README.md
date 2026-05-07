# LeanHuffmanCoding
Lean Implementation for Huffmann Coding Algorithm, as a course Project for [IISc, Proof and Programs 2025](https://github.com/proofs-and-programs/proofs-and-programs-25).

This Library gives a runtime-focused API for integration for other compression pipelines.

> [!Note]
> This library is a work in progress, and more features will be added in the future.

## Implemented features

- Huffman tree construction from `(symbol, frequency)` tables.
- Proof of Correctness and Optimality of the Huffman Algorithm.
- A reusable `Codec` object with:
  - symbol-to-code lookup,
  - stream encoding (`List α -> List Bool`),
  - stream decoding (`List Bool -> List α`) with explicit errors.
- Convenience APIs for `String` and `ByteArray` pipelines.

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

## Future work
- Better API as Library for using Huffman in more practical settings.
- Compatibility with `pack` and `unpack` Linux utilities.

## Acknowledgements
Thanks to Professor Siddhartha Gadgil, IISc for guidance throughout the project.
This project was done with help of Codex AI.
