import Huffman.HfmnTree_Construction
import Huffman.HfmnTree_Compression
import Huffman.Codec
import Huffman.FileCodec

/-!
# Huffman

Public library entrypoint for runtime Huffman coding APIs.

## Core modules
- `Huffman.HfmnTree_Construction`: tree construction and base definitions.
- `Huffman.HfmnTree_Compression`: tree compression and optimization.
- `Huffman.Codec`: production-focused codec API for build/encode/decode.
- `Huffman.FileCodec`: Unix `pack`/`unpack` `.z` archive format.
-/
