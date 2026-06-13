import Huffman.HfmnProofs.HfmnTree_transformations
import Huffman.HfmnProofs.HfmnTree_optimality
import Huffman.HfmnProofs.HfmnTree_uniqueness
import Huffman.HfmnProofs.HfmnTree_prefixfreeness
import Huffman.HfmnProofs.HfmnTree_optimality_lemma
import Huffman.HfmnProofs.Codec_correctness
import Huffman.HfmnProofs.Codec_roundtrip

/-!
# HuffmanProofs

Aggregator for the optimality / correctness proof stack. This is a separate
`lean_lib` target so CI builds (and thereby gates) the proofs, while downstream
consumers of the runtime `Huffman` library are not forced to build them.

`lake build HuffmanProofs` must stay green on every change.
-/
