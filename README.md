# LeanHuffmannCoding

Lean Implementation for Huffmann Coding Algorithm, as a course Project for [IISc, Proof and Programs 2025](https://github.com/proofs-and-programs/proofs-and-programs-25).

## Algorithm

The algorithm is based on the Huffman coding algorithm, which is a greedy algorithm used for lossless data compression. The algorithm works by assigning variable-length codes to input characters, with shorter codes assigned to more frequent characters. The steps of the algorithm are as follows:

1. Count the frequency of each character in the input string.
2. Create a priority queue (or min-heap) of nodes, where each node represents a character and its frequency.
3. While there is more than one node in the queue:
   - Remove the two nodes with the lowest frequency from the queue.
   - Create a new internal node with these two nodes as children and a frequency equal to the sum of their frequencies.
   - Add the new node back to the queue.
4. The remaining node in the queue is the root of the Huffman tree.
5. Traverse the tree to assign binary codes to each character, where left edges represent 0 and right edges represent 1.
6. Encode the input string using the assigned codes.
7. (Optionally) Decode the encoded string using the Huffman tree.

## Implementation

The implementation is done in Lean4, and this repository contains the following -

1. [Implementation](Huffman/HuffmanTree.lean) of the Huffman coding algorithm and binary tree, which we call `HfmnTree`.
2. Proof of Correctness of the algorithm, which includes:
   - [Proof](Huffman/HfmnTree_uniqueness.lean) of uniqueness of the codes present on all vertices of the tree.
   - [Proof](Huffman/HfmnTree_prefixfreeness.lean) of prefix-freeness of the codes present on all leaves of the tree(which contain the characters).

## Future Work

- Proving the Optimality of the Algorithm.

## Acknowledgements

Thanks to Professor Siddhartha Gadgil, IISc for guidance throughout the project.
