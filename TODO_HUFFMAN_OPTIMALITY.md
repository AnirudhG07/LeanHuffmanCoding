# Huffman Optimality Integration Plan

## Canonical Layout
- [x] Keep the abstract optimality proof in the `HfmnTree_*` core modules.
- [x] Keep `HfmnTree_optimality` as the single runtime/public optimality file.
- [x] Keep the abstract optimality stack reduced to `HfmnTree_basic`,
  `HfmnTree_transformations`, and `HfmnTree_optimum`.
- [x] Delete the old copied runtime optimality proof branch.
- [x] Make `HuffmanTree.lean` use the proof-side constructor as the canonical implementation.

## What Is Proven Today
- [x] `HfmnTree_optimum.optimum_huffman`
  - The abstract Huffman algorithm on `HuffmanTree` produces an optimal tree.
- [x] `HfmnTree_optimality.leastEncodedData_eq_wpl`
  - The runtime implementation's encoded bit count matches weighted path length.
- [x] `HfmnTree_optimality.weightedPathLength_optimal`
  - The public `HfmnTree.tree` is optimal among admissible runtime trees.
- [x] `Huffman.leastEncodedData_optimal`
  - The public encoded-bit-count API is minimal among admissible runtime trees.
- [x] `HuffmanTree.lean`
  - The public constructor now builds trees by calling the proof-side `huffman`
    algorithm and converting its result back into `HfmnTree`.

## Remaining Cleanup
- [ ] Trim linter warnings in `HfmnTree_optimality.lean` and the older
  `HfmnTree_*` core files.
- [x] Reduce `HfmnProofs/` to 6 files total:
  `HfmnTree_basic`, `HfmnTree_transformations`, `HfmnTree_optimum`,
  `HfmnTree_optimality`, `HfmnTree_prefixfreeness`, and `HfmnTree_uniqueness`.

## Guardrails
- Keep the `HfmnTree_*` core modules as the single source of truth for abstract optimality.
- Keep `HfmnTree_optimality` as the stable public entry point for the runtime bridge.
- Avoid adding another copied proof branch under a new file name.
