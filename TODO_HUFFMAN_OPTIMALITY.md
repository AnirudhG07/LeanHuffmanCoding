# Huffman Optimality Integration — Done

The optimality integration this file used to track is **complete**. The proofs
live under `Huffman/HfmnProofs/` and are aggregated by the `HuffmanProofs`
`lean_lib` target (built and gated in CI).

## What is proven (current file names)
- `HfmnProofs/HfmnTree_optimality.lean` — `optimum_huffman`: the abstract Huffman
  algorithm produces an optimal tree.
- `HfmnProofs/HfmnTree_optimality_lemma.lean` — the runtime bridge:
  - `leastEncodedData_eq_wpl` — encoded bit count = weighted path length.
  - `HfmnTree.weightedPathLength_optimal` — `HfmnTree.tree` is optimal among
    admissible runtime trees.
  - `Huffman.leastEncodedData_optimal` — the public bit-count API is minimal.
- `HfmnProofs/HfmnTree_transformations.lean`, `HfmnTree_uniqueness.lean`,
  `HfmnTree_prefixfreeness.lean` — supporting structure / distinctness /
  prefix-freeness.

The public constructor `HfmnTree.tree` runs the proof-side `huffman` algorithm and
`ofProofTree`s the result, so the runtime tree *is* the proven-optimal tree.

## Guardrails (still apply)
- Single source of truth for abstract optimality is the `HfmnTree_*` core +
  `HfmnProofs/`. Don't fork a second copy of the proof under a new file name.
- The proofs depend on the spec-layer runtime defs in `HfmnTree_Compression.lean`
  (`HfmnTree.encode`, `encodedList`, `Huffman.leastEncodedData`, `HfmnTree.depth`).
  Keep them frozen; add parallel runtime defs instead of changing them.

The broader "ship as an industry-grade library" roadmap (performance, `pack`
format, tests, CI, docs) is tracked outside this file; see `README.md` *Status*
and `PACK_FORMAT.md`.
