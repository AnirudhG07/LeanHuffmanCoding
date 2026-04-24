# Huffman Optimality TODO Tree

## Final Public Goal
- [ ] `G0`: prove `HfmnTreeOptimality.HuffmanOptimalityTheorem input`
  - Meaning: Huffman tree minimizes weighted path length over all admissible trees.

## Already Done
- [x] `G0_form`: define final target proposition
  - `HfmnTreeOptimality.HuffmanOptimalityTheorem`
- [x] `G0_led_form`: define equivalent least-encoded-data form
  - `HfmnTreeOptimality.HuffmanLeastEncodedDataTheorem`
- [x] `G0_equiv`: prove both forms are equivalent
  - `HfmnTreeOptimality.huffmanOptimalityTheorem_iff_leastEncodedData`
- [x] `R_meta`: reduction meta-theorem
  - `HfmnTreeOptimality.huffmanOptimality_of_reduction`
- [x] `D0`: define concrete scaffold class
  - `HfmnTreeOptimalityInduction.HfmnTree.DeepestSiblingClass`
- [x] `D1`: every tree belongs to scaffold class
  - `HfmnTreeOptimalityInduction.HfmnTree.deepestSiblingClass_all`

## Active Proof Route
- [ ] `R1`: prove concrete reduction hypothesis for scaffold class
  - Target: `ReductionHypothesis input DeepestSiblingClass`
  - First version can be identity reduction (`T' = T`) as a bridge theorem.
- [ ] `R2`: prove reduced-class optimality for a nontrivial reduced class
  - Current scaffold class is too broad, so this is the real hard part.

## Induction Core (real work)
- [ ] `I0`: define strict induction class `InductiveReducedClass`
  - Must encode the merge-step shape (least-frequency sibling condition).
- [ ] `I1`: prove reduction from `Admissible` to `InductiveReducedClass` with non-increasing cost.
- [ ] `I2`: prove one-step contraction theorem:
  - From a tree in `InductiveReducedClass`, contract sibling pair to a smaller admissible instance.
- [ ] `I3`: prove one-step expansion transfer theorem:
  - Lift optimality from merged instance back to split instance using
    `optimalityTransferOfMergeStep`.
- [ ] `I4`: prove base case (alphabet size <= 1).
- [ ] `I5`: prove strong induction on alphabet size for reduced-class optimality.

## Final Assembly
- [ ] `F1`: instantiate `huffmanOptimality_of_reduction` with
  concrete `InductiveReducedClass`, `I1`, `I5`.
- [ ] `F2`: derive least-encoded-data final theorem via equivalence lemma.

## Notes
- Keep current `HfmnTree` definitions (do not rewrite from scratch now).
- Rewriting the core tree model would reset too much proven infrastructure.
- Focus on tightening reduced-class definitions and induction transfer lemmas.
