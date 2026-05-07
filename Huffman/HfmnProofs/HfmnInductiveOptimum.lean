import Huffman.HfmnProofs.HfmnInductiveOptimalityLemmas

/-!
# Optimality of Huffman Trees

This file contains the main theorem proving the optimality of Huffman trees.

Huffman’s algorithm constructs a tree that minimizes the total cost
for a given set of symbol and its frequencies.

## Main Result
Theorem `optimum_huffman` shows that the Huffman tree built from any non-empty forest is optimal,
no other tree with the same alphabet and frequencies has lower cost.
-/

/--
The Huffman tree constructed from a forest `ts` using the `huffman` algorithm
is optimal.
-/
theorem optimum_huffman {α : Type} [d : DecidableEq α] (ts : Forest α)
  (h_consistent_ts : consistentF ts)
  (h_height : heightF ts = 0)
  (h_sorted : sortedByWeight ts)
  (hne : ts ≠ []) :
  optimum (huffman ts hne) := by
  induction h : ts.length using Nat.strong_induction_on generalizing ts with
  | h n ih =>
    cases ts with
    | nil => exact False.elim (hne rfl)
    | cons ta ts' =>
      cases ts' with
      | nil =>
        grind [optimum,huffman,heightF,height_0_imp_cost_0]
        | cons tb ts'' =>
          cases ta with
          | leaf wa a =>
            cases tb with
            | leaf wb b =>
              simp [consistentF] at h_consistent_ts
              let ⟨h_disjoint , h_consistent_ta, h_disjoint_tb_ts,
                h_consistent_tb, h_consistent_ts'' ⟩ := h_consistent_ts
              let ta := HuffmanTree.leaf wa a
              let tb := HuffmanTree.leaf wb b
              let us := insortTree (uniteTrees ta tb) ts''
              let us' := insortTree (HuffmanTree.leaf (wa + wb) a) ts''
              have h_us' : us' ≠ [] := by simp [us']
              let ts := splitLeaf (huffman us' h_us') wa a wb b
              have e1 : huffman (HuffmanTree.leaf wa a
                :: HuffmanTree.leaf wb b :: ts'') hne  =
                huffman us (insortTree_ne_nil _ _) := by
                  aesop (add norm[huffman, us, uniteTrees])
              have h_a_alphabet_ts : a ∉ alphabetF ts'' := by
                aesop (add norm[alphabet, alphabetF])
              have e2 : huffman us (insortTree_ne_nil _ _) = ts := by
                aesop (add norm[splitLeaf, uniteTrees, freq, consistent, consistentF,
                                alphabet, alphabetF])
              have h_optimum_huffman_us' : optimum (huffman us' h_us') := by
                have hconus : consistentF us' := by
                  aesop (add norm[consistentF, consistent, alphabet, alphabetF])
                have h_height_us' : heightF us' = 0 := by aesop(add norm[heightF,height])
                have h_len_us' : us'.length < n := by aesop
                grind[sortedByWeight_insortTree, heightF, height,
                      sortedByWeight_Cons_imp_sortedByWeight]
              have h_optimum_ts : optimum ts := by
                have h_optimum:= optimum_splitLeaf (huffman us' h_us') a b wa wb
                have h_freq_us': ∀ c ∈ alphabetF us',
                  wa ≤ freqF us' c ∧ wb ≤ freqF us' c := by
                  intro c hc
                  by_cases h_ca : c = a
                  · aesop(add norm[freq, freqF,alphabet, alphabetF])
                  · have h_leaf : HuffmanTree.leaf (freqF us' c) c ∈ ts'' := by
                      aesop(add norm[heightF, freq, height, alphabet, alphabetF,
                                      heightF_0_imp_Leaf_freqF_in_set])
                    have h_w := sortedByWeight_Cons_imp_forall_weight_ge tb ts''
                              (sortedByWeight_Cons_imp_sortedByWeight ta
                                (tb :: ts'') h_sorted)
                    have h_wa_freq: wa ≤ freqF us' c := by
                      have h_weight_ta_tb : weight ta ≤ weight tb :=
                        sortedByWeight_Cons_imp_forall_weight_ge ta
                        (tb :: ts'') h_sorted tb (by simp)
                      grind[height_0_imp_cachedWeight_eq_weight, weight]
                    grind[weight]
                have h_b_alphabet_us': b ∉ alphabetF us' := by
                  aesop(add norm[alphabet, alphabetF])
                aesop(add norm[consistentF, consistent, alphabet, alphabetF,
                                consistent_huffman, huffman, freq, freqF])
              simpa [e1, e2] using h_optimum_ts
            | node w t1 t2 => simp [heightF, height] at h_height
          | node w t1 t2 => simp [heightF, height] at h_height
