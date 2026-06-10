import Huffman.HfmnProofs.HfmnTree_transformations

/-!
# Optimality of Huffman Trees

This file contains the abstract optimality lemmas together with the final theorem
proving the optimality of Huffman trees.

Huffman’s algorithm constructs a tree that minimizes the total cost
for a given set of symbol and its frequencies.

## Main Result
Theorem `optimum_huffman` shows that the Huffman tree built from any non-empty forest is optimal,
no other tree with the same alphabet and frequencies has lower cost.
-/

/--
Swapping two pairs of symbols `a b` and `c d` in a Huffman tree
does not increase the cost, if:

- `a` and `b` are minima in the tree,
- `c` and `d` are at the bottom (depth equals height),
- `c ≠ d`.

This proves that rearranging minima and bottom nodes doesn't increase the total cost.
-/
lemma cost_swapFourSyms_le {α} [DecidableEq α]
  (t : HuffmanTree α) (a b c d : α)
  (h_consistent : consistent t) (h_minima : minima t a b) (hc : c ∈ alphabet t)
  (hd : d ∈ alphabet t) (hdhc : depth t c = height t)
  (hdhd : depth t d = height t) (h_cd : c ≠ d) :
  cost (swapFourSyms t a b c d) ≤ cost t := by
  rcases h_minima with ⟨ha, hb, h_ab, h_freq⟩
  by_cases h : a ≠ d ∧ b ≠ c
  · rcases h with ⟨h_ad, h_bc⟩
    by_cases h_ac : a = c
    · simp [swapFourSyms, h_bc, h_ac, h_cd, swapLeaves_id t c h_consistent, swapSyms]
      by_cases h_bd : b = d
      · simp [h_bd, swapLeaves_id t d h_consistent]
      · have hcost := cost_swapLeaves t (freq t b) (freq t d) b d h_consistent h_bd
        simp [hb, hd] at hcost
        have h_freq2 : freq t b ≤ freq t d := (h_freq d hd (Ne.symm h_ad) (Ne.symm h_bd)).2
        have hd2 : depth t b ≤ depth t d := by grind [depth_le_height]
        nlinarith
    · by_cases h_bd : b = d
      · have : swapFourSyms t a b c d = swapLeaves t (freq t a) a (freq t c) c := by
          grind [swapFourSyms, swapLeaves_id, swapSyms, consistent_swapLeaves]
        rw [this]
        have hcost := cost_swapLeaves t (freq t a) (freq t c) a c h_consistent h_ac
        simp [ha, hc] at hcost
        have h_freq2 : freq t a ≤ freq t c := (h_freq c hc (Ne.symm h_ac) (Ne.symm h_bc)).1
        have hd2 : depth t a ≤ depth t c := by grind [depth_le_height]
        nlinarith
      · have := h_freq c hc (Ne.symm h_ac) (Ne.symm h_bc)
        calc
          cost (swapFourSyms t a b c d) ≤ cost (swapSyms t a c) := by
            let t' := swapLeaves t (freq t a) a (freq t c) c
            have h_freq' : freq t' b ≤ freq t' d := by grind [freq_swapLeaves, freq, alphabet]
            aesop (add norm [swapFourSyms])
          _ ≤ cost t := by aesop
  · grind [swapSyms, cost_swapSyms_le, depth_le_height, swapFourSyms, cost_swapLeaves]

/--
Splitting a leaf node `a` into two leaves `a` and `b` preserves optimality, if:

- `t` is optimum,
- `a ∈ alphabet t` and `b ∉ alphabet t`,
- `freq t a = wa + wb`,
- All other frequencies are higher or the same as `wa` and `wb`.

The new tree `splitLeaf t wa a wb b` is also optimal.
-/
@[simp]
lemma optimum_splitLeaf {α : Type} [DecidableEq α]
  (t : HuffmanTree α) (a b : α) (wa wb : ℕ)
  (h_consistent : consistent t) (h_optimum : optimum t)
  (ha_t : a ∈ alphabet t) (hb_t : b ∉ alphabet t) (h_freq : freq t a = wa + wb)
  (h1 : ∀ c ∈ alphabet t, freq t c ≥ wa ∧ freq t c ≥ wb) :
  optimum (splitLeaf t wa a wb b) := by
  intro u h_consistent_u h_alp_t_u h_freq_u
  let t' := splitLeaf t wa a wb b
  change cost t' ≤ cost u
  by_cases h_height_t_0 : height t' = 0
  · simp [*]
  · have ha_u : a ∈ alphabet u := by
      have ha_t' : a ∈ alphabet t' := by simp [t', ha_t]
      grind
    have hb_u : b ∈ alphabet u := by
      have hb_t' : b ∈ alphabet t' := by simp [t', ha_t]
      grind
    have h_ab : a ≠ b := by grind
    have h_height_u : height u > 0 := by cases u <;> grind [height, alphabet]
    obtain ⟨c, hc_u, hc_depth⟩ := exists_at_height u h_consistent_u
    let d := sibling u c
    have h_dc : d ≠ c := by grind [depth_height_imp_sibling_ne]
    have hd_u : d ∈ alphabet u := by
      simp [d, sibling_ne_imp_sibling_in_alphabet u c h_dc]
    have hd_depth : depth u d = height u := by grind [depth_sibling]
    let u' := swapFourSyms u a b c d
    have h_consistent_u' : consistent u' :=
      consistent_swapFourSyms u a b c d h_consistent_u
    have h_alp_u'_u : alphabet u' = alphabet u :=
      alphabet_swapFourSyms u a b c d ha_u hb_u hc_u hd_u
    have h_freq_u' : freq u' = freq u :=
      freq_swapFourSyms u a b c d h_consistent_u ha_u hb_u hc_u hd_u
    have h_sib_a : sibling u' a = b := by grind [sibling_swapFourSyms_when_4th_is_sibling]
    let v := mergeSibling u' a
    have h_consistent_v : consistent v := by grind [consistent_mergeSibling]
    have h_freq_a : freq t' a = freq u a := congr_fun h_freq_u a
    have h_freq_b : freq t' b = freq u b := congr_fun h_freq_u b
    have h_freq_v : freq v = freq t := by
      ext x
      have ha_u' : a ∈ alphabet u' := by simp [h_alp_u'_u, ha_u]
      rw [freq_mergesibling u' a h_consistent_u' ha_u' ?_]
      · aesop (add norm [h_freq_u', h_freq_u.symm])
      · grind
    calc
      cost t' = cost t + wa + wb :=
        cost_splitLeaf t wa wb a b h_consistent ha_t h_freq
      _ ≤ cost v + wa + wb := by
        grind [optimum, consistent_mergeSibling, alphabet_splitLeaf, alphabet_mergeSibling]
      _ = cost u' := by
        have hwafreq : wa = freq u' a := by
          have : wa = freq t' a := by grind [freq_splitLeaf]
          rw [this, h_freq_a, h_freq_u']
        have hwbfreq : wb = freq u' (sibling u' a) := by
          have : wb = freq t' b := by grind [freq_splitLeaf]
          rw [h_sib_a, this, h_freq_b, h_freq_u']
        grind [cost_mergeSibling]
      _ ≤ cost u := by
        have h_minima : minima u a b := by
          apply twice_freq_le_imp_minima t u a b wa wb
          · aesop
          · aesop
          · exact ha_u
          · exact h_ab
          · ext x
            split_ifs with hxa hxb
            · aesop (add norm [freq])
            · aesop (add norm [freq])
            · simp [h_freq_u.symm, freq_splitLeaf t wa wb a b x h_consistent hb_t, hxa, hxb]
        exact cost_swapFourSyms_le u a b c d h_consistent_u h_minima hc_u
            hd_u hc_depth hd_depth h_dc.symm

/--
Splitting a leaf commutes with Huffman tree construction.
Applying `splitLeaf` to a Huffman tree yields the same result
as first splitting the leaf in the forest and then running `huffman`,
if `a ∈ alphabetF ts` and `freqF ts a = wa + wb`.
-/
@[simp]
lemma splitLeaf_huffman_commute {α : Type} [DecidableEq α]
  (ts : Forest α) (a b : α) (wa wb : Nat) (hne : ts ≠ [])
  (h_consistent : consistentF ts) (h_a : a ∈ alphabetF ts)
  (h_freq : freqF ts a = wa + wb) :
  splitLeaf (huffman ts hne) wa a wb b =
  huffman (splitLeafF ts wa a wb b) (splitLeafF_nonempty hne) := by
  induction ts, hne using huffman.induct with
  | case1 t h1 h2 => simp [splitLeafF, huffman]
  | case2 t1 t2 ts h1 h2 ih =>
      have h_disj1 : (alphabet t1 ∪ alphabet t2) ∩ alphabetF ts = ∅ := by
        grind [consistentF, alphabetF]
      have h_disj2 : alphabet t1 ∩ alphabet t2 = ∅ := by grind [consistentF, alphabetF]
      have h_cases :
        (a ∈ alphabet t1 ∧ a ∉ alphabet t2 ∧ a ∉ alphabetF ts) ∨
        (a ∉ alphabet t1 ∧ a ∈ alphabet t2 ∧ a ∉ alphabetF ts) ∨
        (a ∉ alphabet t1 ∧ a ∉ alphabet t2 ∧ a ∈ alphabetF ts) := by
        grind [alphabetF, mem_inter_empty, consistentF]
      rcases h_cases with h1 | h2 | h3 <;>
      aesop (add norm
          [splitLeafF, insortTree, huffman, splitLeaf,
           alphabet, alphabetF, consistentF, consistent,
           cachedWeight, freq, freqF, uniteTrees])

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
                aesop (add norm[splitLeaf, uniteTrees, freq, consistent, consistentF,alphabet, alphabetF])
              have h_optimum_huffman_us' : optimum (huffman us' h_us') := by
                have hconus : consistentF us' := by
                  aesop (add norm[consistentF, consistent, alphabet, alphabetF])
                have h_height_us' : heightF us' = 0 := by aesop(add norm[heightF,height])
                have h_len_us' : us'.length < n := by aesop
                grind[sortedByWeight_insortTree, heightF, height,sortedByWeight_Cons_imp_sortedByWeight]
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
