import Huffman.HfmnProofs.HfmnInductiveTreeStructure

/-!
# Structural Tree Transformations

This file defines tree transformations with swapping leaves, symbols, or 4 symbols
within a Huffman tree together with lemmas showing their effect on the tree structure.
These transformations are used for tree optimality proof

## Definitions
- `swapLeaves t a b`       : Swap two leaf nodes of symbols `a` and `b`.
- `swapSyms t a b`         : Swap two symbols `a` and `b` in tree `t`.
- `swapFourSyms t a b c d` : Swap two pairs of symbol `a` and `b` with `c` and `d`.
-/

/--
Swap two leaf nodes `a` and `b` in tree `t` along with their weights `wa` and `wb`.
-/
def swapLeaves {α} [DecidableEq α] : HuffmanTree α → Nat → α → Nat → α → HuffmanTree α
  | HuffmanTree.leaf wc c, wa, a, wb, b =>
      if c = a then HuffmanTree.leaf wb b
      else if c = b then HuffmanTree.leaf wa a
      else HuffmanTree.leaf wc c
  | HuffmanTree.node w t1 t2, wa, a, wb, b =>
      HuffmanTree.node w (swapLeaves t1 wa a wb b) (swapLeaves t2 wa a wb b)

@[simp]
lemma swapLeaves_id_when_notin_alphabet {α} [DecidableEq α]
  (t : HuffmanTree α) (a : α) (wa wb : ℕ) :
  a ∉ alphabet t → swapLeaves t wa a wb a = t := by
  induction t <;> grind [alphabet, swapLeaves]

@[simp]
lemma swapLeaves_id {α : Type} [d : DecidableEq α]
  (t : HuffmanTree α) (a : α) (h_consistent : consistent t) :
  swapLeaves t (freq t a) a (freq t a) a = t := by
  induction a, h_consistent using huffmanTree_induct_consistent <;>
  aesop (add norm [freq, swapLeaves])

@[simp]
lemma alphabet_swapLeaves {α} [DecidableEq α]
  (t : HuffmanTree α) (wa : ℕ) (a : α) (wb : ℕ) (b : α) :
  alphabet (swapLeaves t wa a wb b) =
    (if a ∈ alphabet t then
        if b ∈ alphabet t then alphabet t else (alphabet t \ {a}) ∪ {b}
     else
        if b ∈ alphabet t then (alphabet t \ {b}) ∪ {a} else alphabet t) := by
  induction t <;> grind [alphabet, swapLeaves]

@[simp]
lemma consistent_swapLeaves {α} [DecidableEq α]
  (t : HuffmanTree α) (wa wb : ℕ) (a b : α) :
  consistent t → consistent (swapLeaves t wa a wb b) := by
  induction t with
  | leaf wc c =>
      aesop (add norm [swapLeaves])
  | node w t1 t2 ih1 ih2 =>
      simp[consistent, swapLeaves]
      grind[mem_inter_empty]

@[simp]
lemma depth_swapLeaves_neither {α} [DecidableEq α]
  (t : HuffmanTree α) (wa wb : ℕ) (a b c : α)
  (h_consistent : consistent t) (h_ca : c ≠ a) (h_cb : c ≠ b) :
  depth (swapLeaves t wa a wb b) c = depth t c := by
  induction a, h_consistent using huffmanTree_induct_consistent <;>
  aesop (add norm [depth, swapLeaves])

@[simp]
lemma height_swapLeaves {α} [DecidableEq α] (t : HuffmanTree α) (wa wb : ℕ) (a b : α) :
  height (swapLeaves t wa a wb b) = height t := by
  induction t <;> aesop (add norm [height, swapLeaves])

@[simp]
lemma freq_swapLeaves {α} [DecidableEq α]
  (t : HuffmanTree α) (wa wb : ℕ) (a b : α)
  (h_consistent : consistent t) (h_ab : a ≠ b) :
  freq (swapLeaves t wa a wb b) =
  fun c =>  if c = a then if b ∈ alphabet t then wa else 0
            else if c = b then if a ∈ alphabet t then wb else 0
            else freq t c := by
  ext c
  induction t with
  | leaf w x => aesop (add norm [freq, alphabet, swapLeaves])
  | node w t1 t2 ih1 ih2 =>
      grind[freq, swapLeaves, alphabet,mem_inter_empty,consistent]

/--
Swapping two leaves `a` and `b` in a consistent Huffman tree updates the tree's weight
according to the frequencies of the swapped leaves.
-/
@[simp]
lemma weight_swapLeaves {α} [DecidableEq α]
  (t : HuffmanTree α) (wa wb : ℕ) (a b : α)
  (h_consistent : consistent t) (h_ab : a ≠ b) :
  if a ∈ alphabet t then
    if b ∈ alphabet t then
      weight (swapLeaves t wa a wb b) + freq t a + freq t b =
        weight t + wa + wb
    else
      weight (swapLeaves t wa a wb b) + freq t a = weight t + wb
  else
    if b ∈ alphabet t then
      weight (swapLeaves t wa a wb b) + freq t b = weight t + wa
    else
      weight (swapLeaves t wa a wb b) = weight t := by
  induction a, h_consistent using huffmanTree_induct_consistent <;>
  grind[weight, alphabet, freq, swapLeaves, mem_inter_empty, notin_alphabet_imp_freq_0]

/--
Computes the cost of a tree after swapping two leaves `a` and `b` by
updating cost according to the swapped weights and original depths.
-/
@[simp]
lemma cost_swapLeaves {α} [DecidableEq α]
  (t : HuffmanTree α) (wa wb : ℕ) (a b : α)
  (h_consistent : consistent t) (h_ab : a ≠ b) :
  if a ∈ alphabet t then
    if b ∈ alphabet t then
      cost (swapLeaves t wa a wb b) + freq t a * depth t a
      + freq t b * depth t b =
        cost t + wa * depth t b + wb * depth t a
    else
      cost (swapLeaves t wa a wb b) + freq t a * depth t a =
        cost t + wb * depth t a
  else
    if b ∈ alphabet t then
      cost (swapLeaves t wa a wb b) + freq t b * depth t b =
        cost t + wa * depth t b
    else
      cost (swapLeaves t wa a wb b) = cost t := by
  induction t with
  | leaf w c => aesop (add norm [cost, alphabet, freq, depth, swapLeaves])
  | node w t1 t2 ih1 ih2 =>
      obtain ⟨h_disj, h_consistent_t1, h_consistent_t2⟩ := h_consistent
      simp [alphabet, cost, freq, depth, swapLeaves]
      have w1 := weight_swapLeaves t1 wa wb a b h_consistent_t1 h_ab
      have w2 := weight_swapLeaves t2 wa wb a b h_consistent_t2 h_ab
      by_cases h_a_t1 : a ∈ alphabet t1
      · have h_a_t2 : a ∉ alphabet t2 := by grind[mem_inter_empty]
        by_cases h_b_t1 : b ∈ alphabet t1
        · have h_b_t2 : b ∉ alphabet t2 := by grind[mem_inter_empty]
          simp [h_a_t1, h_a_t2, h_b_t1, h_b_t2]
          grind
        · by_cases h_b_t2 : b ∈ alphabet t2 <;> simp_all <;> grind
      · by_cases h_a_t2 : a ∈ alphabet t2
        · by_cases h_b_t1 : b ∈ alphabet t1
          · have h_b_t2 : b ∉ alphabet t2 := by grind[mem_inter_empty]
            simp [h_a_t1, h_a_t2, h_b_t1, h_b_t2]
            grind
          · by_cases h_b_t2 : b ∈ alphabet t2 <;> simp_all <;> grind
        · by_cases h_b_t1 : b ∈ alphabet t1
          · have h_b_t2 : b ∉ alphabet t2 := by grind[mem_inter_empty]
            simp [h_a_t1, h_a_t2, h_b_t1, h_b_t2]
            grind
          · by_cases h_b_t2 : b ∈ alphabet t2 <;> simp_all ; grind

set_option maxHeartbeats 300000
/--
Swapping the leaf `a` with the sibling of `b` preserves the sibling relationship:
after the swap, `a`’s sibling becomes `b`.
-/
@[simp]
lemma sibling_swapLeaves_sibling {α} [DecidableEq α]
  (t : HuffmanTree α) (a b : α) (wa ws : ℕ)
  (h_consistent : consistent t) (h_sib_b : sibling t b ≠ b) (h_a_b : a ≠ b) :
  sibling (swapLeaves t wa a ws (sibling t b)) a = b := by
  induction t with
  | leaf w x => simp [sibling] at h_sib_b
  | node w t1 t2 ih1 ih2 =>
      let ⟨h_disj, h_consistent_t1, h_consistent_t2⟩ := h_consistent
      simp [h_consistent_t1, h_consistent_t2] at ih1 ih2
      by_cases h_height_t1 : height t1 = 0
      · cases t1 with
        | leaf wc c =>
            by_cases h_height_t2 : height t2 = 0
            · cases t2 <;> aesop (add norm [sibling, swapLeaves])
            · have h_height_t2_le : height t2 > 0 := Nat.pos_of_ne_zero h_height_t2
              by_cases h_b_c : b = c
              · aesop(add norm[alphabet])
              · have h_sibling: sibling (HuffmanTree.node w (HuffmanTree.leaf wc c) t2) b
                  = sibling t2 b := by aesop
                rw [h_sibling]
                have h_c_alp_t2 : c ∉ alphabet t2 := by
                  intro h1
                  have h2 : c ∈ alphabet (HuffmanTree.leaf wc c) ∩ alphabet t2 :=
                    Finset.mem_inter.mpr ⟨Finset.mem_singleton_self c, h1⟩
                  simp [h_disj] at h2
                simp [swapLeaves]
                split_ifs with h_a_c h_sib_c <;> aesop (add norm [sibling, alphabet])
        | node w t1 t2 => simp [height] at h_height_t1
      · have h_height_t1_le : height t1 > 0 := Nat.pos_of_ne_zero h_height_t1
        by_cases h_b_t1 : b ∈ alphabet t1
        · simp [h_b_t1, h_height_t1_le, swapLeaves]
          grind[height_gt_0_in_alphabet_imp_sibling_left, sibling_ne_imp_sibling_in_alphabet]
        · by_cases h_b_t2 : b ∈ alphabet t2
          · have h_s_alphabet_1 : sibling t2 b ∉ alphabet t1 := by
              grind[in_alphabet_imp_sibling_in_alphabet, mem_inter_empty]
            simp [h_height_t1_le, swapLeaves]
            grind[height_gt_0_notin_alphabet_imp_sibling_left]
          · aesop (add norm [sibling, alphabet])
set_option linter.style.setOption false

/--
Swap symbols `a` and `b` in tree `t`. A more simple form of swapLeaves.
-/
def swapSyms {α} [DecidableEq α] (t : HuffmanTree α) (a b : α) : HuffmanTree α :=
  swapLeaves t (freq t a) a (freq t b) b

@[simp]
lemma swapSyms_id {α} [DecidableEq α]
  (t : HuffmanTree α) (a : α) :
  consistent t → swapSyms t a a = t := by aesop (add norm [swapSyms])

@[simp]
lemma alphabet_swapSyms {α} [DecidableEq α]
  (t : HuffmanTree α) (a b : α)
  (h_a : a ∈ alphabet t) (h_b : b ∈ alphabet t) :
  alphabet (swapSyms t a b) = alphabet t := by aesop (add norm [swapSyms])

@[simp]
lemma consistent_swapSyms {α} [DecidableEq α]
  (t : HuffmanTree α) (a b : α) :
  consistent t → consistent (swapSyms t a b) := by aesop (add norm [swapSyms])

@[simp]
lemma depth_swapSyms_neither {α} [DecidableEq α]
  (t : HuffmanTree α) (a b c : α)
  (h_consistent : consistent t) (h_ca : c ≠ a) (h_cb : c ≠ b) :
  depth (swapSyms t a b) c = depth t c := by aesop (add norm [swapSyms])

@[simp]
lemma freq_swapSyms {α} [DecidableEq α]
  (t : HuffmanTree α) (a b : α)
  (h_consistent : consistent t) (h_a : a ∈ alphabet t) (h_b : b ∈ alphabet t) :
  freq (swapSyms t a b) = freq t := by
    by_cases h_a_b : a = b <;> aesop (add norm [swapSyms])

/--
The cost of a tree after swapping two symbols is updated according to the new depths.
-/
@[simp]
lemma cost_swapSyms {α} [DecidableEq α]
  (t : HuffmanTree α) (a b : α)
  (h_consistent : consistent t) (h_a : a ∈ alphabet t) (h_b : b ∈ alphabet t) :
  cost (swapSyms t a b) + freq t a * depth t a + freq t b * depth t b =
  cost t + freq t a * depth t b + freq t b * depth t a := by
    by_cases h_a_b : a = b
    · simp_all
    · grind[swapSyms, cost_swapLeaves]

/--
Cost after swapping symbols `a` and `b` is lower or equals to original cost
if `freq t a ≤ freq t b` and `depth t a ≤ depth t b`
-/
@[simp]
lemma cost_swapSyms_le {α} [DecidableEq α]
  (t : HuffmanTree α) (a b : α)
  (h_consistent : consistent t) (h_a : a ∈ alphabet t) (h_b : b ∈ alphabet t)
  (h_freq : freq t a ≤ freq t b) (h_depth : depth t a ≤ depth t b) :
  cost (swapSyms t a b) ≤ cost t := by
    have h1 : freq t a * depth t b + freq t b * depth t a
              ≤ freq t a * depth t a + freq t b * depth t b := by nlinarith
    grind [cost_swapSyms]

/--
Sibling relationships is preserved after swapping symbols
-/
@[simp]
lemma sibling_swapSyms_sibling {α} [DecidableEq α]
  (t : HuffmanTree α) (a b : α) :
  consistent t → sibling t b ≠ b → a ≠ b →
  sibling (swapSyms t a (sibling t b)) a = b := by aesop (add norm [swapSyms])

@[simp]
lemma sibling_swapSyms_other_sibling {α} [DecidableEq α]
  (t : HuffmanTree α) (a b : α)
  (h_consistent : consistent t) (h_sib_b_a : sibling t b ≠ a)
  (h_sib_b_b : sibling t b ≠ b) (h_a_b : a ≠ b) :
  sibling (swapSyms t a b) (sibling t b) = a := by
    set c := sibling t b with hc
    have hsbc := sibling_reciprocal t b c h_consistent (by rw [hc])
    grind[sibling_reciprocal, sibling_swapSyms_sibling, consistent_swapSyms, sibling]

/--
Exchange 2 symbol with other 2 symbol
a and b will take the place of c and d
-/
def swapFourSyms {α} [DecidableEq α] (t : HuffmanTree α) (a b c d : α) : HuffmanTree α :=
  if a = d then swapSyms t b c
  else if b = c then swapSyms t a d
  else swapSyms (swapSyms t a c) b d

@[simp]
lemma alphabet_swapFourSyms {α} [DecidableEq α]
  (t : HuffmanTree α) (a b c d : α) :
  a ∈ alphabet t → b ∈ alphabet t → c ∈ alphabet t → d ∈ alphabet t →
  alphabet (swapFourSyms t a b c d) = alphabet t := by aesop (add norm[swapFourSyms])

@[simp]
lemma consistent_swapFourSyms {α} [DecidableEq α]
  (t : HuffmanTree α) (a b c d : α) :
  consistent t → consistent (swapFourSyms t a b c d) := by aesop (add norm[swapFourSyms])

@[simp]
lemma freq_swapFourSyms {α} [DecidableEq α]
  (t : HuffmanTree α) (a b c d : α)
  (h_consistent : consistent t) (h_a : a ∈ alphabet t) (h_b : b ∈ alphabet t)
  (h_c : c ∈ alphabet t) (h_d : d ∈ alphabet t) :
  freq (swapFourSyms t a b c d) = freq t := by
  aesop (add norm[swapFourSyms])

/--
Sibling relationships is preserved after swapping 4 symbols
-/
lemma sibling_swapFourSyms_when_4th_is_sibling {α} [DecidableEq α]
  (t : HuffmanTree α) (a b c d : α)
  (h_consistent : consistent t) (h_a: a ∈ alphabet t) (h_b : b ∈ alphabet t)
  (h_c : c ∈ alphabet t) (h_d : d ∈ alphabet t)
  (h_a_b : a ≠ b) (h_sib_c : sibling t c ≠ c) :
  sibling (swapFourSyms t a b c (sibling t c)) a = b := by
  by_cases h : a ≠ sibling t c ∧ b ≠ c
  · let d' := sibling t c
    let ts := swapFourSyms t a b c d'
    have abba : (sibling ts a = b) = (sibling ts b = a) := by
      grind[sibling_reciprocal, consistent_swapFourSyms]
    have s : sibling t c = sibling (swapSyms t a c) a := by
      grind[sibling_swapSyms_other_sibling, sibling_reciprocal,
            swapSyms, swapLeaves_id,consistent_swapFourSyms, consistent, consistent_swapSyms]
    have h : sibling ts b = a := by
      calc
        sibling ts b = sibling (swapSyms t a c) d' := by
          simp [ts, swapFourSyms, d', h]
          by_cases h_ac : a = c <;>
          aesop (add norm[swapSyms, freq, sibling, consistent, swapLeaves])
        _ = a := by aesop
    aesop (add norm [swapLeaves, swapSyms, sibling])
  · simp [swapFourSyms]
    split
    · by_cases h_bc : b = c <;> aesop
    · aesop (add norm [swapLeaves, swapSyms, sibling])
