/-
  HfmnTree_optimality.lean

  Core objective layer for Huffman optimality:
  * tree depth,
  * weighted path length,
  * bridge theorem `leastEncodedData_eq_wpl`,
  * shared uniqueness predicate `HfmnTree.codesUnique`.

  This file is intentionally independent of any exchange-style framework.
-/

import Huffman.HfmnProofs.HfmnTree_optimality_lemmas
import Huffman.HfmnProofs.HfmnTree_prefixfreeness
import Huffman.HfmnProofs.HfmnTree_uniqueness
import Mathlib

set_option linter.unusedSectionVars false

variable {α : Type} [DecidableEq α] [Inhabited α] [Ord α] [HfmnType α]

instance [Inhabited α] [DecidableEq α] : HfmnType α where
  default := default

-- ─────────────────────────────────────────────────────────────────────────────
-- §1  Depth of a character in a HfmnTree
-- ─────────────────────────────────────────────────────────────────────────────

/-- Depth of character `c` in tree `t`.  Returns 0 for a missing character
    (callers are responsible for only querying characters that exist). -/
@[simp, grind .]
def HfmnTree.depth : HfmnTree α → α → Nat
  | .Leaf _ _,  _ => 0
  | .Node l r,  c =>
    if l.charInTree c then 1 + l.depth c
    else                    1 + r.depth c

@[simp, grind .]
lemma HfmnTree.depth_leaf (val : α) (w : Nat) (c : α) :
    (HfmnTree.Leaf val w).depth c = 0 := rfl

@[simp, grind .]
lemma HfmnTree.depth_node_left (l r : HfmnTree α) (c : α)
    (h : l.charInTree c = true) :
    (HfmnTree.Node l r).depth c = 1 + l.depth c := by
  simp_all [depth]

@[simp, grind .]
lemma HfmnTree.depth_node_right (l r : HfmnTree α) (c : α)
    (h : l.charInTree c = false) :
    (HfmnTree.Node l r).depth c = 1 + r.depth c := by
  simp_all [depth]

-- ─────────────────────────────────────────────────────────────────────────────
-- §2  Weighted path length
-- ─────────────────────────────────────────────────────────────────────────────

/-- Total encoding cost: Σ_{(a,freq) ∈ input} freq * depth(a). -/
@[simp, grind .]
def weightedPathLength (t : HfmnTree α) (input : AlphaNumList α) : Nat :=
  input.foldl (fun acc (a, count) => acc + t.depth a * count) 0

@[simp]
lemma List.foldl_add_assoc {α : Type} (f : α → Nat) (xs : List α) (a b : Nat) :
    List.foldl (fun acc x => acc + f x) (a + b) xs =
    a + List.foldl (fun acc x => acc + f x) b xs := by
  induction xs generalizing a b with
  | nil => rfl
  | cons x xs' ih => grind

/-- Sum-based view of weighted path length; this is easier to rewrite with than `foldl`. -/
@[simp, grind .]
def weightedPathLengthSum (t : HfmnTree α) (input : AlphaNumList α) : Nat :=
  (input.map (fun x => t.depth x.1 * x.2)).sum

@[simp, grind .]
lemma weightedPathLengthSum_nil (t : HfmnTree α) :
    weightedPathLengthSum t [] = 0 := by
  simp [weightedPathLengthSum]

@[simp, grind .]
lemma weightedPathLengthSum_cons (t : HfmnTree α) (a : α) (freq : Nat)
    (rest : AlphaNumList α) :
    weightedPathLengthSum t ((a, freq) :: rest) =
      t.depth a * freq + weightedPathLengthSum t rest := by
  simp [weightedPathLengthSum]

@[simp, grind .]
lemma weightedPathLength_eq_sum (t : HfmnTree α) (input : AlphaNumList α) :
    weightedPathLength t input = weightedPathLengthSum t input := by
  induction input with
  | nil =>
    simp [weightedPathLength, weightedPathLengthSum]
  | cons hd tl ih =>
    obtain ⟨a, freq⟩ := hd
    have ih' :
        List.foldl (fun acc x => acc + t.depth x.1 * x.2) 0 tl =
        (tl.map (fun x => t.depth x.1 * x.2)).sum := by
      simpa [weightedPathLength, weightedPathLengthSum] using ih
    have hfold :
        List.foldl (fun acc x => acc + t.depth x.1 * x.2) (t.depth a * freq) tl =
        t.depth a * freq +
          List.foldl (fun acc x => acc + t.depth x.1 * x.2) 0 tl := by
      simpa using
        (List.foldl_add_assoc (f := fun x : α × Nat => t.depth x.1 * x.2)
          (xs := tl) (a := t.depth a * freq) (b := 0))
    simp [weightedPathLength, weightedPathLengthSum, hfold, ih']

lemma weightedPathLength_perm (t : HfmnTree α)
  {xs ys : AlphaNumList α} (hperm : xs.Perm ys) :
    weightedPathLength t xs = weightedPathLength t ys := by
  rw [weightedPathLength_eq_sum, weightedPathLength_eq_sum]
  unfold weightedPathLengthSum
  exact (hperm.map (fun x : α × Nat => t.depth x.1 * x.2)).sum_eq

@[simp]
lemma List.find?_exists_of_exists_mem {β : Type} (l : List β) (p : β → Bool)
    (h : ∃ x ∈ l, p x = true) :
    ∃ y, y ∈ l ∧ p y = true ∧ l.find? p = some y := by
  induction l with
  | nil =>
    rcases h with ⟨x, hx, _⟩
    simp at hx
  | cons hd tl ih =>
    rcases h with ⟨x, hx, hpx⟩
    simp at hx
    rcases hx with rfl | hx_tl
    · simp_all only [forall_exists_index, and_imp, mem_cons, find?_cons_of_pos, Option.some.injEq,
      exists_eq_or_imp, and_self, ↓existsAndEq, and_true, true_or]
    · simp_all only [forall_exists_index, and_imp, mem_cons, find?_cons_eq_some,
      Bool.not_eq_eq_eq_not, Bool.not_true, exists_eq_or_imp, and_true]
      grind

@[simp, grind .]
lemma List.foldl_congr_mem {β α : Type} (l : List α) (init : β)
    (f g : β → α → β)
    (h : ∀ acc x, x ∈ l → f acc x = g acc x) :
    List.foldl f init l = List.foldl g init l := by
  induction l generalizing init with
  | nil => rfl
  | cons x xs ih =>
    have hx : f init x = g init x := h init x (by simp)
    simp [hx]
    apply ih
    intro acc y hy
    exact h acc y (by simp [hy])

@[simp, grind .]
lemma weightedPathLength_congr_depth
    (t₁ t₂ : HfmnTree α) (input : AlphaNumList α)
    (h : ∀ a f, (a, f) ∈ input → t₁.depth a = t₂.depth a) :
    weightedPathLength t₁ input = weightedPathLength t₂ input := by
  unfold weightedPathLength
  apply List.foldl_congr_mem
  intro acc x hx
  rcases x with ⟨a, f⟩
  have hdepth : t₁.depth a = t₂.depth a := h a f hx
  simp [hdepth]

@[simp, grind .]
lemma encoded_mem_of_char_mem (t : HfmnTree α) (a : α) (ha : a ∈ t.chars) :
    (a, HfmnTree.encode a t) ∈ (t.chars.map (fun c => (c, HfmnTree.encode c t))) := by
  exact List.mem_map.mpr ⟨a, ha, rfl⟩

@[simp, grind .]
lemma encoded_exists_for_char (t : HfmnTree α) (a : α) (ha : a ∈ t.chars) :
    ∃ y ∈ (t.chars.map (fun c => (c, HfmnTree.encode c t))), (fun z => z.1 == a) y = true := by
  exact ⟨(a, HfmnTree.encode a t), encoded_mem_of_char_mem t a ha, by simp⟩

-- ─────────────────────────────────────────────────────────────────────────────
-- §3  encode length = depth  (connects existing API to new definitions)
-- ─────────────────────────────────────────────────────────────────────────────

/-- The length of the encoding of `c` in `t` equals the depth of `c` in `t`. -/
theorem HfmnTree.encode_length_eq_depth (t : HfmnTree α) (c : α)
    (h : t.charInTree c = true) :
    (HfmnTree.encode c t).length = t.depth c := by
  induction t with
  | Leaf val w =>
    simp [HfmnTree.charInTree, HfmnTree.chars] at h
    simp [HfmnTree.encode, HfmnTree.depth, h]
  | Node l r ihl ihr =>
    by_cases hl : l.charInTree c = true
    · -- character is in left subtree
      have := ihl hl
      simp_all [HfmnTree.encode, HfmnTree.depth, List.length_cons]
      grind
    · -- character is in right subtree
      have hl' : l.charInTree c = false := by simp_all
      have hr : r.charInTree c = true := by
        simp [HfmnTree.charInTree, HfmnTree.chars] at h ⊢
        grind
      have := ihr hr
      simp [HfmnTree.encode, HfmnTree.depth]
      grind

lemma leastEncodedData_step_eq_depth
    (huffinput : AlphaNumList α)
    (t : HfmnTree α)
    (encoded : BoolEncList α)
    (ht : t = HfmnTree.tree huffinput)
    (he : encoded = t.chars.map (fun c => (c, HfmnTree.encode c t))) :
    ∀ acc x, x ∈ huffinput →
      (match encoded.find? (fun z => z.1 == x.1) with
       | some (_, code) => acc + code.length * x.2
       | none => acc)
      = acc + t.depth x.1 * x.2 := by
  subst ht he
  intro acc x hx
  rcases x with ⟨a, count⟩
  have hchar : (HfmnTree.tree huffinput).charInTree a = true :=
    HfmnTree.tree_contains_input_chars huffinput a count hx
  have hmem_chars : a ∈ (HfmnTree.tree huffinput).chars :=
    (HfmnTree.charInTree_iff (HfmnTree.tree huffinput) a).1 hchar
  have hex :
      ∃ y ∈ ((HfmnTree.tree huffinput).chars.map
        (fun c => (c, HfmnTree.encode c (HfmnTree.tree huffinput)))),
        (fun z => z.1 == a) y = true :=
    encoded_exists_for_char (HfmnTree.tree huffinput) a hmem_chars
  rcases List.find?_exists_of_exists_mem
      ((HfmnTree.tree huffinput).chars.map
        (fun c => (c, HfmnTree.encode c (HfmnTree.tree huffinput))))
      (fun z => z.1 == a) hex with ⟨y, hy_mem, hy_p, hy_find⟩
  rcases y with ⟨ya, code⟩
  have hchar_ya : (HfmnTree.tree huffinput).charInTree ya = true := by grind
  have hlen_ya :
      (HfmnTree.encode ya (HfmnTree.tree huffinput)).length =
      (HfmnTree.tree huffinput).depth ya :=
    HfmnTree.encode_length_eq_depth (HfmnTree.tree huffinput) ya hchar_ya
  grind

@[simp, grind .]
lemma foldl_depth_eq_weightedPathLengthSum (t : HfmnTree α) (input : AlphaNumList α) :
    List.foldl (fun acc x => acc + t.depth x.1 * x.2) 0 input =
    weightedPathLengthSum t input := by
  simpa [weightedPathLength] using (weightedPathLength_eq_sum t input)


@[simp, grind .]
lemma List.foldl_pull_out (t : HfmnTree α) (a : α) (freq : Nat)
    (b : α) (f : Nat) (tl : AlphaNumList α) :
    List.foldl (fun acc x => acc + t.depth x.1 * x.2)
               (t.depth a * freq + t.depth b * f) tl =
    t.depth a * freq +
    List.foldl (fun acc x => acc + t.depth x.1 * x.2) (t.depth b * f) tl := by
  exact foldl_add_assoc (fun x ↦ t.depth x.1 * x.2) tl (t.depth a * freq) (t.depth b * f)

@[simp, grind .]
lemma weightedPathLength_cons (t : HfmnTree α) (a : α) (freq : Nat) (rest : AlphaNumList α) :
    weightedPathLength t ((a, freq) :: rest) =
    t.depth a * freq + weightedPathLength t rest := by
  induction rest generalizing a freq with
  | nil =>
    simp [weightedPathLength]
  | cons hd tl ih =>
    obtain ⟨b, f⟩ := hd
    simp_all only [weightedPathLength, List.foldl_cons, zero_add, List.foldl_pull_out]


-- ─────────────────────────────────────────────────────────────────────────────
-- §4  leastEncodedData = weightedPathLength of the Huffman tree
-- ─────────────────────────────────────────────────────────────────────────────

/-- `leastEncodedData` equals `weightedPathLength` of the Huffman tree. -/
theorem leastEncodedData_eq_wpl (huffinput : AlphaNumList α) :
    Huffman.leastEncodedData huffinput =
    weightedPathLength (HfmnTree.tree huffinput) huffinput := by
  rw [weightedPathLength_eq_sum]
  let t := HfmnTree.tree huffinput
  let encoded : BoolEncList α := t.chars.map (fun c => (c, HfmnTree.encode c t))
  have hstep :
      ∀ acc x, x ∈ huffinput →
        (match encoded.find? (fun z => z.1 == x.1) with
         | some (_, code) => acc + code.length * x.2
         | none => acc)
        = acc + t.depth x.1 * x.2 :=
    leastEncodedData_step_eq_depth huffinput t encoded rfl rfl

  have hfold :=
    List.foldl_congr_mem huffinput 0
      (fun acc x =>
        match encoded.find? (fun z => z.1 == x.1) with
        | some (_, code) => acc + code.length * x.2
        | none => acc)
      (fun acc x => acc + t.depth x.1 * x.2)
      hstep
  have hright :
      List.foldl (fun acc x => acc + t.depth x.1 * x.2) 0 huffinput =
      weightedPathLengthSum t huffinput :=
    foldl_depth_eq_weightedPathLengthSum t huffinput
  have hmain :
      List.foldl
          (fun acc x =>
            match encoded.find? (fun z => z.1 == x.1) with
            | some (_, code) => acc + code.length * x.2
            | none => acc)
          0 huffinput =
      weightedPathLengthSum t huffinput := hfold.trans hright
  simpa only [Huffman.leastEncodedData, HfmnTree.encodedList, weightedPathLengthSum, t, encoded]
-- ─────────────────────────────────────────────────────────────────────────────

/-- All vertex codes of a tree are pairwise distinct. -/
def HfmnTree.codesUnique (t : HfmnTree α) : Prop :=
  (t.vertices []).Pairwise (fun v₁ v₂ => v₁.code ≠ v₂.code)

/--
The Huffman tree constructed from a forest `ts` using the `huffman` algorithm
is optimal.
-/
theorem optimum_huffman {β : Type} [d : DecidableEq β] (ts : Forest β)
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

namespace HfmnTreeInductiveOptimality

/--
Compact entrypoint theorem for the direct inductive optimality route.
This is the same mathematical statement as `optimum_huffman`.
-/
theorem optimum_huffman_main {β : Type} [DecidableEq β]
  (ts : Forest β)
  (h_consistent_ts : consistentF ts)
  (h_height : heightF ts = 0)
  (h_sorted : sortedByWeight ts)
  (hne : ts ≠ []) :
  optimum (huffman ts hne) :=
  optimum_huffman ts h_consistent_ts h_height h_sorted hne

end HfmnTreeInductiveOptimality
