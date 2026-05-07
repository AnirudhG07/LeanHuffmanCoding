/-
  HfmnTree_optimality.lean

  Runtime-facing objective layer for Huffman optimality:
  * tree depth,
  * weighted path length,
  * bridge theorem `leastEncodedData_eq_wpl`,
  * transfer of the integrated inductive optimality development.

  The abstract optimality proof lives in the `HfmnTree_*` proof-core files. This file
  carries the bridge from that proof stack to the public runtime `HfmnTree` API.
-/

import Huffman.HfmnProofs.HfmnTree_prefixfreeness
import Huffman.HfmnProofs.HfmnTree_uniqueness
import Huffman.HfmnProofs.HfmnTree_optimum
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
-- §5  Bridge from the public API to the proof-side optimality theorem
-- ─────────────────────────────────────────────────────────────────────────────

@[simp]
lemma HfmnTree.chars_ne_nil (t : HfmnTree α) :
    t.chars ≠ [] := by
  induction t <;> simp [HfmnTree.chars, *]

@[simp]
lemma AlphaNumList.lookupFreq_eq_zero_of_not_mem_symbols
    (input : AlphaNumList α) {a : α} (h : a ∉ AlphaNumList.symbols input) :
    AlphaNumList.lookupFreq input a = 0 := by
  induction input with
  | nil =>
      simp [AlphaNumList.lookupFreq]
  | cons x xs ih =>
      have hx_ne : x.1 ≠ a := by
        intro hxa
        apply h
        simp [AlphaNumList.symbols, hxa]
      have hxs : a ∉ AlphaNumList.symbols xs := by
        intro hmem
        apply h
        exact List.mem_cons_of_mem _ hmem
      simpa [AlphaNumList.lookupFreq, hx_ne] using ih hxs

lemma AlphaNumList.lookupFreq_eq_of_mem_wellFormed
    (input : AlphaNumList α) (h_wf : AlphaNumList.WellFormed input)
    {a : α} {f : Nat} (hmem : (a, f) ∈ input) :
    AlphaNumList.lookupFreq input a = f := by
  induction input with
  | nil =>
      cases hmem
  | cons x xs ih =>
      have hsplit : x.1 ∉ AlphaNumList.symbols xs ∧ AlphaNumList.WellFormed xs := by
        simpa [AlphaNumList.WellFormed, AlphaNumList.symbols] using h_wf
      rcases hsplit with ⟨hx_not_mem, hxs_wf⟩
      cases hmem with
      | head =>
          simp [AlphaNumList.lookupFreq]
      | tail _ =>
          rename_i hmem_tail
          have hx_ne_a : x.1 ≠ a := by
            intro hxa
            apply hx_not_mem
            subst hxa
            exact (AlphaNumList.mem_symbols_iff).2 ⟨f, hmem_tail⟩
          simpa [AlphaNumList.lookupFreq, hx_ne_a] using ih hxs_wf hmem_tail

lemma HfmnTree.freqF_proofForest_eq_lookupFreq
    (huffinput : AlphaNumList α) (h_wf : AlphaNumList.WellFormed huffinput) (a : α) :
    freqF (HfmnTree.proofForest huffinput) a = AlphaNumList.lookupFreq huffinput a := by
  induction huffinput with
  | nil =>
      simp [HfmnTree.proofForest, AlphaNumList.lookupFreq, freqF]
  | cons x xs ih =>
      have hsplit : x.1 ∉ AlphaNumList.symbols xs ∧ AlphaNumList.WellFormed xs := by
        simpa [AlphaNumList.WellFormed, AlphaNumList.symbols] using h_wf
      rcases hsplit with ⟨hx_not_mem, hxs_wf⟩
      by_cases hxa : a = x.1
      · subst hxa
        have hlookup0 : AlphaNumList.lookupFreq xs x.1 = 0 :=
          AlphaNumList.lookupFreq_eq_zero_of_not_mem_symbols xs hx_not_mem
        calc
          freqF (HfmnTree.proofForest (x :: xs)) x.1
              = x.2 + freqF (HfmnTree.proofForest xs) x.1 := by
                  simp [HfmnTree.proofForest, HfmnTree.proofLeaf, freqF_insortTree, freq]
          _ = x.2 + AlphaNumList.lookupFreq xs x.1 := by rw [ih hxs_wf]
          _ = x.2 := by rw [hlookup0]; simp
          _ = AlphaNumList.lookupFreq (x :: xs) x.1 := by
                simp [AlphaNumList.lookupFreq]
      · have hx_ne_a : x.1 ≠ a := by
          intro hax
          exact hxa hax.symm
        calc
          freqF (HfmnTree.proofForest (x :: xs)) a
              = 0 + freqF (HfmnTree.proofForest xs) a := by
                  simp [HfmnTree.proofForest, HfmnTree.proofLeaf, freqF_insortTree, freq, hxa]
          _ = AlphaNumList.lookupFreq xs a := by rw [ih hxs_wf]; simp
          _ = AlphaNumList.lookupFreq (x :: xs) a := by
                simp [AlphaNumList.lookupFreq, hx_ne_a]

lemma HfmnTree.consistentF_proofForest (huffinput : AlphaNumList α)
    (h_wf : AlphaNumList.WellFormed huffinput) :
    consistentF (HfmnTree.proofForest huffinput) := by
  induction huffinput with
  | nil =>
      simp [HfmnTree.proofForest, consistentF]
  | cons x xs ih =>
      have hsplit : x.1 ∉ AlphaNumList.symbols xs ∧ AlphaNumList.WellFormed xs := by
        simpa [AlphaNumList.WellFormed, AlphaNumList.symbols] using h_wf
      rcases hsplit with ⟨hx_not_mem, hxs_wf⟩
      have hdisj : alphabet (HfmnTree.proofLeaf x) ∩ alphabetF (HfmnTree.proofForest xs) = ∅ := by
        ext a
        by_cases hax : a = x.1
        · subst hax
          rw [HfmnTree.alphabetF_proofForest]
          have hx_not_mem' : ∀ n, (x.1, n) ∉ xs :=
            (AlphaNumList.not_mem_symbols_iff).1 hx_not_mem
          simp [HfmnTree.proofLeaf, alphabet, hx_not_mem']
        · simp [HfmnTree.proofLeaf, alphabet, hax]
      have hcons_cons : consistentF (HfmnTree.proofLeaf x :: HfmnTree.proofForest xs) := by
        exact ⟨hdisj, by simp [HfmnTree.proofLeaf, consistent], ih hxs_wf⟩
      simpa [HfmnTree.proofForest] using hcons_cons

@[simp]
lemma HfmnTree.chars_toFinset_ofProofTree (t : HuffmanTree α) :
    (HfmnTree.ofProofTree t).chars.toFinset = alphabet t := by
  ext a
  simp [HfmnTree.mem_chars_ofProofTree]

lemma HfmnTree.nodup_chars_of_ofProofTree (t : HuffmanTree α)
    (h_cons : consistent t) :
    (HfmnTree.ofProofTree t).chars.Nodup := by
  induction t with
  | leaf w a =>
      simp [HfmnTree.ofProofTree, HfmnTree.chars]
  | node w t1 t2 ih1 ih2 =>
      rcases h_cons with ⟨hdisj, hc1, hc2⟩
      have hnd1 : (HfmnTree.ofProofTree t1).chars.Nodup := ih1 hc1
      have hnd2 : (HfmnTree.ofProofTree t2).chars.Nodup := ih2 hc2
      have hdisj_list :
          List.Disjoint (HfmnTree.ofProofTree t1).chars (HfmnTree.ofProofTree t2).chars := by
        refine List.disjoint_left.2 ?_
        intro a ha1 ha2
        have h1 : a ∈ alphabet t1 := (HfmnTree.mem_chars_ofProofTree t1 a).1 ha1
        have h2 : a ∈ alphabet t2 := (HfmnTree.mem_chars_ofProofTree t2 a).1 ha2
        have : a ∈ alphabet t1 ∩ alphabet t2 := by simp [h1, h2]
        simp [hdisj] at this
      simpa [HfmnTree.ofProofTree, HfmnTree.chars] using hnd1.append hnd2 hdisj_list

lemma HfmnTree.chars_nodup_of_admissible (huffinput : AlphaNumList α)
    (h_wf : AlphaNumList.WellFormed huffinput) {t : HfmnTree α}
    (h_adm : AdmissibleToInput huffinput t) :
    t.chars.Nodup := by
  exact h_adm.nodup_iff.2 h_wf

lemma HfmnTree.tree_admissible_to_input (huffinput : AlphaNumList α)
    (h_wf : AlphaNumList.WellFormed huffinput) (h_ne : huffinput ≠ []) :
    AdmissibleToInput huffinput (HfmnTree.tree huffinput) := by
  have hcons : consistent (HfmnTree.proofTree huffinput h_ne) := by
    exact consistent_huffman
      (HfmnTree.proofForest huffinput)
      (HfmnTree.proofForest_ne_nil h_ne)
      (HfmnTree.consistentF_proofForest huffinput h_wf)
  have hnodup_tree : (HfmnTree.tree huffinput).chars.Nodup := by
    simpa [HfmnTree.tree, h_ne] using
      (HfmnTree.nodup_chars_of_ofProofTree (HfmnTree.proofTree huffinput h_ne) hcons)
  have htoFinset : (HfmnTree.tree huffinput).chars.toFinset = huffinput.symbols.toFinset := by
    simp [HfmnTree.tree, h_ne, HfmnTree.proofTree,
      HfmnTree.alphabetF_proofForest, alphabet_huffman]
  exact List.perm_of_nodup_nodup_toFinset_eq hnodup_tree h_wf htoFinset

lemma HfmnTree.consistent_toProofTree (huffinput : AlphaNumList α) (t : HfmnTree α)
    (h_nodup : t.chars.Nodup) :
    consistent (HfmnTree.toProofTree huffinput t) := by
  induction t with
  | Leaf a w =>
      simp [HfmnTree.toProofTree, consistent]
  | Node l r ihl ihr =>
      rcases List.nodup_append'.1 h_nodup with ⟨hl_nodup, hr_nodup, hdisj⟩
      have ihl' : consistent (HfmnTree.toProofTree huffinput l) := ihl hl_nodup
      have ihr' : consistent (HfmnTree.toProofTree huffinput r) := ihr hr_nodup
      have hdisj' : ∀ a, a ∈ l.chars → a ∈ r.chars → False := by
        simpa [List.disjoint_left] using hdisj
      have hdisj_alpha :
          alphabet (HfmnTree.toProofTree huffinput l) ∩
            alphabet (HfmnTree.toProofTree huffinput r) = ∅ := by
        ext a
        constructor
        · intro ha
          simp [HfmnTree.alphabet_toProofTree] at ha
          exact False.elim (hdisj' a ha.1 ha.2)
        · intro ha
          simp at ha
          exact ha
      exact ⟨hdisj_alpha, ihl', ihr'⟩

lemma HfmnTree.depth_toProofTree_eq_depth_of_mem
    (huffinput : AlphaNumList α) (t : HfmnTree α) (a : α)
    (h_nodup : t.chars.Nodup) (ha : a ∈ t.chars) :
    _root_.depth (HfmnTree.toProofTree huffinput t) a = t.depth a := by
  induction t generalizing a with
  | Leaf b w =>
      simp [HfmnTree.toProofTree, HfmnTree.depth, _root_.depth, HfmnTree.chars] at ha ⊢
  | Node l r ihl ihr =>
      rcases List.nodup_append'.1 h_nodup with ⟨hl_nodup, hr_nodup, hdisj⟩
      have hdisj' : ∀ x, x ∈ l.chars → x ∈ r.chars → False := by
        simpa [List.disjoint_left] using hdisj
      simp [HfmnTree.chars] at ha
      rcases ha with ha_l | ha_r
      · have hchar_l : l.charInTree a = true := (HfmnTree.charInTree_iff l a).2 ha_l
        have ihl' := ihl a hl_nodup ha_l
        simp [HfmnTree.depth, _root_.depth, HfmnTree.toProofTree,
          HfmnTree.alphabet_toProofTree, hchar_l, ha_l, ihl', Nat.add_comm]
      · have ha_l_not : a ∉ l.chars := by
          intro ha_l
          exact hdisj' a ha_l ha_r
        have hchar_l_false : l.charInTree a = false := by
          cases hres : l.charInTree a with
          | false =>
              simp at hres
              exact hres
          | true =>
              exact False.elim (ha_l_not ((HfmnTree.charInTree_iff l a).1 (by simpa using hres)))
        have ihr' := ihr a hr_nodup ha_r
        simp [HfmnTree.depth, _root_.depth, HfmnTree.toProofTree,
          HfmnTree.alphabet_toProofTree, hchar_l_false, ha_l_not, ha_r,
          ihr', Nat.add_comm]

lemma HfmnTree.freq_toProofTree_eq_lookupFreq_of_mem
    (huffinput : AlphaNumList α) (t : HfmnTree α) (a : α)
    (h_nodup : t.chars.Nodup) (ha : a ∈ t.chars) :
    freq (HfmnTree.toProofTree huffinput t) a = AlphaNumList.lookupFreq huffinput a := by
  induction t generalizing a with
  | Leaf b w =>
      simp [HfmnTree.toProofTree, HfmnTree.chars, freq] at ha ⊢
      subst ha
      simp [freq]
  | Node l r ihl ihr =>
      rcases List.nodup_append'.1 h_nodup with ⟨hl_nodup, hr_nodup, hdisj⟩
      have hdisj' : ∀ x, x ∈ l.chars → x ∈ r.chars → False := by
        simpa [List.disjoint_left] using hdisj
      simp [HfmnTree.chars] at ha
      rcases ha with ha_l | ha_r
      · have ha_r_not : a ∉ r.chars := by
          intro ha_r
          exact hdisj' a ha_l ha_r
        have hfreq_r_zero : freq (HfmnTree.toProofTree huffinput r) a = 0 := by
          apply notin_alphabet_imp_freq_0
          simpa [HfmnTree.alphabet_toProofTree] using ha_r_not
        calc
          freq (HfmnTree.toProofTree huffinput (HfmnTree.Node l r)) a
              = freq (HfmnTree.toProofTree huffinput l) a
                  + freq (HfmnTree.toProofTree huffinput r) a := by
                    simp [HfmnTree.toProofTree, freq]
          _ = AlphaNumList.lookupFreq huffinput a + 0 := by
                rw [ihl a hl_nodup ha_l, hfreq_r_zero]
          _ = AlphaNumList.lookupFreq huffinput a := by simp
      · have ha_l_not : a ∉ l.chars := by
          intro ha_l
          exact hdisj' a ha_l ha_r
        have hfreq_l_zero : freq (HfmnTree.toProofTree huffinput l) a = 0 := by
          apply notin_alphabet_imp_freq_0
          simpa [HfmnTree.alphabet_toProofTree] using ha_l_not
        calc
          freq (HfmnTree.toProofTree huffinput (HfmnTree.Node l r)) a
              = freq (HfmnTree.toProofTree huffinput l) a
                  + freq (HfmnTree.toProofTree huffinput r) a := by
                    simp [HfmnTree.toProofTree, freq]
          _ = 0 + AlphaNumList.lookupFreq huffinput a := by
                rw [hfreq_l_zero, ihr a hr_nodup ha_r]
          _ = AlphaNumList.lookupFreq huffinput a := by simp

lemma weightedPathLength_eq_sum_lookupFreq (t : HfmnTree α) (input : AlphaNumList α)
    (h_wf : AlphaNumList.WellFormed input) (h_adm : AdmissibleToInput input t) :
    weightedPathLength t input =
      ∑ a ∈ t.chars.toFinset, AlphaNumList.lookupFreq input a * t.depth a := by
  rw [weightedPathLength_eq_sum]
  have hmap :
      input.map (fun x => t.depth x.1 * x.2) =
        input.map (fun x => t.depth x.1 * AlphaNumList.lookupFreq input x.1) := by
    apply List.map_congr_left
    intro x hx
    rcases x with ⟨a, f⟩
    rw [AlphaNumList.lookupFreq_eq_of_mem_wellFormed input h_wf hx]
  have hperm_sum :
      (input.symbols.map (fun a => AlphaNumList.lookupFreq input a * t.depth a)).sum =
        (t.chars.map (fun a => AlphaNumList.lookupFreq input a * t.depth a)).sum := by
    exact (h_adm.symm.map (fun a => AlphaNumList.lookupFreq input a * t.depth a)).sum_eq
  have hnodup_t : t.chars.Nodup := HfmnTree.chars_nodup_of_admissible input h_wf h_adm
  have hsymbols :
      (input.map (fun x => t.depth x.1 * AlphaNumList.lookupFreq input x.1)).sum =
        (input.symbols.map (fun a => AlphaNumList.lookupFreq input a * t.depth a)).sum := by
    have hmap_symbols :
        input.map (fun x => t.depth x.1 * AlphaNumList.lookupFreq input x.1) =
          input.symbols.map (fun a => AlphaNumList.lookupFreq input a * t.depth a) := by
      unfold AlphaNumList.symbols
      simp only [List.map_map]
      apply List.map_congr_left
      intro x hx
      simp [Nat.mul_comm]
    rw [hmap_symbols]
  calc
    weightedPathLengthSum t input
        = (input.map (fun x => t.depth x.1 * AlphaNumList.lookupFreq input x.1)).sum := by
            unfold weightedPathLengthSum
            rw [hmap]
    _ = (input.symbols.map (fun a => AlphaNumList.lookupFreq input a * t.depth a)).sum := hsymbols
    _ = (t.chars.map (fun a => AlphaNumList.lookupFreq input a * t.depth a)).sum := hperm_sum
    _ = ∑ a ∈ t.chars.toFinset, AlphaNumList.lookupFreq input a * t.depth a := by
          symm
          simpa using
            (List.sum_toFinset (f := fun a => AlphaNumList.lookupFreq input a * t.depth a) hnodup_t)

lemma HfmnTree.cost_toProofTree_eq_weightedPathLength
    (huffinput : AlphaNumList α) (h_wf : AlphaNumList.WellFormed huffinput)
    (t : HfmnTree α) (h_adm : AdmissibleToInput huffinput t) :
    cost (HfmnTree.toProofTree huffinput t) = weightedPathLength t huffinput := by
  have hnodup_t : t.chars.Nodup := HfmnTree.chars_nodup_of_admissible huffinput h_wf h_adm
  have hcons_t : consistent (HfmnTree.toProofTree huffinput t) :=
    HfmnTree.consistent_toProofTree huffinput t hnodup_t
  calc
    cost (HfmnTree.toProofTree huffinput t)
        = ∑ a ∈ alphabet (HfmnTree.toProofTree huffinput t),
            freq (HfmnTree.toProofTree huffinput t) a *
              _root_.depth (HfmnTree.toProofTree huffinput t) a := by
              exact cost_eq_Sum_freq_mult_depth (t := HfmnTree.toProofTree huffinput t) hcons_t
    _ = ∑ a ∈ t.chars.toFinset, AlphaNumList.lookupFreq huffinput a * t.depth a := by
          rw [HfmnTree.alphabet_toProofTree]
          refine Finset.sum_congr rfl ?_
          intro a ha
          have hfreq :
              freq (HfmnTree.toProofTree huffinput t) a =
                AlphaNumList.lookupFreq huffinput a :=
            HfmnTree.freq_toProofTree_eq_lookupFreq_of_mem huffinput t a hnodup_t (by simpa using ha)
          have hdepth :
              _root_.depth (HfmnTree.toProofTree huffinput t) a = t.depth a :=
            HfmnTree.depth_toProofTree_eq_depth_of_mem huffinput t a hnodup_t (by simpa using ha)
          simp [hfreq, hdepth]
    _ = weightedPathLength t huffinput := by
          symm
          exact weightedPathLength_eq_sum_lookupFreq t huffinput h_wf h_adm

lemma HfmnTree.depth_ofProofTree_eq_depth_of_mem
    (t : HuffmanTree α) (a : α)
    (h_cons : consistent t) (ha : a ∈ alphabet t) :
    (HfmnTree.ofProofTree t).depth a = _root_.depth t a := by
  induction t generalizing a with
  | leaf w b =>
      simp [HfmnTree.ofProofTree, _root_.depth, alphabet] at ha ⊢
  | node w t1 t2 ih1 ih2 =>
      rcases h_cons with ⟨hdisj, hc1, hc2⟩
      have hcases := alphabet_cases a t1 t2 hdisj
      rcases hcases with hleft | hrest
      ·
          rcases hleft with ⟨ha1, _⟩
          have hchar : (HfmnTree.ofProofTree t1).charInTree a = true :=
            (HfmnTree.charInTree_ofProofTree_iff t1 a).2 ha1
          have ih1' := ih1 a hc1 ha1
          simp [HfmnTree.ofProofTree, HfmnTree.depth, _root_.depth,
            hchar, ha1, ih1', Nat.add_comm]
      ·
          rcases hrest with hright | hnone
          · rcases hright with ⟨ha1_not, ha2⟩
            have hchar_false : (HfmnTree.ofProofTree t1).charInTree a = false := by
              cases hres : (HfmnTree.ofProofTree t1).charInTree a with
              | false =>
                  simp at hres
                  exact hres
              | true =>
                  exact False.elim (ha1_not ((HfmnTree.charInTree_ofProofTree_iff t1 a).1 (by simpa using hres)))
            have ih2' := ih2 a hc2 ha2
            simp [HfmnTree.ofProofTree, HfmnTree.depth, _root_.depth,
              HfmnTree.charInTree_ofProofTree_iff, hchar_false, ha1_not, ha2,
              ih2', Nat.add_comm]
          · rcases hnone with ⟨ha1_not, ha2_not⟩
            simp [alphabet, ha1_not, ha2_not] at ha

lemma HfmnTree.cost_ofProofTree_eq_weightedPathLength
    (huffinput : AlphaNumList α) (h_wf : AlphaNumList.WellFormed huffinput)
    (t : HuffmanTree α) (h_cons : consistent t)
    (h_alpha : alphabet t = huffinput.symbols.toFinset)
    (h_freq : ∀ a, a ∈ alphabet t → freq t a = AlphaNumList.lookupFreq huffinput a) :
    cost t = weightedPathLength (HfmnTree.ofProofTree t) huffinput := by
  have h_adm : AdmissibleToInput huffinput (HfmnTree.ofProofTree t) := by
    have hnodup_tree : (HfmnTree.ofProofTree t).chars.Nodup :=
      HfmnTree.nodup_chars_of_ofProofTree t h_cons
    exact List.perm_of_nodup_nodup_toFinset_eq hnodup_tree h_wf
      (by simp [h_alpha] using HfmnTree.chars_toFinset_ofProofTree t)
  calc
    cost t = ∑ a ∈ alphabet t, freq t a * _root_.depth t a := by
      exact cost_eq_Sum_freq_mult_depth t h_cons
    _ = ∑ a ∈ (HfmnTree.ofProofTree t).chars.toFinset,
            AlphaNumList.lookupFreq huffinput a * (HfmnTree.ofProofTree t).depth a := by
          rw [HfmnTree.chars_toFinset_ofProofTree]
          refine Finset.sum_congr rfl ?_
          intro a ha
          have hfreqa : freq t a = AlphaNumList.lookupFreq huffinput a := h_freq a ha
          have hdeptha : (HfmnTree.ofProofTree t).depth a = _root_.depth t a :=
            HfmnTree.depth_ofProofTree_eq_depth_of_mem t a h_cons ha
          simp [hfreqa, hdeptha, Nat.mul_comm]
    _ = weightedPathLength (HfmnTree.ofProofTree t) huffinput := by
          symm
          exact weightedPathLength_eq_sum_lookupFreq (HfmnTree.ofProofTree t) huffinput h_wf h_adm

lemma HfmnTree.cost_proofTree_eq_weightedPathLength
    (huffinput : AlphaNumList α) (h_wf : AlphaNumList.WellFormed huffinput) (h_ne : huffinput ≠ []) :
    cost (HfmnTree.proofTree huffinput h_ne) =
      weightedPathLength (HfmnTree.tree huffinput) huffinput := by
  have hcons : consistent (HfmnTree.proofTree huffinput h_ne) := by
    exact consistent_huffman
      (HfmnTree.proofForest huffinput)
      (HfmnTree.proofForest_ne_nil h_ne)
      (HfmnTree.consistentF_proofForest huffinput h_wf)
  have h_alpha : alphabet (HfmnTree.proofTree huffinput h_ne) = huffinput.symbols.toFinset := by
    simp [HfmnTree.proofTree, HfmnTree.alphabetF_proofForest, alphabet_huffman]
  have h_freq :
      ∀ a, a ∈ alphabet (HfmnTree.proofTree huffinput h_ne) →
        freq (HfmnTree.proofTree huffinput h_ne) a = AlphaNumList.lookupFreq huffinput a := by
    intro a ha
    simp [HfmnTree.proofTree, freq_huffman,
      HfmnTree.freqF_proofForest_eq_lookupFreq huffinput h_wf]
  have hmain :=
    HfmnTree.cost_ofProofTree_eq_weightedPathLength huffinput h_wf
      (HfmnTree.proofTree huffinput h_ne) hcons h_alpha h_freq
  simpa [HfmnTree.tree, h_ne] using hmain

theorem HfmnTree.weightedPathLength_optimal
    (huffinput : AlphaNumList α)
    (h_wf : AlphaNumList.WellFormed huffinput)
    (h_ne : huffinput ≠ [])
    {t : HfmnTree α} (h_adm : AdmissibleToInput huffinput t) :
    weightedPathLength (HfmnTree.tree huffinput) huffinput ≤ weightedPathLength t huffinput := by
  let hp := HfmnTree.proofTree huffinput h_ne
  let u := HfmnTree.toProofTree huffinput t
  have hopt : optimum hp := by
    simpa [hp, HfmnTree.proofTree] using
      (optimum_huffman
        (HfmnTree.proofForest huffinput)
        (HfmnTree.consistentF_proofForest huffinput h_wf)
        (HfmnTree.heightF_proofForest huffinput)
        (HfmnTree.sortedByWeight_proofForest huffinput)
        (HfmnTree.proofForest_ne_nil h_ne))
  have hnodup_t : t.chars.Nodup := HfmnTree.chars_nodup_of_admissible huffinput h_wf h_adm
  have hcons_u : consistent u := HfmnTree.consistent_toProofTree huffinput t hnodup_t
  have halpha : alphabet hp = alphabet u := by
    calc
      alphabet hp = huffinput.symbols.toFinset := by
        simp [hp, HfmnTree.proofTree, HfmnTree.alphabetF_proofForest, alphabet_huffman]
      _ = t.chars.toFinset := by
        symm
        exact List.toFinset_eq_of_perm _ _ h_adm
      _ = alphabet u := by
        symm
        exact HfmnTree.alphabet_toProofTree huffinput t
  have hfreq_eq : freq hp = freq u := by
    funext a
    by_cases ha : a ∈ t.chars
    · have hfreq_u :
          freq u a = AlphaNumList.lookupFreq huffinput a :=
        HfmnTree.freq_toProofTree_eq_lookupFreq_of_mem huffinput t a hnodup_t ha
      have hfreq_hp :
          freq hp a = AlphaNumList.lookupFreq huffinput a := by
        simp [hp, HfmnTree.proofTree, freq_huffman,
          HfmnTree.freqF_proofForest_eq_lookupFreq huffinput h_wf]
      exact hfreq_hp.trans hfreq_u.symm
    · have hnot_input : a ∉ huffinput.symbols := by
        intro hmem
        exact ha ((h_adm.symm.mem_iff).1 hmem)
      have hlookup0 : AlphaNumList.lookupFreq huffinput a = 0 :=
        AlphaNumList.lookupFreq_eq_zero_of_not_mem_symbols huffinput hnot_input
      have hfreq_u0 : freq u a = 0 := by
        apply notin_alphabet_imp_freq_0
        simpa [u, HfmnTree.alphabet_toProofTree] using ha
      have hfreq_hp :
          freq hp a = AlphaNumList.lookupFreq huffinput a := by
        simp [hp, HfmnTree.proofTree, freq_huffman,
          HfmnTree.freqF_proofForest_eq_lookupFreq huffinput h_wf]
      rw [hfreq_hp, hlookup0, hfreq_u0]
  have hcost_le : cost hp ≤ cost u := hopt u hcons_u halpha hfreq_eq
  have hcost_hp :
      cost hp = weightedPathLength (HfmnTree.tree huffinput) huffinput :=
    HfmnTree.cost_proofTree_eq_weightedPathLength huffinput h_wf h_ne
  have hcost_u :
      cost u = weightedPathLength t huffinput :=
    HfmnTree.cost_toProofTree_eq_weightedPathLength huffinput h_wf t h_adm
  calc
    weightedPathLength (HfmnTree.tree huffinput) huffinput = cost hp := hcost_hp.symm
    _ ≤ cost u := hcost_le
    _ = weightedPathLength t huffinput := hcost_u

theorem Huffman.leastEncodedData_optimal
    (huffinput : AlphaNumList α)
    (h_wf : AlphaNumList.WellFormed huffinput)
    (h_ne : huffinput ≠ [])
    {t : HfmnTree α} (h_adm : AdmissibleToInput huffinput t) :
    Huffman.leastEncodedData huffinput ≤ weightedPathLength t huffinput := by
  rw [leastEncodedData_eq_wpl]
  exact HfmnTree.weightedPathLength_optimal huffinput h_wf h_ne h_adm
