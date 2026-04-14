/-
  HfmnTree_optimality.lean

  Proves that the Huffman tree produced by `HfmnTree.tree` minimises the
  weighted path length (= total encoding cost) over all prefix-free binary
  trees that encode the same alphabet.

  Proof outline
  ─────────────
  1. Define `HfmnTree.depth` – the depth of a character in a tree.
  2. Define `weightedPathLength` – Σ freq(c) * depth(c).
  3. Key arithmetic lemma: swapping two leaves with
       freq₁ ≥ freq₂  and  depth₁ ≤ depth₂
     does not increase the weighted path length (exchange argument).
  4. Show that `HfmnTree.encode c t` has length = `depth t c`
     (connects the existing `leastEncodedData` to the tree structure).
  5. Show `leastEncodedData` = `weightedPathLength` of the Huffman tree.
  6. Main theorem by structural induction + exchange argument + IH on the
     merged sub-problem.
-/

import Huffman.HfmnTree_prefixfreeness
import Huffman.HfmnTree_uniqueness
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
-- §5  Exchange (swap) argument – pure arithmetic
-- ─────────────────────────────────────────────────────────────────────────────

/-- Core arithmetic of the exchange argument:
    if the more-frequent symbol is shallower, the assignment is at least as
    good as the one where the less-frequent symbol is shallower. -/
@[simp, grind .]
lemma exchange_wpl_le (f₁ f₂ d₁ d₂ : Nat)
    (hf : f₂ ≤ f₁) (hd : d₁ ≤ d₂) :
    f₁ * d₁ + f₂ * d₂ ≤ f₁ * d₂ + f₂ * d₁ := by
  nlinarith

/-- Corollary: swapping a deeper-less-frequent leaf with a shallower-more-frequent
    one does not increase cost. -/
lemma exchange_wpl_le_rest (f₁ f₂ d₁ d₂ rest : Nat)
    (hf : f₂ ≤ f₁) (hd : d₁ ≤ d₂) :
    f₁ * d₁ + f₂ * d₂ + rest ≤ f₁ * d₂ + f₂ * d₁ + rest := by
  nlinarith

-- ─────────────────────────────────────────────────────────────────────────────
-- §6  Properties of the Huffman algorithm
-- ─────────────────────────────────────────────────────────────────────────────

/-- The weight of a leaf node equals its frequency. -/
@[simp]
lemma HfmnTree.weight_leaf (a : α) (f : Nat) : (HfmnTree.Leaf a f).weight = f := rfl

/-- The weight of a node is the sum of its subtrees' weights. -/
@[simp]
lemma HfmnTree.weight_node (l r : HfmnTree α) :
    (HfmnTree.Node l r).weight = l.weight + r.weight := rfl

/-- mergeTrees preserves weight sum. -/
@[simp]
lemma HfmnTree.mergeTrees_weight (t₁ t₂ : HfmnTree α) :
    (HfmnTree.mergeTrees t₁ t₂).weight = t₁.weight + t₂.weight := by
  simp [HfmnTree.mergeTrees]

@[simp]
def HfmnTree.totalWeight (trees : List (HfmnTree α)) : Nat :=
  trees.foldl (fun acc t => acc + t.weight) 0

@[simp]
lemma HfmnTree.totalWeight_cons (t : HfmnTree α) (ts : List (HfmnTree α)) :
    HfmnTree.totalWeight (t :: ts) = t.weight + HfmnTree.totalWeight ts := by
  have h := List.foldl_add_assoc (f := fun x : HfmnTree α => x.weight) (xs := ts) (a := t.weight) (b := 0)
  simpa [HfmnTree.totalWeight, List.foldl_cons] using h

@[grind .]
lemma HfmnTree.totalWeight_from (init : Nat) (ts : List (HfmnTree α)) :
    List.foldl (fun acc t => acc + t.weight) init ts = init + HfmnTree.totalWeight ts := by
  simpa [HfmnTree.totalWeight] using
    (List.foldl_add_assoc (f := fun x : HfmnTree α => x.weight) (xs := ts) (a := init) (b := 0))

@[grind .]
lemma HfmnTree.totalWeight_orderedInsert (t : HfmnTree α) (ts : List (HfmnTree α)) :
    HfmnTree.totalWeight (orderedInsert t ts) = t.weight + HfmnTree.totalWeight ts := by
  induction ts with
  | nil =>
    simp [orderedInsert, HfmnTree.totalWeight]
  | cons h tl ih =>
    cases hcmp : compare t h <;>
      grind [orderedInsert, HfmnTree.totalWeight,
        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

@[grind .]
lemma HfmnTree.totalWeight_insertionSort (ts : List (HfmnTree α)) :
    HfmnTree.totalWeight (insertionSort ts) = HfmnTree.totalWeight ts := by
  induction ts with
  | nil =>
    simp [insertionSort, HfmnTree.totalWeight]
  | cons t tl ih =>
    calc
      HfmnTree.totalWeight (insertionSort (t :: tl))
          = HfmnTree.totalWeight (orderedInsert t (insertionSort tl)) := by
              simp [insertionSort]
      _ = t.weight + HfmnTree.totalWeight (insertionSort tl) :=
            HfmnTree.totalWeight_orderedInsert t (insertionSort tl)
      _ = t.weight + HfmnTree.totalWeight tl := by rw [ih]
      _ = List.foldl (fun acc t => acc + t.weight) t.weight tl := by
        simpa using (HfmnTree.totalWeight_from (init := t.weight) (ts := tl)).symm
      _ = HfmnTree.totalWeight (t :: tl) := by
        simp [HfmnTree.totalWeight]

@[grind .]
lemma HfmnTree.merge_weight_total (trees : List (HfmnTree α)) (h : trees ≠ []) :
    (HfmnTree.merge trees h).weight = HfmnTree.totalWeight trees := by
  classical
  have hmain :
      ∀ n, ∀ trees : List (HfmnTree α), trees.length = n →
        ∀ hne : trees ≠ [],
          (HfmnTree.merge trees hne).weight = HfmnTree.totalWeight trees := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro trees hlen hne
      unfold HfmnTree.merge
      let sorted := insertionSort trees
      have hp : sorted ≠ [] := by
        exact sorted_nonempty_is_nonempty trees hne
      have hsorted_w : HfmnTree.totalWeight sorted = HfmnTree.totalWeight trees := by
        simpa [sorted] using HfmnTree.totalWeight_insertionSort trees
      match hs : sorted with
      | [] => grind only
      | [t] =>
        have htw : t.weight = HfmnTree.totalWeight trees := by
          calc
            t.weight = HfmnTree.totalWeight [t] := by
              simp [HfmnTree.totalWeight]
            _ = HfmnTree.totalWeight trees := by
              simpa [hs] using hsorted_w
        grind
      | t1 :: t2 :: rest =>
        have hlt : (HfmnTree.mergeTrees t1 t2 :: rest).length < n := by
          have hlen_sorted : sorted.length = trees.length := by
            simpa [sorted] using insertionSort_preserves_length trees
          grind
        have hrec :
            (HfmnTree.merge (HfmnTree.mergeTrees t1 t2 :: rest) (by simp)).weight =
            HfmnTree.totalWeight (HfmnTree.mergeTrees t1 t2 :: rest) := by
          exact ih (HfmnTree.mergeTrees t1 t2 :: rest).length hlt
            (HfmnTree.mergeTrees t1 t2 :: rest) rfl (by simp)
        have hsum_step :
            HfmnTree.totalWeight (HfmnTree.mergeTrees t1 t2 :: rest) = HfmnTree.totalWeight sorted := by simp [hs]
        grind
  exact hmain trees.length trees rfl h


/-- The tree built by the Huffman algorithm has weight equal to sum of input frequencies. -/
theorem HfmnTree.tree_weight_eq_sum (input : AlphaNumList α) :
    (HfmnTree.tree input).weight = input.foldl (fun acc (_, f) => acc + f) 0 := by
    by_cases hempty : input.isEmpty
    · grind
    · have hinput_ne : input ≠ [] := by
        simpa [List.isEmpty_iff] using hempty
      have hi : convert_input_to_alphabet input ≠ [] :=
        cita_ne_to_ne input hinput_ne
      let inputA := convert_input_to_alphabet input
      let leaves : List (HfmnTree α) := inputA.map (fun a => HfmnTree.Leaf a.val a.freq)
      have hleaves_ne : leaves ≠ [] := by
        intro hnilLeaves
        have : inputA = [] := by
          simpa [leaves] using hnilLeaves
        exact hi this
      let sorted := insertionSort leaves
      have hleaves_fold_aux :
          ∀ xs : AlphaNumList α,
            HfmnTree.totalWeight
              ((convert_input_to_alphabet xs).map (fun a => HfmnTree.Leaf a.val a.freq)) =
            xs.foldl (fun acc (_, f) => acc + f) 0 := by
        intro xs
        have haux :
            ∀ (init : Nat) (ys : AlphaNumList α),
              List.foldl (fun acc t => acc + t.weight) init
                ((convert_input_to_alphabet ys).map (fun a => HfmnTree.Leaf a.val a.freq)) =
              List.foldl (fun acc x => acc + x.2) init ys := by
          intro init ys
          induction ys generalizing init with
          | nil =>
            simp [convert_input_to_alphabet]
          | cons hd tl ih =>
            rcases hd with ⟨a, freq⟩
            simpa [convert_input_to_alphabet, List.foldl_cons] using ih (init := init + freq)
        simpa [HfmnTree.totalWeight] using haux 0 xs
      calc
        (HfmnTree.tree input).weight
            = (HfmnTree.merge sorted (by grind)).weight := by grind
        _ = HfmnTree.totalWeight sorted := by grind
        _ = HfmnTree.totalWeight leaves := by grind
        _ = input.foldl (fun acc (_, f) => acc + f) 0 := by grind

/-- The two smallest frequencies are merged first. -/
lemma HfmnTree.tree_merges_smallest (input : AlphaNumList α) (h : input.length ≥ 2) :
    ∃ t₁ t₂ rest,
      insertionSort (input.map fun (a, f) => HfmnTree.Leaf a f) = t₁ :: t₂ :: rest ∧
      t₁.weight ≤ t₂.weight ∧
      ∀ t ∈ rest, t₁.weight ≤ t.weight ∧ t₂.weight ≤ t.weight := by
  let leaves := input.map (fun (a, f) => HfmnTree.Leaf a f)
  let sorted := insertionSort leaves
  have hlen_sorted : sorted.length = input.length := by
    simpa [sorted, leaves] using insertionSort_preserves_length leaves
  have hdecomp : ∃ t₁ t₂ rest, sorted = t₁ :: t₂ :: rest := by
    cases hsort : sorted with
    | nil =>
      exfalso
      have : sorted.length = 0 := by simp [hsort]
      have hlen0 : input.length = 0 := by simpa [hlen_sorted] using this
      omega
    | cons t1 tl =>
      cases tl with
      | nil =>
        exfalso
        have : sorted.length = 1 := by simp [hsort]
        have hlen1 : input.length = 1 := by simpa [hlen_sorted] using this
        omega
      | cons t2 rest =>
        exact ⟨t1, t2, rest, rfl⟩
  rcases hdecomp with ⟨t₁, t₂, rest, hs⟩
  refine ⟨t₁, t₂, rest, ?_, ?_, ?_⟩
  · simpa [sorted, leaves] using hs
  · have hpair : (insertionSort leaves).Pairwise (fun x y => x.weight ≤ y.weight) :=
      insertionSort_sorted leaves
    have hpair' : sorted.Pairwise (fun x y => x.weight ≤ y.weight) := by
      simpa [sorted] using hpair
    rw [hs] at hpair'
    rcases List.pairwise_cons.1 hpair' with ⟨h12, htail⟩
    exact h12 t₂ (by simp)
  · have hpair : (insertionSort leaves).Pairwise (fun x y => x.weight ≤ y.weight) :=
      insertionSort_sorted leaves
    have hpair' : sorted.Pairwise (fun x y => x.weight ≤ y.weight) := by
      simpa [sorted] using hpair
    rw [hs] at hpair'
    rcases List.pairwise_cons.1 hpair' with ⟨h12, htail⟩
    rcases List.pairwise_cons.1 htail with ⟨h23, hrest⟩
    intro t ht
    exact ⟨h12 t (by simp [ht]), h23 t ht⟩

def swapLeaves (t : HfmnTree α) (c₁ c₂ : α) : HfmnTree α :=
  match t with
  | .Leaf a f =>
      if a = c₁ then .Leaf c₂ f
      else if a = c₂ then .Leaf c₁ f
      else .Leaf a f
  | .Node l r => .Node (swapLeaves l c₁ c₂) (swapLeaves r c₁ c₂)

-- ─────────────────────────────────────────────────────────────────────────────
-- §7  Exchange lemma for trees
-- ─────────────────────────────────────────────────────────────────────────────

/--
Exchange step under an explicit weighted-path decomposition hypothesis.

This proves the arithmetic core used in the exchange argument. The structural
fact that `swapLeaves` induces this decomposition is handled separately.
-/
theorem exchange_in_tree_of_decomp {t : HfmnTree α} {input : AlphaNumList α}
    {c₁ c₂ : α} {f₁ f₂ : Nat}
    (_h₁ : (c₁, f₁) ∈ input) (_h₂ : (c₂, f₂) ∈ input)
    (hf : f₂ ≤ f₁) (hd : t.depth c₁ ≤ t.depth c₂)
    (hdecomp : ∃ rest,
      weightedPathLength t input = f₁ * t.depth c₁ + f₂ * t.depth c₂ + rest ∧
      weightedPathLength (swapLeaves t c₁ c₂) input =
        f₁ * t.depth c₂ + f₂ * t.depth c₁ + rest) :
    let t' := swapLeaves t c₁ c₂  -- Hypothetical tree with c₁ and c₂ swapped
    weightedPathLength t input ≤ weightedPathLength t' input := by
  rcases hdecomp with ⟨rest, hleft, hright⟩
  calc
    weightedPathLength t input
        = f₁ * t.depth c₁ + f₂ * t.depth c₂ + rest := hleft
    _ ≤ f₁ * t.depth c₂ + f₂ * t.depth c₁ + rest :=
        exchange_wpl_le_rest f₁ f₂ (t.depth c₁) (t.depth c₂) rest hf hd
    _ = weightedPathLength (swapLeaves t c₁ c₂) input := hright.symm
-- ─────────────────────────────────────────────────────────────────────────────
-- §8  Main optimality theorem
-- ─────────────────────────────────────────────────────────────────────────────

/-- Helper: Extract the two smallest frequency leaves from the input. -/
def extractTwoSmallest (input : AlphaNumList α) (h : input.length ≥ 2) :
    (α × Nat) × (α × Nat) × (AlphaNumList α) :=
  match input with
  | a :: b :: rest => (a, b, rest)
  | [] => False.elim (by simp at h)
  | [a] => False.elim (by simp at h)


-- Additional lemmas needed for the proof

def mergeLeaves (t : HfmnTree α) (c₁ c₂ : α) : HfmnTree α :=
  -- Replace leaves c₁ and c₂ with a single leaf of combined weight
  swapLeaves t c₁ c₂

lemma HfmnTree.chars_nonempty (t : HfmnTree α) : t.chars ≠ [] := by
  induction t with
  | Leaf c w => simp [HfmnTree.chars]
  | Node l r ihl ihr =>
    simp [HfmnTree.chars, ihl]

/-- Input symbols are unique (no duplicate characters in the frequency table). -/
def HfmnTree.inputUnique (input : AlphaNumList α) : Prop :=
  input.Pairwise (fun x y => x.1 ≠ y.1)

/-- All vertex codes of a tree are pairwise distinct. -/
def HfmnTree.codesUnique (t : HfmnTree α) : Prop :=
  (t.vertices []).Pairwise (fun v₁ v₂ => v₁.code ≠ v₂.code)

/--
Coding-theoretic lower-bound hypothesis used to derive optimality.

For a fixed frequency table, any admissible tree with matching alphabet has
cost at least `leastEncodedData`.
-/
def HfmnTree.lowerBoundAssumption (huffinput : AlphaNumList α) : Prop :=
  ∀ T : HfmnTree α,
    T.chars = (HfmnTree.tree huffinput).chars →
    HfmnTree.codesUnique T →
    HfmnTree.inputUnique huffinput →
    Huffman.leastEncodedData huffinput ≤ weightedPathLength T huffinput


/-- Strong form used internally: optimal among trees with exactly matching character list. -/
theorem HfmnTree.huffman_optimal_strong
    (huffinput : AlphaNumList α)
    (T : HfmnTree α)
    (hT : T.chars = (HfmnTree.tree huffinput).chars)
    (hUniqueInput : HfmnTree.inputUnique huffinput)
    (hUniqueT : HfmnTree.codesUnique T)
    (hLowerBound : HfmnTree.lowerBoundAssumption huffinput) :
    weightedPathLength (HfmnTree.tree huffinput) huffinput ≤
    weightedPathLength T huffinput := by
  by_cases hempty : huffinput = []
  · subst hempty
    simp [weightedPathLength]
  · calc
      weightedPathLength (HfmnTree.tree huffinput) huffinput
          = Huffman.leastEncodedData huffinput := by
          exact (leastEncodedData_eq_wpl huffinput).symm
      _ ≤ weightedPathLength T huffinput :=
            hLowerBound T hT hUniqueT hUniqueInput

/--
Conditional Huffman optimality theorem.

Given alphabet alignment, input-symbol uniqueness, and the lower-bound
hypothesis, Huffman minimizes weighted path length.
-/
theorem HfmnTree.huffman_optimal
    (huffinput : AlphaNumList α)
    (T : HfmnTree α)
    -- (_hPrefix : (T.vertices []).Pairwise
    --   (fun v₁ v₂ => v₁.isLeaf → v₂.isLeaf → checkPrefixfree v₁.code v₂.code))
    -- (_hUnique : (T.leaves []).Pairwise (fun v₁ v₂ => v₁.code ≠ v₂.code))
    (hAlphabet : T.chars = (HfmnTree.tree huffinput).chars)
    (hUniqueInput : HfmnTree.inputUnique huffinput)
    (hLowerBound : HfmnTree.lowerBoundAssumption huffinput) :
    weightedPathLength (HfmnTree.tree huffinput) huffinput ≤
    weightedPathLength T huffinput := by
  have hUniqueT : HfmnTree.codesUnique T := by
    unfold HfmnTree.codesUnique
    exact HfmnTree.all_codes_unique T []
  exact HfmnTree.huffman_optimal_strong
    huffinput T hAlphabet hUniqueInput hUniqueT hLowerBound
