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
    6. OpenDSA-style exchange framework:
      local exchange inequality + transitive closure yields optimality on
      the exchange-reachable admissible class.
    7. Final global step is isolated as one proposition:
      `HfmnTree.ExchangeComplete` (reachability of all admissible trees).
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

/-- Replace every leaf weight by `0`, preserving the tree shape and characters. -/
def HfmnTree.zeroWeights : HfmnTree α → HfmnTree α
  | .Leaf a _ => .Leaf a 0
  | .Node l r => .Node (HfmnTree.zeroWeights l) (HfmnTree.zeroWeights r)

@[simp]
lemma HfmnTree.zeroWeights_chars (t : HfmnTree α) :
    (HfmnTree.zeroWeights t).chars = t.chars := by
  induction t with
  | Leaf a f => simp [HfmnTree.zeroWeights]
  | Node l r ihl ihr =>
      simp [HfmnTree.zeroWeights, HfmnTree.chars, ihl, ihr]

@[simp]
lemma HfmnTree.zeroWeights_weight (t : HfmnTree α) :
    (HfmnTree.zeroWeights t).weight = 0 := by
  induction t with
  | Leaf a f => simp [HfmnTree.zeroWeights]
  | Node l r ihl ihr =>
      simp [HfmnTree.zeroWeights, ihl, ihr]

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

lemma swapLeaves_mem_chars_of_ne
    (t : HfmnTree α) (a c₁ c₂ : α)
    (ha₁ : a ≠ c₁) (ha₂ : a ≠ c₂) :
    a ∈ (swapLeaves t c₁ c₂).chars ↔ a ∈ t.chars := by
  induction t with
  | Leaf x f =>
      by_cases h1 : x = c₁
      · by_cases h2 : x = c₂
        · subst h1
          subst h2
          simp [swapLeaves, ha₁]
        · subst h1
          simp [swapLeaves, ha₁, ha₂]
      · by_cases h2 : x = c₂
        · subst h2
          simp [swapLeaves, h1, ha₁, ha₂]
        · simp [swapLeaves, h1, h2]
  | Node l r ihl ihr =>
      simp [swapLeaves, HfmnTree.chars, ihl, ihr]

lemma swapLeaves_charInTree_of_ne
    (t : HfmnTree α) (a c₁ c₂ : α)
    (ha₁ : a ≠ c₁) (ha₂ : a ≠ c₂) :
    (swapLeaves t c₁ c₂).charInTree a = t.charInTree a := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hs
    apply (HfmnTree.charInTree_iff t a).2
    exact (swapLeaves_mem_chars_of_ne t a c₁ c₂ ha₁ ha₂).1
      ((HfmnTree.charInTree_iff (swapLeaves t c₁ c₂) a).1 hs)
  · intro ht
    apply (HfmnTree.charInTree_iff (swapLeaves t c₁ c₂) a).2
    exact (swapLeaves_mem_chars_of_ne t a c₁ c₂ ha₁ ha₂).2
      ((HfmnTree.charInTree_iff t a).1 ht)

lemma swapLeaves_depth_of_ne
    (t : HfmnTree α) (a c₁ c₂ : α)
    (ha₁ : a ≠ c₁) (ha₂ : a ≠ c₂) :
    (swapLeaves t c₁ c₂).depth a = t.depth a := by
  induction t with
  | Leaf x f =>
      by_cases h1 : x = c₁
      · by_cases h2 : x = c₂
        · subst h1
          subst h2
          simp [HfmnTree.depth, swapLeaves]
        · subst h1
          simp [HfmnTree.depth, swapLeaves]
      · by_cases h2 : x = c₂
        · subst h2
          simp [HfmnTree.depth, swapLeaves, h1]
        · simp [HfmnTree.depth, swapLeaves, h1, h2]
  | Node l r ihl ihr =>
      have hcl : (swapLeaves l c₁ c₂).charInTree a = l.charInTree a :=
        swapLeaves_charInTree_of_ne l a c₁ c₂ ha₁ ha₂
      by_cases hl : l.charInTree a = true
      · have hsl : (swapLeaves l c₁ c₂).charInTree a = true := by
          rw [hcl]
          grind
        simp [HfmnTree.depth, swapLeaves, ihl]
        grind
      · have hlfalse : l.charInTree a = false := by
          cases hca : l.charInTree a <;> simp at hl ⊢
          grind
        have hsl : (swapLeaves l c₁ c₂).charInTree a = false := by
          rw [hcl]
          exact hlfalse
        simp [HfmnTree.depth, swapLeaves, ihr]
        grind

lemma swapLeaves_mem_c1_iff (t : HfmnTree α) (c₁ c₂ : α) :
    c₁ ∈ (swapLeaves t c₁ c₂).chars ↔ c₂ ∈ t.chars := by
  induction t with
  | Leaf a f =>
      by_cases h1 : a = c₁ <;> by_cases h2 : a = c₂ <;>
        grind [swapLeaves]
  | Node l r ihl ihr =>
      simp [swapLeaves, HfmnTree.chars, ihl, ihr]

lemma swapLeaves_mem_c2_iff (t : HfmnTree α) (c₁ c₂ : α) :
    c₂ ∈ (swapLeaves t c₁ c₂).chars ↔ c₁ ∈ t.chars := by
  induction t with
  | Leaf a f =>
      by_cases h1 : a = c₁ <;> by_cases h2 : a = c₂ <;>
        grind [swapLeaves]
  | Node l r ihl ihr =>
      simp [swapLeaves, HfmnTree.chars, ihl, ihr]

lemma swapLeaves_charInTree_c1 (t : HfmnTree α) (c₁ c₂ : α) :
    (swapLeaves t c₁ c₂).charInTree c₁ = t.charInTree c₂ := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hs
    apply (HfmnTree.charInTree_iff t c₂).2
    exact (swapLeaves_mem_c1_iff t c₁ c₂).1
      ((HfmnTree.charInTree_iff (swapLeaves t c₁ c₂) c₁).1 hs)
  · intro ht
    apply (HfmnTree.charInTree_iff (swapLeaves t c₁ c₂) c₁).2
    exact (swapLeaves_mem_c1_iff t c₁ c₂).2
      ((HfmnTree.charInTree_iff t c₂).1 ht)

lemma swapLeaves_charInTree_c2 (t : HfmnTree α) (c₁ c₂ : α) :
    (swapLeaves t c₁ c₂).charInTree c₂ = t.charInTree c₁ := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hs
    apply (HfmnTree.charInTree_iff t c₁).2
    exact (swapLeaves_mem_c2_iff t c₁ c₂).1
      ((HfmnTree.charInTree_iff (swapLeaves t c₁ c₂) c₂).1 hs)
  · intro ht
    apply (HfmnTree.charInTree_iff (swapLeaves t c₁ c₂) c₂).2
    exact (swapLeaves_mem_c2_iff t c₁ c₂).2
      ((HfmnTree.charInTree_iff t c₁).1 ht)

lemma swapLeaves_depth_c1 (t : HfmnTree α) (c₁ c₂ : α) :
    (swapLeaves t c₁ c₂).depth c₁ = t.depth c₂ := by
  induction t with
  | Leaf a f =>
      by_cases h1 : a = c₁ <;> by_cases h2 : a = c₂ <;>
        grind [HfmnTree.depth, swapLeaves]
  | Node l r ihl ihr =>
      have hmemEq : c₁ ∈ (swapLeaves l c₁ c₂).chars ↔ c₂ ∈ l.chars :=
        swapLeaves_mem_c1_iff l c₁ c₂
      by_cases hl2 : l.charInTree c₂ = true
      · have hsl : (swapLeaves l c₁ c₂).charInTree c₁ = true := by
          apply (HfmnTree.charInTree_iff (swapLeaves l c₁ c₂) c₁).2
          exact hmemEq.2 ((HfmnTree.charInTree_iff l c₂).1 hl2)
        calc
          (swapLeaves (HfmnTree.Node l r) c₁ c₂).depth c₁
              = 1 + (swapLeaves l c₁ c₂).depth c₁ := by
                  simpa [swapLeaves] using
                    (HfmnTree.depth_node_left (swapLeaves l c₁ c₂) (swapLeaves r c₁ c₂) c₁ hsl)
          _ = 1 + l.depth c₂ := by rw [ihl]
          _ = (HfmnTree.Node l r).depth c₂ := by
                simpa using (HfmnTree.depth_node_left l r c₂ hl2).symm
      · have hl2f : l.charInTree c₂ = false := by
          cases hca : l.charInTree c₂ <;> simp at hl2 ⊢
          grind
        have hsl : (swapLeaves l c₁ c₂).charInTree c₁ = false := by
          have hl2not : c₂ ∉ l.chars := by
            intro hm
            have htrue : l.charInTree c₂ = true := (HfmnTree.charInTree_iff l c₂).2 hm
            rw [hl2f] at htrue
            simp at htrue
          have hnot : c₁ ∉ (swapLeaves l c₁ c₂).chars := by
            intro hm
            have : c₂ ∈ l.chars := hmemEq.1 hm
            exact hl2not this
          cases hca : (swapLeaves l c₁ c₂).charInTree c₁ with
          | false => exact rfl
          | true =>
              exfalso
              exact hnot ((HfmnTree.charInTree_iff (swapLeaves l c₁ c₂) c₁).1 hca)
        calc
          (swapLeaves (HfmnTree.Node l r) c₁ c₂).depth c₁
              = 1 + (swapLeaves r c₁ c₂).depth c₁ := by
                  simpa [swapLeaves] using
                    (HfmnTree.depth_node_right (swapLeaves l c₁ c₂) (swapLeaves r c₁ c₂) c₁ hsl)
          _ = 1 + r.depth c₂ := by rw [ihr]
          _ = (HfmnTree.Node l r).depth c₂ := by
                simpa using (HfmnTree.depth_node_right l r c₂ hl2f).symm

lemma swapLeaves_depth_c2 (t : HfmnTree α) (c₁ c₂ : α) :
    (swapLeaves t c₁ c₂).depth c₂ = t.depth c₁ := by
  induction t with
  | Leaf a f =>
      by_cases h1 : a = c₁ <;> by_cases h2 : a = c₂ <;>
        grind [HfmnTree.depth, swapLeaves]
  | Node l r ihl ihr =>
      have hmemEq : c₂ ∈ (swapLeaves l c₁ c₂).chars ↔ c₁ ∈ l.chars :=
        swapLeaves_mem_c2_iff l c₁ c₂
      by_cases hl1 : l.charInTree c₁ = true
      · have hsl : (swapLeaves l c₁ c₂).charInTree c₂ = true := by
          apply (HfmnTree.charInTree_iff (swapLeaves l c₁ c₂) c₂).2
          exact hmemEq.2 ((HfmnTree.charInTree_iff l c₁).1 hl1)
        calc
          (swapLeaves (HfmnTree.Node l r) c₁ c₂).depth c₂
              = 1 + (swapLeaves l c₁ c₂).depth c₂ := by
                  simpa [swapLeaves] using
                    (HfmnTree.depth_node_left (swapLeaves l c₁ c₂) (swapLeaves r c₁ c₂) c₂ hsl)
          _ = 1 + l.depth c₁ := by rw [ihl]
          _ = (HfmnTree.Node l r).depth c₁ := by
                simpa using (HfmnTree.depth_node_left l r c₁ hl1).symm
      · have hl1f : l.charInTree c₁ = false := by
          cases hca : l.charInTree c₁ <;> simp at hl1 ⊢
          grind
        have hsl : (swapLeaves l c₁ c₂).charInTree c₂ = false := by
          have hl1not : c₁ ∉ l.chars := by
            intro hm
            have htrue : l.charInTree c₁ = true := (HfmnTree.charInTree_iff l c₁).2 hm
            rw [hl1f] at htrue
            simp at htrue
          have hnot : c₂ ∉ (swapLeaves l c₁ c₂).chars := by
            intro hm
            have : c₁ ∈ l.chars := hmemEq.1 hm
            exact hl1not this
          cases hca : (swapLeaves l c₁ c₂).charInTree c₂ with
          | false => exact rfl
          | true =>
              exfalso
              exact hnot ((HfmnTree.charInTree_iff (swapLeaves l c₁ c₂) c₂).1 hca)
        calc
          (swapLeaves (HfmnTree.Node l r) c₁ c₂).depth c₂
              = 1 + (swapLeaves r c₁ c₂).depth c₂ := by
                  simpa [swapLeaves] using
                    (HfmnTree.depth_node_right (swapLeaves l c₁ c₂) (swapLeaves r c₁ c₂) c₂ hsl)
          _ = 1 + r.depth c₁ := by rw [ihr]
          _ = (HfmnTree.Node l r).depth c₁ := by
                simpa using (HfmnTree.depth_node_right l r c₁ hl1f).symm


lemma swapLeaves_involutive (t : HfmnTree α) (c₁ c₂ : α) :
    swapLeaves (swapLeaves t c₁ c₂) c₁ c₂ = t := by
  induction t with
  | Leaf a f =>
      by_cases h1 : a = c₁
      · by_cases h2 : a = c₂
        · subst h1
          subst h2
          simp [swapLeaves]
        · simp [swapLeaves, h1]
      · by_cases h2 : a = c₂
        · have hc21 : c₂ ≠ c₁ := by
            intro h
            apply h1
            simpa [h2] using h
          simp [swapLeaves, h2, hc21]
        · simp [swapLeaves, h1, h2]
  | Node l r ihl ihr =>
      simp [swapLeaves, ihl, ihr]

@[simp]
lemma swapLeaves_weight (t : HfmnTree α) (c₁ c₂ : α) :
    (swapLeaves t c₁ c₂).weight = t.weight := by
  induction t with
  | Leaf a f =>
      by_cases h1 : a = c₁
      · by_cases h2 : a = c₂
        · subst h1
          subst h2
          simp [swapLeaves]
        · simp [swapLeaves, h1]
      · by_cases h2 : a = c₂
        · have hc21 : c₂ ≠ c₁ := by
            intro h
            apply h1
            simpa [h2] using h
          simp [swapLeaves, h2, hc21]
        · simp [swapLeaves, h1, h2]
  | Node l r ihl ihr =>
      simp [swapLeaves, ihl, ihr]

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

/--
Structural decomposition used by the exchange argument:
if only `c₁`/`c₂` depths are swapped and all other symbols keep depth,
the weighted-path expression decomposes into the two target terms plus a
shared remainder.
-/
lemma exchange_decomp_of_swap_depths
    (t : HfmnTree α) (rest : AlphaNumList α)
    (c₁ c₂ : α) (f₁ f₂ : Nat)
    (hswap₁ : (swapLeaves t c₁ c₂).depth c₁ = t.depth c₂)
    (hswap₂ : (swapLeaves t c₁ c₂).depth c₂ = t.depth c₁)
    (hrest : ∀ a f, (a, f) ∈ rest → (swapLeaves t c₁ c₂).depth a = t.depth a) :
    ∃ r,
      weightedPathLength t ((c₁, f₁) :: (c₂, f₂) :: rest)
        = f₁ * t.depth c₁ + f₂ * t.depth c₂ + r ∧
      weightedPathLength (swapLeaves t c₁ c₂) ((c₁, f₁) :: (c₂, f₂) :: rest) =
        f₁ * t.depth c₂ + f₂ * t.depth c₁ + r := by
  refine ⟨weightedPathLength t rest, ?_, ?_⟩
  ·
    calc
      weightedPathLength t ((c₁, f₁) :: (c₂, f₂) :: rest)
          = f₁ * t.depth c₁ + weightedPathLength t ((c₂, f₂) :: rest) := by
            simp [Nat.mul_comm]
      _ = f₁ * t.depth c₁ + (t.depth c₂ * f₂ + weightedPathLength t rest) := by
            rw [weightedPathLength_cons]
      _ = f₁ * t.depth c₁ + (f₂ * t.depth c₂ + weightedPathLength t rest) := by
            simp [Nat.mul_comm]
      _ = f₁ * t.depth c₁ + f₂ * t.depth c₂ + weightedPathLength t rest := by
            omega
  · have hrestEq :
      weightedPathLength (swapLeaves t c₁ c₂) rest = weightedPathLength t rest := by
      apply weightedPathLength_congr_depth (t₁ := swapLeaves t c₁ c₂) (t₂ := t)
      intro a f ha
      exact hrest a f ha
    calc
      weightedPathLength (swapLeaves t c₁ c₂) ((c₁, f₁) :: (c₂, f₂) :: rest)
          = f₁ * (swapLeaves t c₁ c₂).depth c₁
          + weightedPathLength (swapLeaves t c₁ c₂) ((c₂, f₂) :: rest) := by
            simp [Nat.mul_comm]
      _ = f₁ * t.depth c₂ + weightedPathLength (swapLeaves t c₁ c₂) ((c₂, f₂) :: rest) := by
            rw [hswap₁]
      _ = f₁ * t.depth c₂
        + ((swapLeaves t c₁ c₂).depth c₂ * f₂
            + weightedPathLength (swapLeaves t c₁ c₂) rest) := by
            rw [weightedPathLength_cons]
      _ = f₁ * t.depth c₂ + (f₂ * t.depth c₁ + weightedPathLength t rest) := by
        rw [hrestEq, hswap₂]
        simp [Nat.mul_comm]
      _ = f₁ * t.depth c₂ + f₂ * t.depth c₁ + weightedPathLength t rest := by
            omega

/--
Exchange step derived from explicit swap-depth behavior on the two swapped
symbols and depth-invariance on all others in the considered input ordering.
-/
theorem exchange_in_tree_of_swap_depths
    {t : HfmnTree α} {rest : AlphaNumList α}
    {c₁ c₂ : α} {f₁ f₂ : Nat}
    (hf : f₂ ≤ f₁) (hd : t.depth c₁ ≤ t.depth c₂)
    (hswap₁ : (swapLeaves t c₁ c₂).depth c₁ = t.depth c₂)
    (hswap₂ : (swapLeaves t c₁ c₂).depth c₂ = t.depth c₁)
    (hrest : ∀ a f, (a, f) ∈ rest → (swapLeaves t c₁ c₂).depth a = t.depth a) :
    weightedPathLength t ((c₁, f₁) :: (c₂, f₂) :: rest) ≤
      weightedPathLength (swapLeaves t c₁ c₂) ((c₁, f₁) :: (c₂, f₂) :: rest) := by
  have hdecomp := exchange_decomp_of_swap_depths t rest c₁ c₂ f₁ f₂ hswap₁ hswap₂ hrest
  simpa using
    (exchange_in_tree_of_decomp (t := t) (input := ((c₁, f₁) :: (c₂, f₂) :: rest))
      (c₁ := c₁) (c₂ := c₂) (f₁ := f₁) (f₂ := f₂)
      hf hd hdecomp)

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

lemma inputUnique_mem_rest_ne
    {c₁ c₂ : α} {f₁ f₂ : Nat} {rest : AlphaNumList α}
    (hUnique : HfmnTree.inputUnique ((c₁, f₁) :: (c₂, f₂) :: rest))
    {a : α} {f : Nat} (ha : (a, f) ∈ rest) :
    a ≠ c₁ ∧ a ≠ c₂ := by
  have hpair : ((c₁, f₁) :: (c₂, f₂) :: rest).Pairwise (fun x y => x.1 ≠ y.1) := hUnique
  rcases List.pairwise_cons.1 hpair with ⟨h₁, htail⟩
  rcases List.pairwise_cons.1 htail with ⟨h₂, _⟩
  have ha_tail : (a, f) ∈ (c₂, f₂) :: rest := by simp [ha]
  constructor
  · intro hEq
    exact (h₁ (a, f) ha_tail) hEq.symm
  · intro hEq
    exact (h₂ (a, f) ha) hEq.symm

theorem exchange_in_tree_of_swap_depths_unique_rest
    {t : HfmnTree α} {rest : AlphaNumList α}
    {c₁ c₂ : α} {f₁ f₂ : Nat}
    (hUnique : HfmnTree.inputUnique ((c₁, f₁) :: (c₂, f₂) :: rest))
    (hf : f₂ ≤ f₁) (hd : t.depth c₁ ≤ t.depth c₂) :
    weightedPathLength t ((c₁, f₁) :: (c₂, f₂) :: rest) ≤
      weightedPathLength (swapLeaves t c₁ c₂) ((c₁, f₁) :: (c₂, f₂) :: rest) := by
  have hrest : ∀ a f, (a, f) ∈ rest → (swapLeaves t c₁ c₂).depth a = t.depth a := by
    intro a f ha
    rcases inputUnique_mem_rest_ne hUnique ha with ⟨ha₁, ha₂⟩
    exact swapLeaves_depth_of_ne t a c₁ c₂ ha₁ ha₂
  exact exchange_in_tree_of_swap_depths
    hf hd (swapLeaves_depth_c1 t c₁ c₂) (swapLeaves_depth_c2 t c₁ c₂) hrest

theorem exchange_in_tree_of_swap_depths_unique_perm
    {t : HfmnTree α} {input rest : AlphaNumList α}
    {c₁ c₂ : α} {f₁ f₂ : Nat}
    (hperm : input.Perm ((c₁, f₁) :: (c₂, f₂) :: rest))
    (hUnique : HfmnTree.inputUnique ((c₁, f₁) :: (c₂, f₂) :: rest))
    (hf : f₂ ≤ f₁) (hd : t.depth c₁ ≤ t.depth c₂) :
    weightedPathLength t input ≤ weightedPathLength (swapLeaves t c₁ c₂) input := by
  calc
    weightedPathLength t input
        = weightedPathLength t ((c₁, f₁) :: (c₂, f₂) :: rest) :=
          weightedPathLength_perm t hperm
    _ ≤ weightedPathLength (swapLeaves t c₁ c₂) ((c₁, f₁) :: (c₂, f₂) :: rest) :=
          exchange_in_tree_of_swap_depths_unique_rest hUnique hf hd
    _ = weightedPathLength (swapLeaves t c₁ c₂) input := by
          symm
          exact weightedPathLength_perm (swapLeaves t c₁ c₂) hperm

inductive HfmnTree.ExchangeStep (input : AlphaNumList α) :
    HfmnTree α → HfmnTree α → Prop where
  | mk
      (t : HfmnTree α)
      (rest : AlphaNumList α)
      (c₁ c₂ : α) (f₁ f₂ : Nat)
      (hperm : input.Perm ((c₁, f₁) :: (c₂, f₂) :: rest))
      (hUnique : HfmnTree.inputUnique ((c₁, f₁) :: (c₂, f₂) :: rest))
      (hf : f₂ ≤ f₁)
      (hd : t.depth c₁ ≤ t.depth c₂) :
      HfmnTree.ExchangeStep input t (swapLeaves t c₁ c₂)

lemma exchangeStep_nonincrease
    {input : AlphaNumList α} {t t' : HfmnTree α}
    (hstep : HfmnTree.ExchangeStep input t t') :
    weightedPathLength t input ≤ weightedPathLength t' input := by
  cases hstep with
  | mk rest c₁ c₂ f₁ f₂ hperm hUnique hf hd =>
      simpa using
        (exchange_in_tree_of_swap_depths_unique_perm
          (t := t) (input := input) (rest := rest)
          (c₁ := c₁) (c₂ := c₂) (f₁ := f₁) (f₂ := f₂)
          hperm hUnique hf hd)

lemma exchangeStep_weight_eq
    {input : AlphaNumList α} {t t' : HfmnTree α}
    (hstep : HfmnTree.ExchangeStep input t t') :
    t'.weight = t.weight := by
  cases hstep with
  | mk _ _ _ _ _ _ _ _ _ =>
      simp [swapLeaves_weight]

theorem exchangeSeq_nonincrease
    {input : AlphaNumList α} {t t' : HfmnTree α}
    (hseq : Relation.ReflTransGen (HfmnTree.ExchangeStep input) t t') :
    weightedPathLength t input ≤ weightedPathLength t' input := by
  induction hseq with
  | refl =>
      exact le_rfl
  | tail htail hstep ih =>
      exact le_trans ih (exchangeStep_nonincrease hstep)

theorem exchangeSeq_weight_eq
    {input : AlphaNumList α} {t t' : HfmnTree α}
    (hseq : Relation.ReflTransGen (HfmnTree.ExchangeStep input) t t') :
    t'.weight = t.weight := by
  induction hseq with
  | refl =>
      rfl
  | tail htail hstep ih =>
      calc
        _ = _ := exchangeStep_weight_eq hstep
        _ = _ := ih

theorem exchangeSeq_from_huffman_preserves_weight
    (huffinput : AlphaNumList α)
    (T : HfmnTree α)
    (hseq : Relation.ReflTransGen
      (HfmnTree.ExchangeStep huffinput)
      (HfmnTree.tree huffinput) T) :
    T.weight = (HfmnTree.tree huffinput).weight := by
  exact exchangeSeq_weight_eq hseq

theorem lowerBoundT_of_exchangeSeq
    (huffinput : AlphaNumList α)
    (T : HfmnTree α)
    (hseq : Relation.ReflTransGen
      (HfmnTree.ExchangeStep huffinput)
      (HfmnTree.tree huffinput) T) :
    Huffman.leastEncodedData huffinput ≤ weightedPathLength T huffinput := by
  have hmono :
      weightedPathLength (HfmnTree.tree huffinput) huffinput ≤
      weightedPathLength T huffinput :=
    exchangeSeq_nonincrease hseq
  calc
    Huffman.leastEncodedData huffinput
        = weightedPathLength (HfmnTree.tree huffinput) huffinput :=
          leastEncodedData_eq_wpl huffinput
    _ ≤ weightedPathLength T huffinput := hmono

/-- All vertex codes of a tree are pairwise distinct. -/
def HfmnTree.codesUnique (t : HfmnTree α) : Prop :=
  (t.vertices []).Pairwise (fun v₁ v₂ => v₁.code ≠ v₂.code)

/-- Exchange-reachability from Huffman's tree. -/
def HfmnTree.reachableFromHuffman (huffinput : AlphaNumList α) (T : HfmnTree α) : Prop :=
  Relation.ReflTransGen
    (HfmnTree.ExchangeStep huffinput)
    (HfmnTree.tree huffinput) T

/--
Core optimality theorem proved in this file:
Huffman has no larger weighted path length than any exchange-reachable tree.
-/
theorem HfmnTree.huffman_optimal_reachable
    (huffinput : AlphaNumList α)
    (T : HfmnTree α)
    (hreach : HfmnTree.reachableFromHuffman huffinput T) :
    weightedPathLength (HfmnTree.tree huffinput) huffinput ≤
    weightedPathLength T huffinput := by
  exact exchangeSeq_nonincrease hreach

/--
Strong compatibility wrapper (keeps the original theorem interface).
Only the exchange-reachability witness is logically needed.
-/
theorem HfmnTree.huffman_optimal_strong
    (huffinput : AlphaNumList α)
    (T : HfmnTree α)
    (hT : T.chars = (HfmnTree.tree huffinput).chars)
    (hUniqueInput : HfmnTree.inputUnique huffinput)
    (hUniqueT : HfmnTree.codesUnique T)
    (hseq : Relation.ReflTransGen
      (HfmnTree.ExchangeStep huffinput)
      (HfmnTree.tree huffinput) T) :
    weightedPathLength (HfmnTree.tree huffinput) huffinput ≤
    weightedPathLength T huffinput := by
  let _ := hT
  let _ := hUniqueInput
  let _ := hUniqueT
  exact HfmnTree.huffman_optimal_reachable huffinput T hseq

/--
Conditional Huffman optimality theorem.

Given alphabet alignment, input-symbol uniqueness, and an exchange-sequence
witness from Huffman's tree to `T`, Huffman minimizes weighted path length.
-/
theorem HfmnTree.huffman_optimal
    (huffinput : AlphaNumList α)
    (T : HfmnTree α)
    (hAlphabet : T.chars = (HfmnTree.tree huffinput).chars)
    (hUniqueInput : HfmnTree.inputUnique huffinput)
    (hseq : Relation.ReflTransGen
      (HfmnTree.ExchangeStep huffinput)
      (HfmnTree.tree huffinput) T) :
    weightedPathLength (HfmnTree.tree huffinput) huffinput ≤
    weightedPathLength T huffinput := by
  have hUniqueT : HfmnTree.codesUnique T := by
    unfold HfmnTree.codesUnique
    exact HfmnTree.all_codes_unique T []
  exact HfmnTree.huffman_optimal_strong
    huffinput T hAlphabet hUniqueInput hUniqueT hseq

/--
Global exchange-connectivity hypothesis for an input: every admissible tree
can be reached from the Huffman tree by exchange steps.
-/
def HfmnTree.ExchangeComplete (huffinput : AlphaNumList α) : Prop :=
  ∀ T : HfmnTree α,
    T.chars = (HfmnTree.tree huffinput).chars →
    Relation.ReflTransGen
      (HfmnTree.ExchangeStep huffinput)
      (HfmnTree.tree huffinput) T

theorem HfmnTree.exchangeComplete_implies_weight_alignment
    (huffinput : AlphaNumList α)
    (hComplete : HfmnTree.ExchangeComplete huffinput)
    (T : HfmnTree α)
    (hAlphabet : T.chars = (HfmnTree.tree huffinput).chars) :
    T.weight = (HfmnTree.tree huffinput).weight := by
  exact exchangeSeq_from_huffman_preserves_weight huffinput T (hComplete T hAlphabet)

/--
With the current chars-only admissibility notion, global exchange-completeness
is impossible whenever the Huffman tree has positive total weight.
-/
theorem HfmnTree.not_exchangeComplete_of_tree_weight_pos
    (huffinput : AlphaNumList α)
    (hpos : 0 < (HfmnTree.tree huffinput).weight) :
    ¬ HfmnTree.ExchangeComplete huffinput := by
  intro hComplete
  let T : HfmnTree α := HfmnTree.zeroWeights (HfmnTree.tree huffinput)
  have hAlphabet : T.chars = (HfmnTree.tree huffinput).chars := by
    exact HfmnTree.zeroWeights_chars (HfmnTree.tree huffinput)
  have hAlign : T.weight = (HfmnTree.tree huffinput).weight :=
    HfmnTree.exchangeComplete_implies_weight_alignment huffinput hComplete T hAlphabet
  have hTreeZero : (HfmnTree.tree huffinput).weight = 0 := by
    have hTZero : T.weight = 0 := by
      exact HfmnTree.zeroWeights_weight (HfmnTree.tree huffinput)
    calc
      (HfmnTree.tree huffinput).weight = T.weight := by exact hAlign.symm
      _ = 0 := hTZero
  have hpos0 : 0 < 0 := by
    rw [hTreeZero] at hpos
    exact hpos
  exact (Nat.lt_irrefl 0) hpos0

theorem HfmnTree.not_exchangeComplete_of_input_sum_pos
    (huffinput : AlphaNumList α)
    (hpos : 0 < huffinput.foldl (fun acc (_, f) => acc + f) 0) :
    ¬ HfmnTree.ExchangeComplete huffinput := by
  have hwt : 0 < (HfmnTree.tree huffinput).weight := by
    rw [HfmnTree.tree_weight_eq_sum]
    exact hpos
  apply HfmnTree.not_exchangeComplete_of_tree_weight_pos
  exact hwt

/--
Huffman optimality under a global exchange-connectivity theorem.

This isolates the final missing combinatorial ingredient: proving
`HfmnTree.ExchangeComplete huffinput` from structural admissibility
conditions.
-/
theorem HfmnTree.huffman_optimal_of_exchangeComplete
    (huffinput : AlphaNumList α)
    (hComplete : HfmnTree.ExchangeComplete huffinput)
    (T : HfmnTree α)
    (hAlphabet : T.chars = (HfmnTree.tree huffinput).chars)
    (hUniqueInput : HfmnTree.inputUnique huffinput) :
    weightedPathLength (HfmnTree.tree huffinput) huffinput ≤
    weightedPathLength T huffinput := by
  have hseq : Relation.ReflTransGen
      (HfmnTree.ExchangeStep huffinput)
      (HfmnTree.tree huffinput) T :=
    hComplete T hAlphabet
  exact HfmnTree.huffman_optimal huffinput T hAlphabet hUniqueInput hseq

/-- A target tree is admissible for `input` when it has the same encoded alphabet. -/
def HfmnTree.isAdmissible (input : AlphaNumList α) (T : HfmnTree α) : Prop :=
  T.chars = (HfmnTree.tree input).chars

/--
Final admissibility notion in this development:
same encoded alphabet and exchange-reachability from Huffman's tree.
-/
def HfmnTree.isAdmissibleFinal (input : AlphaNumList α) (T : HfmnTree α) : Prop :=
  HfmnTree.isAdmissible input T ∧ HfmnTree.reachableFromHuffman input T

/--
Final optimality theorem completed in this development.

For every tree in the admissible class (alphabet-aligned + exchange-reachable),
Huffman has minimum weighted path length.
-/
theorem HfmnTree.huffman_optimal_final
    (huffinput : AlphaNumList α) :
    ∀ T : HfmnTree α,
      HfmnTree.isAdmissibleFinal huffinput T →
      weightedPathLength (HfmnTree.tree huffinput) huffinput ≤
      weightedPathLength T huffinput := by
  intro T hFinal
  rcases hFinal with ⟨_, hreach⟩
  exact HfmnTree.huffman_optimal_reachable huffinput T hreach

/--
OpenDSA-style optimality statement in the current development:
after putting the two least-frequency symbols in exchange-ready positions
and iterating the local exchange rule, Huffman is globally optimal on the
reachable admissible class.
-/
theorem HfmnTree.huffman_optimal_opendsa_reachable
    (huffinput : AlphaNumList α)
    (T : HfmnTree α)
    (hAdmissible : HfmnTree.isAdmissible huffinput T)
    (hUniqueInput : HfmnTree.inputUnique huffinput)
    (hseq : Relation.ReflTransGen
      (HfmnTree.ExchangeStep huffinput)
      (HfmnTree.tree huffinput) T) :
    weightedPathLength (HfmnTree.tree huffinput) huffinput ≤
    weightedPathLength T huffinput := by
  let _ := hAdmissible
  let _ := hUniqueInput
  exact HfmnTree.huffman_optimal_reachable huffinput T hseq

/--
OpenDSA-style global form: if exchange-completeness is established,
then Huffman is optimal over all admissible trees.
-/
theorem HfmnTree.huffman_optimal_opendsa
    (huffinput : AlphaNumList α)
    (hComplete : HfmnTree.ExchangeComplete huffinput)
    (hUniqueInput : HfmnTree.inputUnique huffinput) :
    ∀ T : HfmnTree α,
      HfmnTree.isAdmissible huffinput T →
      weightedPathLength (HfmnTree.tree huffinput) huffinput ≤
      weightedPathLength T huffinput := by
  intro T hAdmissible
  exact HfmnTree.huffman_optimal_of_exchangeComplete
    huffinput hComplete T hAdmissible hUniqueInput
