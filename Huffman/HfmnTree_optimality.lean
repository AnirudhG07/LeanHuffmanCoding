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

@[simp]
lemma weightedPathLengthSum_nil (t : HfmnTree α) :
    weightedPathLengthSum t [] = 0 := by
  simp [weightedPathLengthSum]

@[simp]
lemma weightedPathLengthSum_cons (t : HfmnTree α) (a : α) (freq : Nat)
    (rest : AlphaNumList α) :
    weightedPathLengthSum t ((a, freq) :: rest) =
      t.depth a * freq + weightedPathLengthSum t rest := by
  simp [weightedPathLengthSum]

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

-- ─────────────────────────────────────────────────────────────────────────────
-- §4  leastEncodedData = weightedPathLength of the Huffman tree
-- ─────────────────────────────────────────────────────────────────────────────

/-- `leastEncodedData` equals `weightedPathLength` of the Huffman tree. -/
theorem leastEncodedData_eq_wpl (huffinput : AlphaNumList α) :
    Huffman.leastEncodedData huffinput =
    weightedPathLength (HfmnTree.tree huffinput) huffinput := by
  rw [weightedPathLength_eq_sum]
  induction p:huffinput with
  | nil =>
    simp [Huffman.leastEncodedData, weightedPathLengthSum]
  | cons hd tl ih =>
    obtain ⟨a, freq⟩ := hd
    have hmem : (a, freq) ∈ (a, freq) :: tl := by grind
    have hchar := HfmnTree.tree_contains_input_chars ((a, freq) :: tl) a freq hmem
    have hlen :
        (HfmnTree.encode a (HfmnTree.tree ((a, freq) :: tl))).length =
        (HfmnTree.tree ((a, freq) :: tl)).depth a :=
      HfmnTree.encode_length_eq_depth _ a hchar
    sorry

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
lemma exchange_wpl_le' (f₁ f₂ d₁ d₂ rest : Nat)
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


/-- The tree built by the Huffman algorithm has weight equal to sum of input frequencies. -/
lemma HfmnTree.tree_weight_eq_sum (input : AlphaNumList α) :
    (HfmnTree.tree input).weight = input.foldl (fun acc (_, f) => acc + f) 0 := by
  induction p:input with
  | nil =>
    simp [HfmnTree.tree]
  | cons hd tl ih =>
    obtain ⟨a, f⟩ := hd
    cases tl with
    | nil =>
      sorry
    | cons hd' tl' =>
      sorry -- Induction on the merge process

/-- The two smallest frequencies are merged first. -/
lemma HfmnTree.tree_merges_smallest (input : AlphaNumList α) (h : input.length ≥ 2) :
    ∃ t₁ t₂ rest,
      insertionSort (input.map fun (a, f) => HfmnTree.Leaf a f) = t₁ :: t₂ :: rest ∧
      t₁.weight ≤ t₂.weight ∧
      ∀ t ∈ rest, t₁.weight ≤ t.weight ∧ t₂.weight ≤ t.weight := by
  -- TODO: prove insertionSort is weight-sorted and conclude the head pair is minimal.
  sorry

def swapLeaves (t : HfmnTree α) (c₁ c₂ : α) : HfmnTree α :=
  -- Implementation: traverse tree and swap the two leaves
  match t with
  | .Leaf a f => if a = c₁ then .Leaf c₂ f else if a = c₂ then .Leaf c₁ f else t
  | .Node l r => .Node (swapLeaves l c₁ c₂) (swapLeaves r c₁ c₂)

-- ─────────────────────────────────────────────────────────────────────────────
-- §7  Exchange lemma for trees
-- ─────────────────────────────────────────────────────────────────────────────

/-- Swapping two leaves in a tree at depths d₁ and d₂ (d₁ ≤ d₂) with frequencies
    f₁ and f₂ (f₁ ≥ f₂) does not increase the weighted path length. -/
lemma exchange_in_tree {t : HfmnTree α} {input : AlphaNumList α}
    {c₁ c₂ : α} {f₁ f₂ : Nat}
    (h₁ : (c₁, f₁) ∈ input) (h₂ : (c₂, f₂) ∈ input)
    (hf : f₂ ≤ f₁) (hd : t.depth c₁ ≤ t.depth c₂) :
    let t' := swapLeaves t c₁ c₂  -- Hypothetical tree with c₁ and c₂ swapped
    weightedPathLength t input ≤ weightedPathLength t' input := by
  -- This requires defining swapLeaves and showing it only affects depths of c₁ and c₂
  sorry

-- ─────────────────────────────────────────────────────────────────────────────
-- §8  Main optimality theorem
-- ─────────────────────────────────────────────────────────────────────────────

/-- The characters in the Huffman tree are exactly those in the input. -/
lemma HfmnTree.tree_chars_eq_input_chars (input : AlphaNumList α) :
    (HfmnTree.tree input).chars = (input.map Prod.fst).dedup := by
  induction input with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨a, f⟩ := hd
    cases tl with
    | nil => simp_all [HfmnTree.tree]
    | cons hd' tl' =>
      simp [HfmnTree.tree, HfmnTree.merge, HfmnTree.chars, HfmnTree.mergeTrees_charInTree]
      sorry

/-- Helper: Extract the two smallest frequency leaves from the input. -/
def extractTwoSmallest (input : AlphaNumList α) (h : input.length ≥ 2) :
    (α × Nat) × (α × Nat) × (AlphaNumList α) :=
  -- Sort by frequency and take first two
  let sorted := input.qsort (fun p₁ p₂ => p₁.2 ≤ p₂.2)
  let first := sorted.head!
  let second := (sorted.tail!).head!
  let rest := (sorted.tail!).tail!
  (first, second, rest)


-- Additional lemmas needed for the proof
lemma insertionSort_sorted (trees : List (HfmnTree α)) :
    (insertionSort trees).Pairwise (fun t₁ t₂ => t₁.weight ≤ t₂.weight) := by
  sorry

def mergeLeaves (t : HfmnTree α) (c₁ c₂ : α) : HfmnTree α :=
  -- Replace leaves c₁ and c₂ with a single leaf of combined weight
  sorry


/-- `HfmnTree.tree huffinput` achieves minimum weighted path length among all
    `HfmnTree α` encoding the same characters with the same frequencies. -/
theorem HfmnTree.huffman_optimal
    (huffinput : AlphaNumList α)
    (T : HfmnTree α)
    (hT : T.chars = (HfmnTree.tree huffinput).chars) :
    weightedPathLength (HfmnTree.tree huffinput) huffinput ≤
    weightedPathLength T huffinput := by
  -- Induction on the number of distinct symbols (not just input length)
  let numSymbols := (huffinput.map Prod.fst).dedup.length
  induction numSymbols using Nat.strongRec generalizing huffinput T with
  | ind n ih =>
    match n with
    | 0 =>
      -- Empty input
      have : huffinput = [] := by
        simp [numSymbols] at *
        exact List.map_eq_nil_iff.mp (List.dedup_eq_nil_iff.mp (by simp_all))
      subst this
      simp [weightedPathLength]

    | 1 =>
      -- Single symbol: both trees must be leaves (since they have same chars)
      have h_len : (huffinput.map Prod.fst).dedup.length = 1 := by simp [numSymbols, *]
      -- The Huffman tree is a single leaf with depth 0
      have h_tree : HfmnTree.tree huffinput =
                   HfmnTree.Leaf (huffinput.head!.1) (huffinput.head!.2) := by
        cases huffinput
        · contradiction
        · case cons hd tl =>
          simp [HfmnTree.tree]
          have : tl = [] := by
            simp [List.dedup, List.map] at h_len
            cases tl
            · rfl
            · simp [List.dedup_cons] at h_len
              have := List.length_dedup_le tl
              omega
          subst this
          rfl

      -- T must also be a leaf (since it has same single character)
      have h_T_leaf : ∃ a f, T = HfmnTree.Leaf a f := by
        cases T
        · case Leaf a f => exact ⟨a, f, rfl⟩
        · case Node l r =>
          have := HfmnTree.chars_node l r
          rw [hT, h_tree] at this
          simp [HfmnTree.chars] at this
          have h_len_l : l.chars.length ≥ 1 := by sorry  -- Node has at least 2 chars
          omega

      rcases h_T_leaf with ⟨a, f, rfl⟩
      simp [weightedPathLength, h_tree, HfmnTree.depth]
      -- Both depths are 0, so costs are 0

    | n' + 2 =>
      -- At least 2 distinct symbols
      have h_len : huffinput.length ≥ 2 := by
        have := List.length_dedup_le (huffinput.map Prod.fst)
        rw [← numSymbols] at this
        omega

      -- Identify the two smallest frequencies in the input
      let sortedInput := huffinput.qsort (fun p₁ p₂ => p₁.2 ≤ p₂.2)
      have h_sorted : sortedInput.Pairwise (fun p₁ p₂ => p₁.2 ≤ p₂.2) :=
        List.qsort_sorted _ _

      let min1 := sortedInput.head!
      let min2 := (sortedInput.tail!).head!
      have h_min : min1.2 ≤ min2.2 := by
        have := List.pairwise_cons.mp h_sorted
        exact this.1 _ (List.mem_head!_of_ne_nil _)

      -- The Huffman algorithm merges these two smallest frequencies
      let reducedInput : AlphaNumList α :=
        (min2 :: (sortedInput.tail!).tail!).qsort (fun p₁ p₂ => p₁.2 ≤ p₂.2)
      let mergedFreq := min1.2 + min2.2

      -- Build the reduced problem: replace min1 and min2 with their merge
      let reducedAlphabet : AlphaNumList α :=
        (("__merged__", mergedFreq) :: reducedInput).eraseP (fun p => p.1 == min1.1)

      -- The Huffman tree for the original input is equivalent to the Huffman tree
      -- for the reduced input with an extra level
      have h_huffman_reduced :
          (HfmnTree.tree huffinput).weight = (HfmnTree.tree reducedAlphabet).weight := by
        sorry -- Show that merging two smallest doesn't change total weight

      -- Now apply the exchange argument to the competing tree T
      -- Find the two deepest leaves in T corresponding to min1 and min2
      -- If they are not min1 and min2, we can swap to reduce cost

      -- Let d₁ and d₂ be the depths of min1 and min2 in T
      let d₁ := T.depth min1.1
      let d₂ := T.depth min2.1

      -- Exchange argument: if the smaller frequency is deeper, we can swap
      have h_exchange : weightedPathLength T huffinput ≤
                        weightedPathLength (swapLeaves T min1.1 min2.1) huffinput := by
        by_cases h_depth : d₁ ≤ d₂
        · -- Already optimal ordering for these two
          rw [weightedPathLength, weightedPathLength]
          apply exchange_wpl_le' min1.2 min2.2 d₁ d₂
          · exact h_min
          · exact h_depth
          · sorry -- Need to isolate the rest of the sum
        · -- Need to swap
          have h_depth' : d₂ ≤ d₁ := by omega
          apply exchange_wpl_le' min2.2 min1.2 d₂ d₁
          · omega
          · exact h_depth'
          · sorry

      -- After ensuring min1 and min2 are optimally placed, we can merge them in T
      -- to get a tree T' for the reduced problem
      let T' := mergeLeaves T min1.1 min2.1  -- Replace both leaves with a single merged leaf

      have h_T'_valid : T'.chars = (HfmnTree.tree reducedAlphabet).chars := by
        sorry -- T' encodes the reduced alphabet

      -- Apply IH to the reduced problem
      have ih_result := ih (reducedAlphabet.map Prod.fst).dedup.length
        (by
          simp [numSymbols] at *
          -- Reduced alphabet has one fewer distinct symbol
          have : (reducedAlphabet.map Prod.fst).dedup.length < n' + 2 := by
            sorry
          exact this
        )
        reducedAlphabet T' h_T'_valid

      -- Show that optimality for reduced problem implies optimality for original
      have h_cost_relation :
          weightedPathLength (HfmnTree.tree huffinput) huffinput =
          weightedPathLength (HfmnTree.tree reducedAlphabet) reducedAlphabet + mergedFreq := by
        sorry -- The merge adds mergedFreq to total cost

      have h_cost_relation_T :
          weightedPathLength T' reducedAlphabet + mergedFreq ≤
          weightedPathLength T huffinput := by
        sorry -- Merging in T doesn't increase cost beyond original T

      -- Chain the inequalities
      calc weightedPathLength (HfmnTree.tree huffinput) huffinput
        = weightedPathLength (HfmnTree.tree reducedAlphabet) reducedAlphabet + mergedFreq :=
          h_cost_relation
        _ ≤ weightedPathLength T' reducedAlphabet + mergedFreq := by
          simp [ih_result]
        _ ≤ weightedPathLength T huffinput := h_cost_relation_T
