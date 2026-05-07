import Mathlib.Tactic
import Aesop


/-!
# Basic Lemma used for proof

This file contains basic lemma about element of finset and their intersections

It provides results showing that if two sets are disjoint,
an element cannot belong to both sets at the same time.
-/

/--
If `A` and `B` are disjoint (their intersection is empty),
no element can belong to both sets at the same time.
-/
lemma mem_inter_empty {α} [DecidableEq α]
  (A B : Finset α) (a : α) (h : A ∩ B = ∅)
  (h1 : a ∈ A) (h2 : a ∈ B) : False := by
  have : a ∈ A ∩ B := Finset.mem_inter_of_mem h1 h2
  simp [h] at this


/-!
# Basic Definitions for Huffman Trees

This file introduces the core definition used throughout the
formalisation of Huffman’s algorithm.
It defines the Huffman tree and forest, along with their properties:
which are alphabets, consistent, frequencies, depth, height.
Additional tree properties weight and cost is also defined.

`minima` and `optimum` definition which are used in optimality proofs is also introduced here.

Lemmas about main definitions describing its properties and relationships is also included.

## Definitions

- `HuffmanTree α`    : Datatype representing a Huffman tree with symbols of type `α`.
- `Forest α`         : A list of Huffman trees.
- `alphabet t`       : The set of symbols occurring in tree `t`.
- `consistent t`     : Condition stating that each symbol only appears in one leaf in tree `t`.
- `depth t a`        : Depth of symbol `a` in tree `t`.
- `height t`         : Height of the tree `t`.
- `freq t a`         : Frequency of symbol `a` in tree `t`.
- `weight t`         : Weight of the tree `t`.
- `cost t`           : Cost of tree `t`.
- `optimum t`        : Condition stating that tree `t` is optimal.
- `minima t a b`     : Condition stating that two symbols have the lowest frequencies in tree `t`.
-/

/--
A Huffman tree over an alphabet `α`.

Leaves are labeled by symbols and their frequencies, while
nodes are labeled by sum of frequencies of their subtrees.
-/
inductive HuffmanTree (α : Type) where
  | leaf (w : Nat) (a : α) : HuffmanTree α
  | node (w : Nat) (t1 : HuffmanTree α) (t2 : HuffmanTree α) : HuffmanTree α

/--
A list of Huffman trees.
-/
abbrev Forest (α) := List (HuffmanTree α)

/--
The set of symbols occurring in the leaves of a Huffman tree.
-/
def alphabet {α} [DecidableEq α] : HuffmanTree α → Finset α
  | HuffmanTree.leaf _ a => {a}
  | HuffmanTree.node _ t1 t2 => alphabet t1 ∪ alphabet t2

/--
The set of symbols occurring in a forest of Huffman trees.
-/
def alphabetF {α} [DecidableEq α] : Forest α → Finset α
  | [] => Finset.empty
  | t :: ts => alphabet t ∪ alphabetF ts

lemma exists_in_alphabet {α} [DecidableEq α] (t : HuffmanTree α) :
  ∃ a, a ∈ alphabet t := by
  induction t <;> aesop(add norm[alphabet])

/--
For two Huffman trees with disjoint alphabets, `a` is either:
- in `t1`
- in `t2`
- neither in `t1` nor `t2`
-/
lemma alphabet_cases {α} [DecidableEq α]
  (a : α) (t1 t2 : HuffmanTree α)
  (hdis : alphabet t1 ∩ alphabet t2 = ∅) :
  (a ∈ alphabet t1 ∧ a ∉ alphabet t2) ∨
  (a ∉ alphabet t1 ∧ a ∈ alphabet t2) ∨
  (a ∉ alphabet t1 ∧ a ∉ alphabet t2) := by
  by_cases h1 : a ∈ alphabet t1 <;> grind[mem_inter_empty]

/--
A Huffman tree is consistent if each symbol only appears in one leaf in a tree and
for each inner node the alphabets of the two subtrees are disjoint.
-/
def consistent {α} [DecidableEq α] : HuffmanTree α → Prop
  | HuffmanTree.leaf _ _ => True
  | HuffmanTree.node _ t1 t2 => (alphabet t1 ∩ alphabet t2 = ∅) ∧ consistent t1 ∧ consistent t2

/--
A forest of Huffman trees is `consistent` if all trees in the forest
are consistent and have disjoint alphabets.
-/
def consistentF {α} [DecidableEq α] : Forest α → Prop
  | [] => True
  | t :: ts => (alphabet t ∩ alphabetF ts = ∅) ∧ consistent t ∧ consistentF ts

/--
A custom induction rule for Huffman trees under the assumption
of consistency. It is used throughout the development to simplify proofs.
-/
theorem huffmanTree_induct_consistent {α} [DecidableEq α]
{P : (t : HuffmanTree α) → α → consistent t → Prop}
  {t : HuffmanTree α} (a : α) (h_consistent : consistent t)
    (leaf : ∀ wb b (h_consistent : consistent (HuffmanTree.leaf wb b)),
      P (HuffmanTree.leaf wb b) a h_consistent)
    (left : ∀ w t1 t2 (h_consistent : consistent (HuffmanTree.node w t1 t2))
      (h_consistent_t1 : consistent t1) (h_consistent_t2 : consistent t2),
      alphabet t1 ∩ alphabet t2 = ∅ →
      a ∈ alphabet t1 → a ∉ alphabet t2 →
      P t1 a h_consistent_t1 → P t2 a h_consistent_t2 →
      P (HuffmanTree.node w t1 t2) a h_consistent)
    (right : ∀ w t1 t2 (h_consistent : consistent (HuffmanTree.node w t1 t2))
      (h_consistent_t1 : consistent t1) (h_consistent_t2 : consistent t2),
      alphabet t1 ∩ alphabet t2 = ∅ →
      a ∉ alphabet t1 → a ∈ alphabet t2 →
      P t1 a h_consistent_t1 → P t2 a h_consistent_t2 →
      P (HuffmanTree.node w t1 t2) a h_consistent)
    (none : ∀ w t1 t2 (h_consistent : consistent (HuffmanTree.node w t1 t2))
      (h_consistent_t1 : consistent t1) (h_consistent_t2 : consistent t2),
      alphabet t1 ∩ alphabet t2 = ∅ →
      a ∉ alphabet t1 → a ∉ alphabet t2 →
      P t1 a h_consistent_t1 → P t2 a h_consistent_t2 →
      P (HuffmanTree.node w t1 t2) a h_consistent)
  : P t a h_consistent := by
    induction t <;> grind[mem_inter_empty, consistent, alphabet_cases]

/--
Depth is the length of the path from root of tree to a leaf.
-/
def depth {α} [DecidableEq α] : HuffmanTree α → α → Nat
  | HuffmanTree.leaf _ _, _ => 0
  | HuffmanTree.node _ t1 t2, a =>
    if a ∈ alphabet t1 then depth t1 a + 1
    else if a ∈ alphabet t2 then depth t2 a + 1
    else 0

/--
The height of a Huffman tree, the length of the longest path from root to leaf.
-/
def height {α} : HuffmanTree α → Nat
  | HuffmanTree.leaf _ _ => 0
  | HuffmanTree.node _ t1 t2 => max (height t1) (height t2) + 1

/--
The maximum height of all trees in a forest.
-/
def heightF {α} : Forest α → Nat
  | [] => 0
  | t :: ts => max (height t) (heightF ts)

@[simp]
lemma depth_le_height {α} [DecidableEq α] (t : HuffmanTree α) (a : α) :
  depth t a ≤ height t := by
  induction t <;> aesop(add norm[depth, height])

/--
In a consistent Huffman tree, exists a symbol whose depth is equal to the height of the tree.
-/
@[simp]
lemma exists_at_height {α} [DecidableEq α]
  (t : HuffmanTree α) (h_consistent : consistent t) :
  ∃a ∈ alphabet t, depth t a = height t := by
  induction t with
  | leaf w x => aesop (add norm[depth,height, alphabet])
  | node w t1 t2 h1 h2 =>
      simp[alphabet,height,depth]
      grind[mem_inter_empty,consistent]

/--
If a Huffman tree `t` has positive height and is consistent, then any Huffman tree `u`
with the same alphabet also has positive height.
-/
lemma height_gt_0_alphabet_eq_imp_height_gt_0 {α} [DecidableEq α] (t u : HuffmanTree α)
  (h_height : height t > 0) (h_consistent : consistent t)
  (h_alphabet_t_u : alphabet t = alphabet u)
  : height u > 0 := by
  cases t with
  | leaf w x => simp [height] at h_height
  | node w t1 t2 =>
      obtain ⟨b, h_b⟩ := exists_in_alphabet t1
      obtain ⟨c, h_c⟩ := exists_in_alphabet t2
      cases u with
      | leaf w a =>
          simp [alphabet] at h_alphabet_t_u
          have hba : b ∈ ({a} : Finset α) := by grind
          have hca : c ∈ ({a} : Finset α) := by grind
          grind[mem_inter_empty, consistent]
      | node w t3 t4 => simp [height]

/--
The frequency of symbol `a` in tree `t`, `0` if it's not in the tree.
-/
def freq {α} [DecidableEq α] : HuffmanTree α → α → Nat
  | HuffmanTree.leaf w a, b => if b = a then w else 0
  | HuffmanTree.node _ t1 t2, b => freq t1 b + freq t2 b

/--
The total frequency of symbol `a` in a forest,
defined as the sum of its frequencies from all trees.
-/
def freqF {α} [DecidableEq α] : Forest α → α → Nat
  | [] , _ => 0
  | t :: ts , b => freq t b + freqF ts b

@[simp]
lemma notin_alphabet_imp_freq_0 {α} [DecidableEq α] (a : α) (t : HuffmanTree α) :
  a ∉ alphabet t → freq t a = 0 := by
  induction t <;> simp_all[alphabet,freq]

@[simp]
lemma notin_alphabetF_imp_freqF_0 {α} [DecidableEq α] (a : α) (ts : Forest α) :
  a ∉ alphabetF ts → freqF ts a = 0 := by
  induction ts <;> simp_all[alphabetF, freqF]

@[simp]
lemma freq_0_right {α} [DecidableEq α] (a : α) (t1 t2 : HuffmanTree α)
  (h_disj : alphabet t1 ∩ alphabet t2 = ∅) (h_a_t1 : a ∈ alphabet t1) :
  freq t2 a = 0 := by
  grind[notin_alphabet_imp_freq_0, mem_inter_empty]

@[simp]
lemma freq_0_left {α} [DecidableEq α] (a : α) (t1 t2 : HuffmanTree α)
  (h_disj : alphabet t1 ∩ alphabet t2 = ∅) (h_a_t2 : a ∈ alphabet t2) :
  freq t1 a = 0 := by
  grind[notin_alphabet_imp_freq_0, mem_inter_empty]

/--
If a forest is consistent and has height zero,
then for symbol `a` from the forest alphabet,
the leaf `a` and its frequency is an element of the forest.
-/
lemma heightF_0_imp_Leaf_freqF_in_set {α} [DecidableEq α] (ts : Forest α) (a : α)
  (h_consistent : consistentF ts) (h_height : heightF ts = 0)
  (h_alphabet : a ∈ alphabetF ts) :
  HuffmanTree.leaf (freqF ts a) a ∈ ts := by
  induction ts with
  | nil =>
      simp [alphabetF] at h_alphabet
      contradiction
  | cons t ts ih =>
      cases t <;>
      grind[notin_alphabet_imp_freq_0, notin_alphabetF_imp_freqF_0,
            freq, freqF, alphabet, alphabetF, alphabet_cases,
            consistent, consistentF, height, heightF]

/--
The total weight of a Huffman tree, defined as the sum of frequencies from all leaves.
-/
def weight {α} : HuffmanTree α → Nat
  | HuffmanTree.leaf w _ => w
  | HuffmanTree.node _ t1 t2 => weight t1 + weight t2

/--
For a consistent Huffman tree, the weight is the sum of the
frequencies of all symbols in its alphabet.
-/
@[simp]
lemma weight_eq_Sum_freq {α} [DecidableEq α]
  (t : HuffmanTree α) (h_consistent : consistent t) :
   weight t = (∑a ∈ alphabet t, freq t a) := by
  induction t with
  | leaf w x => simp [weight, alphabet, freq]
  | node w t1 t2 ih1 ih2 =>
      let ⟨hd, h_consistent_t1, h_consistent_t2⟩ := h_consistent
      have h_sum_1 : (∑ a ∈ alphabet t1, freq t2 a) = 0 := by
        apply Finset.sum_eq_zero
        grind[freq, freq_0_right]
      have h_sum_2 : (∑ a ∈ alphabet t2, freq t1 a) = 0 := by
        apply Finset.sum_eq_zero
        grind[freq, freq_0_left]
      aesop(add norm[weight, alphabet, freq,
            Finset.sum_union, Finset.disjoint_iff_inter_eq_empty])

/--
The cost of a Huffman tree, also called the weighted path length.

It is the sum of freq * depth
-/
def cost {α} : HuffmanTree α → Nat
  | HuffmanTree.leaf _ _ => 0
  | HuffmanTree.node _ t1 t2 => weight t1 + cost t1 + weight t2 + cost t2

/--
This theorem proves that for a consistent Huffman tree,
the cost is the sum of frequency multiplied by depth for all symbols.
-/
theorem cost_eq_Sum_freq_mult_depth
  {α} [DecidableEq α] (t : HuffmanTree α) :
  consistent t →
  cost t = (∑ a ∈ alphabet t, freq t a * depth t a) := by
  induction t with
  | leaf w a => simp [cost, alphabet, freq, depth]
  | node w t1 t2 ih1 ih2 =>
      rintro ⟨h_disj, h_consistent_t1, h_consistent_t2⟩
      let t := HuffmanTree.node w t1 t2
      have d1 : ∀ a, a ∈ alphabet t1 → depth t a = depth t1 a + 1 := by
        grind[depth]
      have d2 : ∀ a, a ∈ alphabet t2 → depth t a = depth t2 a + 1 := by
        grind[mem_inter_empty,depth]
      calc
        cost t
            = weight t1 + cost t1 + weight t2 + cost t2 := by simp[t, cost]
        _ = weight t1 + (∑ a ∈ alphabet t1, freq t1 a * depth t1 a)
            + weight t2 + (∑ a ∈ alphabet t2, freq t2 a * depth t2 a) := by
              rw[ih1 h_consistent_t1, ih2 h_consistent_t2]
        _ = ∑ a ∈ alphabet t1, freq t1 a * (depth t1 a + 1)
            + ∑ a ∈ alphabet t2, freq t2 a * (depth t2 a + 1) := by
              simp[weight_eq_Sum_freq, h_consistent_t1, h_consistent_t2,
                Nat.mul_add, Nat.add_comm, Finset.sum_add_distrib]
              linarith
        _ = ∑ a ∈ alphabet t1, freq t a * depth t a
            + ∑ a ∈ alphabet t2, freq t a * depth t a := by
              grind[Finset.sum_congr,freq_0_right,freq_0_left,freq]
        _ = ∑ a ∈ alphabet t1 ∪ alphabet t2, freq t a * depth t a := by
              aesop(add norm[Finset.sum_union, Finset.disjoint_iff_inter_eq_empty])
        _ = ∑ a ∈ alphabet t, freq t a * depth t a := by simp[t, alphabet]

@[simp]
lemma height_0_imp_cost_0 {α} (t : HuffmanTree α) :
  height t = 0 → cost t = 0 := by
  cases t <;> simp [height, cost]

/--
A Huffman tree is `optimum` if the cost of tree is lower than other comparable tree
with the same alphabet.
-/
def optimum {α} [DecidableEq α] (t : HuffmanTree α) : Prop :=
  ∀ u : HuffmanTree α, consistent u →
    alphabet t = alphabet u →
    freq t = freq u →
    cost t ≤ cost u

/--
`minima t a b` means `a` and `b` have the lowest frequency among all
symbols occurring in the tree `t`.
-/
def minima {α} [DecidableEq α]
  (t : HuffmanTree α) (a b : α) : Prop :=
    a ∈ alphabet t ∧
    b ∈ alphabet t ∧
    a ≠ b ∧
    ∀ c ∈ alphabet t,
      c ≠ a →
      c ≠ b →
      freq t c ≥ freq t a ∧
      freq t c ≥ freq t b

/--
If two symbols `a` and `b` have frequencies less than or equal to all other
frequencies in a tree, then they form a `minima` pair.
-/
lemma twice_freq_le_imp_minima {α} [DecidableEq α]
  (t u : HuffmanTree α) (a b : α) (wa wb : ℕ)
  (h1 : ∀ c ∈ alphabet t, wa ≤ freq t c ∧ wb ≤ freq t c)
  (h2 : alphabet u = alphabet t ∪ {b})
  (h3 : a ∈ alphabet u)
  (h4 : a ≠ b)
  (h5 : freq u =
    fun c => if c = a then wa else if c = b then wb else freq t c) :
  minima u a b := by grind[minima, alphabet, freq]


/-!
# Huffman Algorithm Construction

This file contains the algorithm of the Huffman Tree construction.
It defines functions used in the construction of Huffman trees,
such as cached weight, tree union, and insertion of tree into forest,
as well as the condition `sortedByWeight`, which states that a forest
is sorted according to the weights of its trees.
Based on these functions, it formalizes the Huffman algorithm.
The file also includes lemmas that establish basic correctness and
structural properties of these constructions.

## Definitions

- `sortedByWeight ts` : Predicate stating that a list of trees `ts` is sorted by weight.
- `cachedWeight t`    : Computes the weight of tree `t`.
- `uniteTrees t1 t2`  : Combines two Huffman trees into a single tree with summed weight.
- `insortTree t ts`   : Inserts a tree `t` into forest `ts`.
- `huffman ts h`      : Recursively constructs the Huffman tree from a non-empty forest `ts`.
-/

/--
Condition stating that a forest `ts` is sorted by weight.
-/
def sortedByWeight {α} : Forest α → Prop
  | [] => true
  | [_] => true
  | t1 :: t2 :: ts => weight t1 ≤ weight t2 ∧ sortedByWeight (t2 :: ts)

/--
If a forest `(t :: ts)` is sorted by weight, then its tail is also sorted by weight.
-/
@[simp]
lemma sortedByWeight_Cons_imp_sortedByWeight {α}
  (t : HuffmanTree α) (ts : Forest α) :
  sortedByWeight (t :: ts) → sortedByWeight ts := by
  cases ts <;> simp [sortedByWeight]

/--
If a forest `(t :: ts)` is sorted by weight, then every tree
in the tail has weight greater than or equal to the weight of `t`.
`t` has minimal weight among all trees in the forest.
-/
@[simp]
lemma sortedByWeight_Cons_imp_forall_weight_ge {α}
  (t : HuffmanTree α) (ts : Forest α) :
  sortedByWeight (t :: ts) → ∀u ∈ ts, weight u ≥ weight t := by
  induction ts generalizing t <;> grind[sortedByWeight]

/--
The weight that is stored in the node.
-/
def cachedWeight {α} : HuffmanTree α → Nat
  | HuffmanTree.leaf w _ => w
  | HuffmanTree.node w _ _ => w

/--
For trees of height zero, the cached weight is the actual weight.
-/
@[simp]
lemma height_0_imp_cachedWeight_eq_weight {α} (t : HuffmanTree α) :
  height t = 0 → cachedWeight t = weight t := by
  aesop (add norm[weight, cachedWeight, height])

/--
Combine two Huffman trees into a single tree.

The final tree has as children the input trees and sum of their weights as its weight.
-/
def uniteTrees {α} (t1 t2 : HuffmanTree α) : HuffmanTree α :=
  HuffmanTree.node (cachedWeight t1 + cachedWeight t2) t1 t2

/--
The alphabet of a united tree is the union of the alphabets of its input trees.
-/
@[simp]
lemma alphabet_uniteTrees {α : Type} [DecidableEq α] (t1 t2 : HuffmanTree α) :
  alphabet (uniteTrees t1 t2) = alphabet t1 ∪ alphabet t2 := by simp [uniteTrees, alphabet]

/--
Uniting two consistent trees with disjoint alphabets creates a consistent tree.
-/
@[simp]
lemma consistent_uniteTrees {α : Type} [DecidableEq α] (t1 t2 : HuffmanTree α)
  (h_consistent_t1 : consistent t1) (h_consisstent_t2 : consistent t2)
  (h_disj : alphabet t1 ∩ alphabet t2 = ∅) :
  consistent (uniteTrees t1 t2) := by simp_all [uniteTrees, consistent]

@[simp]
lemma freq_uniteTrees {α : Type} [DecidableEq α] (t1 t2 : HuffmanTree α) (a : α) :
  freq (uniteTrees t1 t2) a = freq t1 a + freq t2 a := by simp [uniteTrees, freq]

/--
Insert a Huffman tree into a forest, preserving the ordering by weight.
-/
def insortTree {α} (u : HuffmanTree α) : List (HuffmanTree α) → List (HuffmanTree α)
  | [] => [u]
  | t :: ts =>
      if cachedWeight u ≤ cachedWeight t then
        u :: t :: ts
      else
        t :: insortTree u ts

/--
Inserting a tree into a list `ts` using `insortTree`
increases the length of the list by one.
-/
@[simp]
lemma insortTree_length {α} (u : HuffmanTree α) (ts : List (HuffmanTree α)) :
    (insortTree u ts).length = ts.length + 1 := by
  induction ts <;> aesop (add norm[insortTree])

/--
Inserting a tree into any list `ts` using `insortTree`
produces a non-empty list.
-/
@[simp]
lemma insortTree_ne_nil {α} (u : HuffmanTree α) (ts : List (HuffmanTree α)) :
    insortTree u ts ≠ [] := by grind[insortTree, insortTree_length]

/--
Inserting a tree into a forest joins its alphabet to the forest alphabet.
-/
@[simp]
lemma alphabetF_insortTree {α : Type} [DecidableEq α] (u : HuffmanTree α) (ts : Forest α) :
  alphabetF (insortTree u ts) = alphabet u ∪ alphabetF ts := by
  induction ts <;> aesop(add norm[insortTree, alphabetF, alphabet])

@[simp]
lemma consistentF_insortTree {α : Type} [DecidableEq α] (u : HuffmanTree α) (ts : Forest α) :
  consistentF (insortTree u ts) = consistentF ( u :: ts ):= by
  induction ts <;> grind[consistentF, alphabetF_insortTree, alphabetF, insortTree]

@[simp]
lemma freqF_insortTree {α : Type} [DecidableEq α] (u : HuffmanTree α) (ts : Forest α) :
  freqF (insortTree u ts) = fun a => freq u a + freqF ts a := by
  ext a
  induction ts <;> aesop (add norm[insortTree, freq, freqF, add_left_comm])

@[simp]
lemma heightF_insortTree {α : Type} (u : HuffmanTree α) (ts : Forest α) :
  heightF (insortTree u ts) = max (height u) (heightF ts) := by
  induction ts <;> aesop (add norm[heightF, max_left_comm, height, insortTree])

/--
Inserting a tree into a forest that is sorted by weight preserves sorting.
-/
@[simp]
lemma sortedByWeight_insortTree {α}
  (t : HuffmanTree α) (ts : Forest α)
  (h_sbw : sortedByWeight ts) (h_height_t : height t = 0) (h_height_ts : heightF ts = 0) :
  sortedByWeight (insortTree t ts) := by
  induction ts using sortedByWeight.induct <;>
    grind[heightF, insortTree, height_0_imp_cachedWeight_eq_weight, sortedByWeight]

/--
Construct a Huffman tree from a non-empty forest.

At each step, two trees are combined and inserted into the forest until only a tree is left.
-/
def huffman {α} (xs : Forest α) (h : xs ≠ []) : HuffmanTree α :=
  match xs with
  | [t]      => t
  | t1 :: t2 :: ts =>
      huffman (insortTree (uniteTrees t1 t2) ts) (insortTree_ne_nil _ _)
termination_by xs.length

/--
The alphabet of the Huffman tree constructed from a forest is exactly the alphabet of the forest.
-/
@[simp]
lemma alphabet_huffman {α} [DecidableEq α] (ts : Forest α) (h : ts ≠ []) :
  alphabet (huffman ts h) = alphabetF ts := by
  induction ts, h using huffman.induct with
  | case1 t h1 h2 =>
      simp[alphabetF, huffman, Finset.inter_eq_left]
      exact Finset.inter_eq_left.mp rfl
  | case2 t1 t2 ts h1 h2 ih =>
      simp [huffman, alphabetF, ih, Finset.union_left_comm, Finset.union_comm]

/--
If the input forest is consistent, then the Huffman tree constructed is also consistent.
-/
@[simp]
lemma consistent_huffman {α} [DecidableEq α] (ts : Forest α) (h : ts ≠ []) :
  consistentF ts → consistent (huffman ts h) := by
  induction ts, h using huffman.induct <;>
  simp [consistentF, huffman, alphabetF, Finset.inter_union_distrib_left] at *
  grind[consistent_uniteTrees, consistent, huffman, consistentF]

/--
The frequency of a symbol in the Huffman tree constructed is its total frequency in the forest.
-/
@[simp]
lemma freq_huffman {α} [DecidableEq α] (ts : Forest α) (a : α) (h : ts ≠ []) :
  freq (huffman ts h) a = freqF ts a := by
  induction ts, h using huffman.induct <;>
  grind[freq, freqF, huffman, uniteTrees, freqF_insortTree]


/-!
# Structural properties and operations of Huffman trees

This file formalises structural properties of Huffman trees.
It defines sibling relations, merging sibling nodes, and splitting leaf nodes.
Lemmas accompanying each definition formalise their structural properties.

## Main definitions

- `sibling t a`            : Returns the sibling of symbol `a` in tree `t`.
- `mergeSibling t a`       : Combines a pair of sibling nodes into a single node.
- `splitLeaf t wa a wb b`  : Splits a leaf into two leaves.
-/

/--
Returns the label of the node that is the sibling (left or right) of the symbol `a`

- If `a` is not in the tree or the tree is a leaf, returns `a`.
- If `a` is in a node, returns its sibling in the left or right subtree.
-/
def sibling {α} [DecidableEq α] : HuffmanTree α → α → α
  | HuffmanTree.leaf _ _, a => a
  | HuffmanTree.node _ (HuffmanTree.leaf _ b) (HuffmanTree.leaf _ c), a =>
      if a = b then c else if a = c then b else a
  | HuffmanTree.node _ t1 t2, a =>
      if a ∈ alphabet t1 then sibling t1 a
      else if a ∈ alphabet t2 then sibling t2 a
      else a

@[simp]
lemma notin_alphabet_imp_sibling_id {α} [DecidableEq α] (t : HuffmanTree α) (a : α)
  (h_a : a ∉ alphabet t) : sibling t a = a := by
  cases t with
  | leaf w x => simp [sibling]
  | node w t1 t2 =>
    cases t1 <;> cases t2 <;> aesop (add norm[sibling, alphabet])

@[simp]
lemma height_0_imp_sibling_id {α} [DecidableEq α] (t : HuffmanTree α) (a : α) :
  height t = 0 → sibling t a = a := by
  cases t <;> simp[sibling, height]

@[simp]
lemma height_gt_0_in_alphabet_imp_sibling_left {α} [DecidableEq α]
  (t1 t2 : HuffmanTree α) (a : α) (w : ℕ) :
  height t1 > 0 → a ∈ alphabet t1 → sibling (HuffmanTree.node w t1 t2) a = sibling t1 a := by
  cases t1 <;> aesop (add norm [height, sibling])

@[simp]
lemma height_gt_0_in_alphabet_imp_sibling_right {α} [DecidableEq α]
  (t1 t2 : HuffmanTree α) (a : α) (w : ℕ) :
  height t2 > 0 → a ∈ alphabet t1 → sibling (HuffmanTree.node w t1 t2) a = sibling t1 a := by
  cases t2 <;> aesop (add norm [height, sibling])

@[simp]
lemma height_gt_0_notin_alphabet_imp_sibling_left {α} [DecidableEq α]
  (t1 t2 : HuffmanTree α) (a : α) (w : ℕ) :
  height t1 > 0 → a ∉ alphabet t1 → sibling (HuffmanTree.node w t1 t2) a = sibling t2 a := by
  cases t1 <;> aesop (add norm [height, sibling])

@[simp]
lemma height_gt_0_notin_alphabet_imp_sibling_right {α} [DecidableEq α]
  (t1 t2 : HuffmanTree α) (a : α) (w : ℕ) :
  height t2 > 0 → a ∉ alphabet t1 → sibling (HuffmanTree.node w t1 t2) a = sibling t2 a := by
  cases t2 <;> aesop (add norm [height, sibling])

@[simp]
lemma either_height_gt_0_imp_sibling {α} [DecidableEq α]
  (t1 t2 : HuffmanTree α) (a : α) (w : ℕ) :
  height t1 > 0 ∨ height t2 > 0 →
  sibling (HuffmanTree.node w t1 t2) a =
  (if a ∈ alphabet t1 then sibling t1 a else sibling t2 a) := by
  aesop

@[simp]
lemma in_alphabet_imp_sibling_in_alphabet {α} [DecidableEq α]
  (t : HuffmanTree α) (a : α) :
  a ∈ alphabet t → sibling t a ∈ alphabet t := by
  induction t, a using sibling.induct <;> aesop (add norm [alphabet,sibling])

@[simp]
lemma sibling_ne_imp_sibling_in_alphabet {α} [DecidableEq α]
  (t : HuffmanTree α) (a : α) :
  sibling t a ≠ a → sibling t a ∈ alphabet t := by
  by_cases h_a : a ∈ alphabet t <;> aesop

/--
A custom induction rule for Huffman trees using sibling and consistency.
It is used to simplify proofs.
-/
theorem sibling_induct_consistent {α} [DecidableEq α]
  {P : (t : HuffmanTree α) → α → consistent t → Prop}
  {t : HuffmanTree α} (a : α) (h_consistent : consistent t)
  (leaf : ∀ w b (h_consistent : consistent (HuffmanTree.leaf w b)),
    P (HuffmanTree.leaf w b) a h_consistent)
  (step1 : ∀ w wb b wc c
  (h_consistent : consistent (HuffmanTree.node w (HuffmanTree.leaf wb b) (HuffmanTree.leaf wc c))),
    b ≠ c → P (HuffmanTree.node w (HuffmanTree.leaf wb b) (HuffmanTree.leaf wc c)) a h_consistent)
  (step21 : ∀ w t1 t2 (h_consistent : consistent (HuffmanTree.node w t1 t2))
    (h_consistent_t1 : consistent t1) (h_consistent_t2 : consistent t2),
    alphabet t1 ∩ alphabet t2 = ∅ →
    (height t1 > 0 ∨ height t2 > 0) →
    a ∈ alphabet t1 →
    sibling t1 a ∈ alphabet t1 →
    a ∉ alphabet t2 →
    sibling t1 a ∉ alphabet t2 →
    P t1 a h_consistent_t1 →
    P (HuffmanTree.node w t1 t2) a h_consistent)
  (step22 : ∀ w t1 t2 (h_consistent : consistent (HuffmanTree.node w t1 t2))
    (h_consistent_t1 : consistent t1) (h_consistent_t2 : consistent t2),
    alphabet t1 ∩ alphabet t2 = ∅ →
    (height t1 > 0 ∨ height t2 > 0) →
    a ∉ alphabet t1 →
    sibling t2 a ∉ alphabet t1 →
    a ∈ alphabet t2 →
    sibling t2 a ∈ alphabet t2 →
    P t2 a h_consistent_t2 →
    P (HuffmanTree.node w t1 t2) a h_consistent)
  (step23 : ∀ w t1 t2 (h_consistent : consistent (HuffmanTree.node w t1 t2))
    (h_consistent_t1 : consistent t1) (h_consistent_t2 : consistent t2),
    alphabet t1 ∩ alphabet t2 = ∅ →
    (height t1 > 0 ∨ height t2 > 0) →
    a ∉ alphabet t1 →
    a ∉ alphabet t2 →
    P (HuffmanTree.node w t1 t2) a h_consistent)
  : P t a h_consistent := by
  induction t with
  | leaf w b => exact leaf w b h_consistent
  | node w1 t1 t2 ih1 ih2 =>
      let ⟨h_disj, h_consistent_t1, h_consistent_t2⟩ := h_consistent
      cases t1 <;> cases t2 <;>
      grind[in_alphabet_imp_sibling_in_alphabet,
            alphabet_cases, height, alphabet, consistent]

/--
For a consistent tree, applying `sibling` twice returns the original symbol.
-/
@[simp]
lemma sibling_sibling_id {α} [DecidableEq α]
  (t : HuffmanTree α) (a : α) (h_consistent : consistent t) :
  sibling t (sibling t a) = a := by
  induction a, h_consistent using sibling_induct_consistent <;> aesop (add norm [sibling])

/--
In a consistent tree, if `a` is the sibling of `b`, then `b` is the sibling of `a`.
-/
@[simp]
lemma sibling_reciprocal {α} [DecidableEq α]
  (t : HuffmanTree α) (a b : α) :
  consistent t → sibling t a = b → sibling t b = a := by aesop

lemma depth_height_imp_sibling_ne {α} [DecidableEq α]
  (t : HuffmanTree α) (a : α)
  (h_consistent : consistent t) (h_depth_height : depth t a = height t)
  (h_height : height t > 0) (h_a_t : a ∈ alphabet t) :
  sibling t a ≠ a := by
  induction a, h_consistent using sibling_induct_consistent <;>
  simp[*] <;>
  grind[height, depth, alphabet, depth_le_height, sibling]

/--
Siblings have equal depth in a consistent tree.
-/
@[simp]
lemma depth_sibling {α} [DecidableEq α]
  (t : HuffmanTree α) (a : α) (h_consistent : consistent t) :
  depth t (sibling t a) = depth t a := by
  induction a, h_consistent using sibling_induct_consistent <;>
  aesop (add norm [depth, alphabet, sibling])

/--
Merge a pair of sibling nodes into a single node.
-/
def mergeSibling {α} [DecidableEq α] : HuffmanTree α → α → HuffmanTree α
  | HuffmanTree.leaf wb b, _ => HuffmanTree.leaf wb b
  | HuffmanTree.node w (HuffmanTree.leaf wb b) (HuffmanTree.leaf wc c), a =>
      if a = b ∨ a = c then HuffmanTree.leaf (wb + wc) a
      else HuffmanTree.node w (HuffmanTree.leaf wb b) (HuffmanTree.leaf wc c)
  | HuffmanTree.node w (HuffmanTree.node v va vb) t2, a =>
      HuffmanTree.node w (mergeSibling (HuffmanTree.node v va vb) a) (mergeSibling t2 a)
  | HuffmanTree.node w t1 (HuffmanTree.node v va vb), a =>
      HuffmanTree.node w (mergeSibling t1 a) (mergeSibling (HuffmanTree.node v va vb) a)

@[simp]
lemma notin_alphabet_imp_mergeSibling_id {α} [DecidableEq α]
  (t : HuffmanTree α) (a : α) :
  a ∉ alphabet t → mergeSibling t a = t := by
  induction t,a using mergeSibling.induct <;> grind[alphabet, mergeSibling]

@[simp]
lemma height_gt_0_imp_mergeSibling_left {α} [DecidableEq α]
  (t1 t2 : HuffmanTree α) (a : α) (w : ℕ) :
  height t1 > 0 → mergeSibling (HuffmanTree.node w t1 t2) a =
  HuffmanTree.node w (mergeSibling t1 a) (mergeSibling t2 a) := by
  cases t1 <;> aesop (add norm [mergeSibling, height])

@[simp]
lemma height_gt_0_imp_mergeSibling_right {α} [DecidableEq α]
  (t1 t2 : HuffmanTree α) (a : α) (w : ℕ) :
  height t2 > 0 → mergeSibling (HuffmanTree.node w t1 t2) a =
  HuffmanTree.node w (mergeSibling t1 a) (mergeSibling t2 a) := by
  cases t2 <;> cases t1 <;> aesop (add norm [mergeSibling, height])

@[simp]
lemma either_height_gt_0_imp_mergeSibling {α} [DecidableEq α]
  (t1 t2 : HuffmanTree α) (a : α) (w : ℕ) :
  height t1 > 0 ∨ height t2 > 0 →
  mergeSibling (HuffmanTree.node w t1 t2) a =
  HuffmanTree.node w (mergeSibling t1 a) (mergeSibling t2 a) := by aesop

/--
Merging siblings `a` updates the alphabet by replacing the original sibling with `a`.
-/
@[simp]
lemma alphabet_mergeSibling {α} [DecidableEq α]
  (t : HuffmanTree α) (a : α)
  (h_consistent : consistent t) (h_a : a ∈ alphabet t) :
  alphabet (mergeSibling t a) = (alphabet t \ {sibling t a}) ∪ {a} := by
  induction a, h_consistent using sibling_induct_consistent
  <;> aesop (add norm [alphabet, mergeSibling, sibling])

@[simp]
lemma consistent_mergeSibling {α} [DecidableEq α]
  (t : HuffmanTree α) (a : α) (h_consistent : consistent t) :
  consistent (mergeSibling t a) := by
  induction a, h_consistent using sibling_induct_consistent <;>
  grind[consistent, mergeSibling, alphabet, alphabet_mergeSibling,
        either_height_gt_0_imp_mergeSibling, notin_alphabet_imp_mergeSibling_id]

@[simp]
lemma freq_mergesibling {α} [DecidableEq α]
  (t : HuffmanTree α) (a : α)
  (h_consistent : consistent t) (h_a : a ∈ alphabet t) (h_sib : sibling t a ≠ a) :
  freq (mergeSibling t a) =
  fun c => if c = a then freq t a + freq t (sibling t a)
            else if c = sibling t a then 0
            else freq t c := by
  induction a, h_consistent using sibling_induct_consistent <;>
    grind[freq, alphabet, consistent, mergeSibling, sibling,
          notin_alphabet_imp_freq_0,
          notin_alphabet_imp_mergeSibling_id,
          either_height_gt_0_imp_sibling,
          either_height_gt_0_imp_mergeSibling]

/--
Merging siblings does not change the weight of the tree.
-/
@[simp]
lemma weight_mergeSibling {α} [DecidableEq α]
  (t : HuffmanTree α) (a : α) :
  weight (mergeSibling t a) = weight t := by
  induction t, a using mergeSibling.induct <;> grind[weight, mergeSibling]

/--
The cost of merged tree plus the frequencies of `a` and its
sibling equals the original cost.
-/
@[simp]
lemma cost_mergeSibling {α} [DecidableEq α]
  (t : HuffmanTree α) (a : α)
  (h_consistent : consistent t) (h_sib : sibling t a ≠ a) :
  cost (mergeSibling t a) + freq t a + freq t (sibling t a) = cost t := by
  induction a, h_consistent using sibling_induct_consistent <;>
  grind[mergeSibling, cost, freq, weight, sibling, consistent, alphabet,
        weight_mergeSibling, notin_alphabet_imp_sibling_id,
        notin_alphabet_imp_mergeSibling_id, either_height_gt_0_imp_sibling,
        notin_alphabet_imp_freq_0, either_height_gt_0_imp_mergeSibling]

/--
Split a leaf node into two leaves `a` and `b` with
weights `wa` and `wb`. This undos the merging from mergeSibling.
-/
def splitLeaf {α} [DecidableEq α] : HuffmanTree α → Nat → α → Nat → α → HuffmanTree α
  | HuffmanTree.leaf wc c, wa, a, wb, b =>
      if c = a then HuffmanTree.node wc (HuffmanTree.leaf wa a) (HuffmanTree.leaf wb b)
      else HuffmanTree.leaf wc c
  | HuffmanTree.node w t1 t2, wa, a, wb, b =>
      HuffmanTree.node w (splitLeaf t1 wa a wb b) (splitLeaf t2 wa a wb b)

def splitLeafF {α} [DecidableEq α] : Forest α → Nat → α → Nat → α → Forest α
  | [] , _, _, _, _ => []
  | t :: ts , wa, a, wb, b => splitLeaf t wa a wb b :: splitLeafF ts wa a wb b

@[simp]
lemma notin_alphabet_imp_splitLeaf_id {α} [DecidableEq α]
(t : HuffmanTree α) (wa wb : Nat) (a b : α) :
  a ∉ alphabet t → splitLeaf t wa a wb b = t := by
  induction t <;> grind [alphabet, splitLeaf]

@[simp]
lemma notin_alphabetF_imp_splitLeafF_id {α} [DecidableEq α]
(ts : Forest α) (wa wb : Nat) (a b : α) :
  a ∉ alphabetF ts → splitLeafF ts wa a wb b = ts := by
  induction ts <;> aesop(add norm[alphabetF, splitLeafF, alphabet, splitLeaf])

/--
The alphabet after splitting a leaf into `a` and `b`.
Adds `b` to the alphabet if `a` is in the tree.
-/
@[simp]
lemma alphabet_splitLeaf {α} [DecidableEq α] (t : HuffmanTree α) (wa wb : Nat) (a b : α) :
    alphabet (splitLeaf t wa a wb b) = if a ∈ alphabet t then alphabet t ∪ {b} else alphabet t := by
  induction t <;> grind [splitLeaf, alphabet]

@[simp]
lemma consistent_splitLeaf {α} [DecidableEq α] (t : HuffmanTree α) (wa wb : Nat) (a b : α)
  (h_consistent : consistent t) (h_b : b ∉ alphabet t) : consistent (splitLeaf t wa a wb b) := by
  induction t with
  | leaf w x => grind [splitLeaf,consistent, alphabet]
  | node w t1 t2 ih1 ih2 =>
      grind[mem_inter_empty, alphabet, consistent, splitLeaf, alphabet_splitLeaf]

@[simp]
lemma freq_splitLeaf {α} [DecidableEq α] (t : HuffmanTree α)
  (wa wb : Nat) (a b c : α)
  (h_consistent : consistent t) (h_b : b ∉ alphabet t) :
  freq (splitLeaf t wa a wb b) c =
    if a ∈ alphabet t then
      if c = a then wa else if c = b then wb else freq t c
    else freq t c := by
    induction a, h_consistent using huffmanTree_induct_consistent <;>
      aesop (add norm [freq, alphabet, splitLeaf])

/--
Splitting a leaf preserves weight of the tree.
-/
@[simp]
lemma weight_splitLeaf {α} [DecidableEq α] (t : HuffmanTree α) (wa wb : Nat) (a b : α)
  (h_consistent : consistent t) (h_a : a ∈ alphabet t) (h_freq : freq t a = wa + wb) :
  weight (splitLeaf t wa a wb b) = weight t := by
  induction a, h_consistent using huffmanTree_induct_consistent <;>
    aesop (add norm [weight,splitLeaf,alphabet,freq])

/--
The cost of the tree after splitting a leaf into `a` and `b`
increases the cost of the tree by `wa + wb`.
-/
lemma cost_splitLeaf {α} [DecidableEq α] (t : HuffmanTree α) (wa wb : Nat) (a b : α)
  (h_consistent : consistent t)  (h_alphabet : a ∈ alphabet t) (h_freq : freq t a = wa + wb) :
  cost (splitLeaf t wa a wb b) = cost t + wa + wb := by
  induction a, h_consistent using huffmanTree_induct_consistent <;>
  grind[cost, weight, splitLeaf, freq, alphabet,
          weight_splitLeaf, notin_alphabet_imp_freq_0,
          weight_eq_Sum_freq, notin_alphabet_imp_splitLeaf_id]

@[simp]
lemma cachedWeight_splitLeaf {α : Type} [DecidableEq α]
(t : HuffmanTree α) (a b : α) (wa wb : Nat) :
  cachedWeight (splitLeaf t wa a wb b) = cachedWeight t := by
  cases t <;> grind [splitLeaf, cachedWeight]

@[simp]
lemma splitLeafF_insortTree_when_in_alphabet_left {α : Type} [DecidableEq α]
  (t : HuffmanTree α) (ts : Forest α) (a b : α) (wa wb : Nat)
  (h_a : a ∈ alphabet t) (h_consistent : consistent t)
  (h_a_ts : a ∉ alphabetF ts) (h_freq : freq t a = wa + wb) :
  splitLeafF (insortTree t ts) wa a wb b =
    insortTree (splitLeaf t wa a wb b) ts := by
  induction ts <;> aesop (add norm [splitLeaf, splitLeafF, insortTree,alphabetF,alphabet])

@[simp]
lemma splitLeafF_insortTree_when_in_alphabetF_tail {α : Type} [DecidableEq α]
  (t : HuffmanTree α) (ts : Forest α) (a b : α) (wa wb : Nat)
  (h_a_ts : a ∈ alphabetF ts) (h_consistent : consistentF ts)
  (h_a : a ∉ alphabet t) (h_freq : freqF ts a = wa + wb) :
  splitLeafF (insortTree t ts) wa a wb b =
    insortTree t (splitLeafF ts wa a wb b) := by
  induction ts with
  | nil => aesop (add norm[splitLeafF, insortTree])
  | cons u us ih =>
      simp [consistentF] at h_consistent
      by_cases hau : a ∈ alphabet u
      · have haus : a ∉ alphabetF us := by grind[mem_inter_empty]
        aesop (add norm [splitLeaf, splitLeafF, insortTree])
      · simp [alphabetF, hau] at h_a_ts
        simp [freqF, notin_alphabet_imp_freq_0 a u hau] at h_freq
        aesop (add norm [splitLeaf, splitLeafF, insortTree, freqF])

lemma splitLeafF_nonempty {α : Type} [DecidableEq α]
  {ts : Forest α} {wa wb : Nat} {a b : α} (hne : ts ≠ []) :
  splitLeafF ts wa a wb b ≠ [] := by
  cases ts <;> grind[splitLeafF]


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


/-!
# Lemmas for Huffman Tree Optimality

This file contains key lemmas used to prove the optimality of Huffman trees

## Lemmas
- Lemma `cost_swapFourSyms_le`
If a and b are minima and c and d are at the bottom of the tree,
swapping a and b with c and d does not increase the cost of tree

- Lemma `optimum_splitLeaf`
The tree `splitLeaf t wa a wb b` is optimal if `t` is optimal.

- Lemma `splitLeaf_huffman_commute`
Spliting a leaf node before applying Huffman's algorithm gives the same result as
applying the algorithm first then spliting the leaf
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
        have h_freq2: freq t b ≤ freq t d := (h_freq d hd (Ne.symm h_ad) (Ne.symm h_bd)).2
        have hd2: depth t b ≤ depth t d := by grind[depth_le_height]
        nlinarith
    · by_cases h_bd : b = d
      · have : swapFourSyms t a b c d = swapLeaves t (freq t a) a (freq t c) c := by
          grind[swapFourSyms, swapLeaves_id, swapSyms, consistent_swapLeaves]
        rw [this]
        have hcost := cost_swapLeaves t (freq t a) (freq t c) a c h_consistent h_ac
        simp [ha, hc] at hcost
        have h_freq2: freq t a ≤ freq t c := (h_freq c hc (Ne.symm h_ac) (Ne.symm h_bc)).1
        have hd2: depth t a ≤ depth t c := by grind[depth_le_height]
        nlinarith
      · have := h_freq c hc (Ne.symm h_ac) (Ne.symm h_bc)
        calc
          cost (swapFourSyms t a b c d) ≤ cost (swapSyms t a c) := by
            let t' := swapLeaves t (freq t a) a (freq t c) c
            have h_freq' : freq t' b ≤ freq t' d := by grind[freq_swapLeaves, freq, alphabet]
            aesop(add norm[swapFourSyms])
          _ ≤ cost t := by aesop
  · grind[swapSyms, cost_swapSyms_le, depth_le_height, swapFourSyms, cost_swapLeaves]

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
  · simp[*]
  · have ha_u : a ∈ alphabet u := by
      have ha_t' : a ∈ alphabet t' := by simp [t', ha_t]
      grind
    have hb_u : b ∈ alphabet u := by
      have hb_t' : b ∈ alphabet t' := by simp [t', ha_t]
      grind
    have h_ab : a ≠ b := by grind
    have h_height_u : height u > 0 := by cases u <;> grind[height, alphabet]
    obtain ⟨c, hc_u, hc_depth⟩ := exists_at_height u h_consistent_u
    let d := sibling u c
    have h_dc : d ≠ c := by grind[depth_height_imp_sibling_ne]
    have hd_u : d ∈ alphabet u := by
      simp [d, sibling_ne_imp_sibling_in_alphabet u c h_dc]
    have hd_depth : depth u d = height u := by grind[depth_sibling]
    let u' := swapFourSyms u a b c d
    have h_consistent_u' : consistent u' :=
      consistent_swapFourSyms u a b c d h_consistent_u
    have h_alp_u'_u : alphabet u' = alphabet u :=
      alphabet_swapFourSyms u a b c d ha_u hb_u hc_u hd_u
    have h_freq_u' : freq u' = freq u :=
      freq_swapFourSyms u a b c d h_consistent_u ha_u hb_u hc_u hd_u
    have h_sib_a : sibling u' a = b := by grind[sibling_swapFourSyms_when_4th_is_sibling]
    let v := mergeSibling u' a
    have h_consistent_v : consistent v := by grind[consistent_mergeSibling]
    have h_freq_a : freq t' a = freq u a := congr_fun h_freq_u a
    have h_freq_b : freq t' b = freq u b := congr_fun h_freq_u b
    have h_freq_v : freq v = freq t := by
      ext x
      have ha_u': a ∈ alphabet u' := by simp [h_alp_u'_u, ha_u]
      rw [freq_mergesibling u' a h_consistent_u' ha_u' ?_] <;>
      aesop(add norm[h_freq_u', h_freq_u.symm])
    calc
      cost t' = cost t + wa + wb :=
        cost_splitLeaf t wa wb a b h_consistent ha_t h_freq
      _ ≤ cost v + wa + wb := by
        grind[optimum, consistent_mergeSibling, alphabet_splitLeaf, alphabet_mergeSibling]
      _ = cost u' := by
        have hwafreq : wa = freq u' a := by
          have : wa = freq t' a := by grind[freq_splitLeaf]
          rw [this, h_freq_a, h_freq_u']
        have hwbfreq : wb = freq u' (sibling u' a) := by
          have : wb = freq t' b := by grind[freq_splitLeaf]
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
            · aesop(add norm[freq])
            · aesop(add norm[freq])
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
        grind[consistentF,alphabetF]
      have h_disj2 : alphabet t1 ∩ alphabet t2 = ∅ := by grind[consistentF, alphabetF]
      have h_cases :
        (a ∈ alphabet t1 ∧ a ∉ alphabet t2 ∧ a ∉ alphabetF ts) ∨
        (a ∉ alphabet t1 ∧ a ∈ alphabet t2 ∧ a ∉ alphabetF ts) ∨
        (a ∉ alphabet t1 ∧ a ∉ alphabet t2 ∧ a ∈ alphabetF ts):= by
        grind [alphabetF, mem_inter_empty, consistentF]
      rcases h_cases with h1 | h2 | h3 <;>
      aesop (add norm
          [splitLeafF, insortTree, huffman, splitLeaf,
           alphabet, alphabetF, consistentF, consistent,
           cachedWeight, freq, freqF, uniteTrees])
