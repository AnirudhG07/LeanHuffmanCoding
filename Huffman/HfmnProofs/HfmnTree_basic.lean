import Mathlib.Tactic
import Aesop

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
If `A` and `B` are disjoint (their intersection is empty),
no element can belong to both sets at the same time.
-/
lemma mem_inter_empty {α} [DecidableEq α]
  (A B : Finset α) (a : α) (h : A ∩ B = ∅)
  (h1 : a ∈ A) (h2 : a ∈ B) : False := by
  have : a ∈ A ∩ B := Finset.mem_inter_of_mem h1 h2
  simp [h] at this

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
