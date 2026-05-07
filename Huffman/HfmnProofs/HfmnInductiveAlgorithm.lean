import Huffman.HfmnProofs.HfmnInductiveBasic

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
