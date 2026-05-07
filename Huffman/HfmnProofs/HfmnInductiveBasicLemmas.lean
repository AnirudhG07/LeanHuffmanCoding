import Mathlib.Tactic

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
