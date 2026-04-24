/-
  HfmnTree_optimality_final.lean

  Final optimality interface built on top of the proved exchange machinery in
  `HfmnTree_optimality`.

  Design:
  * State the final global Huffman optimality theorem first.
  * Isolate the remaining global combinatorial step as one hypothesis.
  * Keep theorems mathematically clean and name them generically.
-/

import Huffman.HfmnTree_optimality

set_option linter.unusedSectionVars false

variable {α : Type} [DecidableEq α] [Inhabited α] [Ord α] [HfmnType α]

instance [Inhabited α] [DecidableEq α] : HfmnType α where
  default := default

namespace HfmnTreeOptimality

/-- Order-insensitive admissibility: same encoded alphabet as Huffman's tree. -/
def Admissible (input : AlphaNumList α) (T : HfmnTree α) : Prop :=
  T.chars.Perm (HfmnTree.tree input).chars

/-- Admissibility plus exchange-reachability from the Huffman tree. -/
def ReachableAdmissible (input : AlphaNumList α) (T : HfmnTree α) : Prop :=
  Admissible input T ∧ HfmnTree.reachableFromHuffman input T

/--
Global combinatorial reduction step needed for unconditional optimality:
every admissible tree can be transformed to a reachable admissible tree
without increasing weighted path length.
-/
def RearrangementHypothesis (input : AlphaNumList α) : Prop :=
  ∀ T : HfmnTree α,
    Admissible input T →
    ∃ T' : HfmnTree α,
      ReachableAdmissible input T' ∧
      weightedPathLength T' input ≤ weightedPathLength T input

/--
Final Huffman optimality theorem.

Once `RearrangementHypothesis` is proved, Huffman is globally optimal over all
admissible trees.
-/
theorem huffmanOptimality
    (input : AlphaNumList α)
    (hRearr : RearrangementHypothesis input) :
    ∀ T : HfmnTree α,
      Admissible input T →
      weightedPathLength (HfmnTree.tree input) input ≤ weightedPathLength T input := by
  intro T hAdm
  rcases hRearr T hAdm with ⟨T', hT', hle⟩
  rcases hT' with ⟨_, hReach⟩
  have hoptT' :
      weightedPathLength (HfmnTree.tree input) input ≤ weightedPathLength T' input :=
    HfmnTree.huffman_optimal_reachable input T' hReach
  exact le_trans hoptT' hle

/-- Proven theorem in current development: optimality on reachable admissible trees. -/
theorem huffmanOptimalityOnReachable
    (input : AlphaNumList α) :
    ∀ T : HfmnTree α,
      ReachableAdmissible input T →
      weightedPathLength (HfmnTree.tree input) input ≤ weightedPathLength T input := by
  intro T hAdm
  rcases hAdm with ⟨_, hReach⟩
  exact HfmnTree.huffman_optimal_reachable input T hReach

/-- Lower bound form on the reachable admissible class. -/
theorem leastEncodedDataLowerBoundOnReachable
    (input : AlphaNumList α) :
    ∀ T : HfmnTree α,
      ReachableAdmissible input T →
      Huffman.leastEncodedData input ≤ weightedPathLength T input := by
  intro T hAdm
  have hopt :
      weightedPathLength (HfmnTree.tree input) input ≤ weightedPathLength T input :=
    huffmanOptimalityOnReachable input T hAdm
  calc
    Huffman.leastEncodedData input
        = weightedPathLength (HfmnTree.tree input) input :=
          leastEncodedData_eq_wpl input
    _ ≤ weightedPathLength T input := hopt

/-- Global lower bound form from the final theorem hypothesis. -/
theorem leastEncodedDataLowerBound
    (input : AlphaNumList α)
    (hRearr : RearrangementHypothesis input) :
    ∀ T : HfmnTree α,
      Admissible input T →
      Huffman.leastEncodedData input ≤ weightedPathLength T input := by
  intro T hAdm
  have hopt :
      weightedPathLength (HfmnTree.tree input) input ≤ weightedPathLength T input :=
    huffmanOptimality input hRearr T hAdm
  calc
    Huffman.leastEncodedData input
        = weightedPathLength (HfmnTree.tree input) input :=
          leastEncodedData_eq_wpl input
    _ ≤ weightedPathLength T input := hopt

/--
If global admissible-class optimality is already known, the rearrangement
hypothesis follows immediately by choosing `T' = HfmnTree.tree input`.
-/
theorem rearrangementHypothesisOfGlobalOptimality
    (input : AlphaNumList α)
    (hGlobal :
      ∀ T : HfmnTree α,
        Admissible input T →
        weightedPathLength (HfmnTree.tree input) input ≤ weightedPathLength T input) :
    RearrangementHypothesis input := by
  intro T hAdm
  refine ⟨HfmnTree.tree input, ?_, ?_⟩
  constructor
  · unfold Admissible
    exact List.Perm.refl _
  · exact Relation.ReflTransGen.refl
  · exact hGlobal T hAdm

/--
`RearrangementHypothesis` is equivalent to global admissible-class optimality.

So proving either one gives the other.
-/
theorem rearrangementHypothesis_iff_globalOptimality
    (input : AlphaNumList α) :
    RearrangementHypothesis input ↔
      (∀ T : HfmnTree α,
        Admissible input T →
        weightedPathLength (HfmnTree.tree input) input ≤ weightedPathLength T input) := by
  constructor
  · intro hRearr
    exact huffmanOptimality input hRearr
  · intro hGlobal
    exact rearrangementHypothesisOfGlobalOptimality input hGlobal

/-- Compatibility bridge from the older list-equality admissibility notion. -/
lemma admissibleEqImpliesAdmissible
    (input : AlphaNumList α) (T : HfmnTree α)
    (h : HfmnTree.isAdmissible input T) :
    Admissible input T := by
  unfold HfmnTree.isAdmissible at h
  unfold Admissible
  exact h ▸ List.Perm.refl _

end HfmnTreeOptimality
