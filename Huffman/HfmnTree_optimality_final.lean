/-
  HfmnTree_optimality_final.lean

  Final theorem interface for Huffman optimality, stated in a reduction style
  that matches the induction proof route.

  This file intentionally avoids exchange-specific notions.
-/

import Huffman.HfmnTree_optimality
import Huffman.HfmnTree_optimality_induction

set_option linter.unusedSectionVars false

variable {α : Type} [DecidableEq α] [Inhabited α] [Ord α] [HfmnType α]

instance [Inhabited α] [DecidableEq α] : HfmnType α where
  default := default

namespace HfmnTreeOptimality

/-- Order-insensitive admissibility: same encoded alphabet as Huffman's tree. -/
def Admissible (input : AlphaNumList α) (T : HfmnTree α) : Prop :=
  T.chars.Perm (HfmnTree.tree input).chars

/--
Final global Huffman optimality statement (assumption-free target):
among all admissible trees, Huffman's tree has minimum weighted path length.
-/
def HuffmanOptimalityTheorem (input : AlphaNumList α) : Prop :=
  ∀ T : HfmnTree α,
    Admissible input T →
    weightedPathLength (HfmnTree.tree input) input ≤ weightedPathLength T input

/--
Equivalent least-encoded-data lower-bound form of the final target theorem.
-/
def HuffmanLeastEncodedDataTheorem (input : AlphaNumList α) : Prop :=
  ∀ T : HfmnTree α,
    Admissible input T →
    Huffman.leastEncodedData input ≤ weightedPathLength T input

/--
The two standard final statements are equivalent:
weighted-path-length optimality and least-encoded-data lower bound.
-/
  theorem huffmanOptimalityTheorem_iff_leastEncodedData
    (input : AlphaNumList α) :
    HuffmanOptimalityTheorem input ↔ HuffmanLeastEncodedDataTheorem input := by
  constructor
  · intro hOpt T hAdm
    have hWpl := hOpt T hAdm
    calc
      Huffman.leastEncodedData input
          = weightedPathLength (HfmnTree.tree input) input :=
            leastEncodedData_eq_wpl input
      _ ≤ weightedPathLength T input := hWpl
  · intro hBound T hAdm
    have hLed := hBound T hAdm
    calc
      weightedPathLength (HfmnTree.tree input) input
          = Huffman.leastEncodedData input := (leastEncodedData_eq_wpl input).symm
      _ ≤ weightedPathLength T input := hLed

/-- Admissibility restricted to an abstract reduced class used by induction. -/
def ReducedAdmissible
    (input : AlphaNumList α)
    (ReducedClass : HfmnTree α → Prop)
    (T : HfmnTree α) : Prop :=
  Admissible input T ∧ ReducedClass T

/--
Global reduction step:
every admissible tree can be reduced into the chosen reduced class
without increasing weighted path length.
-/
def ReductionHypothesis
    (input : AlphaNumList α)
    (ReducedClass : HfmnTree α → Prop) : Prop :=
  ∀ T : HfmnTree α,
    Admissible input T →
    ∃ T' : HfmnTree α,
      ReducedAdmissible input ReducedClass T' ∧
      weightedPathLength T' input ≤ weightedPathLength T input

/--
Optimality on the reduced class.
-/
def ReducedClassOptimality
    (input : AlphaNumList α)
    (ReducedClass : HfmnTree α → Prop) : Prop :=
  ∀ T : HfmnTree α,
    ReducedAdmissible input ReducedClass T →
    weightedPathLength (HfmnTree.tree input) input ≤ weightedPathLength T input

/--
Reduction theorem:
if reduced-class optimality and global reduction are proved, then the final
assumption-free target theorem follows.
-/
theorem huffmanOptimality_of_reduction
    (input : AlphaNumList α)
    (ReducedClass : HfmnTree α → Prop)
    (hReducedOptimal : ReducedClassOptimality input ReducedClass)
    (hReduce : ReductionHypothesis input ReducedClass) :
    HuffmanOptimalityTheorem input := by
  intro T hAdm
  rcases hReduce T hAdm with ⟨T', hT', hle⟩
  have hoptT' :
      weightedPathLength (HfmnTree.tree input) input ≤ weightedPathLength T' input :=
    hReducedOptimal T' hT'
  exact le_trans hoptT' hle

/-- Reduction theorem for the least-encoded-data lower-bound form. -/
theorem leastEncodedDataLowerBound_of_reduction
    (input : AlphaNumList α)
    (ReducedClass : HfmnTree α → Prop)
    (hReducedOptimal : ReducedClassOptimality input ReducedClass)
    (hReduce : ReductionHypothesis input ReducedClass) :
    HuffmanLeastEncodedDataTheorem input := by
  intro T hAdm
  have hopt :
      weightedPathLength (HfmnTree.tree input) input ≤ weightedPathLength T input :=
    huffmanOptimality_of_reduction input ReducedClass hReducedOptimal hReduce T hAdm
  calc
    Huffman.leastEncodedData input
        = weightedPathLength (HfmnTree.tree input) input :=
          leastEncodedData_eq_wpl input
    _ ≤ weightedPathLength T input := hopt

/--
If global optimality is already known and Huffman's tree is in the reduced class,
then the reduction hypothesis follows.
-/
theorem reductionHypothesisOfGlobalOptimality
    (input : AlphaNumList α)
    (ReducedClass : HfmnTree α → Prop)
    (hRootReduced : ReducedClass (HfmnTree.tree input))
  (hGlobal :
      ∀ T : HfmnTree α,
        Admissible input T →
        weightedPathLength (HfmnTree.tree input) input ≤ weightedPathLength T input) :
    ReductionHypothesis input ReducedClass := by
  intro T hAdm
  refine ⟨HfmnTree.tree input, ?_⟩
  constructor
  · constructor
    · unfold Admissible
      exact List.Perm.refl _
    · exact hRootReduced
  · exact hGlobal T hAdm

/--
Concrete bridge: the currently defined `DeepestSiblingClass` admits a trivial
identity reduction (`T' = T`), since every tree is already in the class.
-/
theorem reductionHypothesis_deepestSiblingClass
    (input : AlphaNumList α) :
    ReductionHypothesis input HfmnTreeOptimalityInduction.HfmnTree.DeepestSiblingClass := by
  intro T hAdm
  refine ⟨T, ?_⟩
  constructor
  · exact ⟨hAdm, HfmnTreeOptimalityInduction.HfmnTree.deepestSiblingClass_all T⟩
  · exact le_rfl

/--
Immediate corollary: if reduced-class optimality is proved for `DeepestSiblingClass`,
then the final global Huffman optimality theorem follows.
-/
theorem huffmanOptimality_of_deepestSiblingClassOptimality
    (input : AlphaNumList α)
    (hReducedOptimal :
      ReducedClassOptimality input HfmnTreeOptimalityInduction.HfmnTree.DeepestSiblingClass) :
    HuffmanOptimalityTheorem input := by
  exact huffmanOptimality_of_reduction
    input
    HfmnTreeOptimalityInduction.HfmnTree.DeepestSiblingClass
    hReducedOptimal
    (reductionHypothesis_deepestSiblingClass input)

end HfmnTreeOptimality
