/-
  HfmnTree_optimality_induction.lean

  Step 1 for the full Huffman optimality proof:
  introduce a frequency-independent code-tree model and bridge lemmas from the
  existing weighted `HfmnTree` representation.
-/

import Huffman.HfmnTree_optimality

set_option linter.unusedSectionVars false

variable {α : Type} [DecidableEq α] [Inhabited α] [Ord α] [HfmnType α]

namespace HfmnTreeOptimalityInduction

/--
Code invariants needed in the induction proof path:
all vertex codes are unique, and leaf codes are pairwise prefix-free.
-/
def HfmnTree.CodeInvariant (t : HfmnTree α) : Prop :=
  HfmnTree.codesUnique t ∧
  (t.vertices []).Pairwise
    (fun v₁ v₂ => v₁.isLeaf → v₂.isLeaf → checkPrefixfree v₁.code v₂.code)

theorem HfmnTree.codeInvariant_all (t : HfmnTree α) :
    HfmnTree.CodeInvariant t := by
  constructor
  · unfold HfmnTree.codesUnique
    exact HfmnTree.all_codes_unique t []
  · exact HfmnTree.hfmntree_is_prefix_free t []

theorem HfmnTree.codeInvariant_huffmanTree (input : AlphaNumList α) :
    HfmnTree.CodeInvariant (HfmnTree.tree input) := by
  exact HfmnTree.codeInvariant_all (HfmnTree.tree input)

/-- Every Huffman tree has at least one leaf vertex. -/
lemma HfmnTree.exists_mem_leaves (t : HfmnTree α) (c : BoolList) :
    ∃ v, v ∈ t.leaves c := by
  induction t generalizing c with
  | Leaf a w =>
      refine ⟨Vertex.Leaf c, ?_⟩
      simp [HfmnTree.leaves, HfmnTree.vertices, Vertex.isLeaf]
  | Node l r ihl ihr =>
      rcases ihl (c ++ [false]) with ⟨v, hv⟩
      refine ⟨v, ?_⟩
      simp [HfmnTree.leaves, HfmnTree.vertices, Vertex.isLeaf]
      grind

lemma HfmnTree.leaves_nonempty (t : HfmnTree α) (c : BoolList) :
    t.leaves c ≠ [] := by
  rcases HfmnTree.exists_mem_leaves t c with ⟨v, hv⟩
  grind

@[simp]
lemma HfmnTree.mem_leaves_iff
    (t : HfmnTree α) (c : BoolList) (v : Vertex) :
    v ∈ t.leaves c ↔ v ∈ t.vertices c ∧ v.isLeaf = true := by
  simp [HfmnTree.leaves, List.mem_filter]

/--
Every nontrivial node has two distinct leaves, one in each subtree.
-/
theorem HfmnTree.exists_two_distinct_leaves_of_node
    (l r : HfmnTree α) :
    ∃ v₁ v₂,
      v₁ ∈ (HfmnTree.Node l r).leaves [] ∧
      v₂ ∈ (HfmnTree.Node l r).leaves [] ∧
      v₁ ≠ v₂ := by
  rcases HfmnTree.exists_mem_leaves l [false] with ⟨v₁, hv₁L⟩
  rcases HfmnTree.exists_mem_leaves r [true] with ⟨v₂, hv₂R⟩
  have hv₁Pair : v₁ ∈ l.vertices [false] ∧ v₁.isLeaf = true :=
    (HfmnTree.mem_leaves_iff l [false] v₁).1 hv₁L
  have hv₂Pair : v₂ ∈ r.vertices [true] ∧ v₂.isLeaf = true :=
    (HfmnTree.mem_leaves_iff r [true] v₂).1 hv₂R
  have hv₁Node : v₁ ∈ (HfmnTree.Node l r).leaves [] := by
    simp [HfmnTree.leaves, HfmnTree.vertices, Vertex.isLeaf]
    exact Or.inl (by simp_all only [HfmnTree.leaves, Vertex.isLeaf, List.mem_filter, true_and,
      and_true, and_self])
  have hv₂Node : v₂ ∈ (HfmnTree.Node l r).leaves [] := by
    simp [HfmnTree.leaves, HfmnTree.vertices, Vertex.isLeaf]
    exact Or.inr (by simp_all only [HfmnTree.leaves, Vertex.isLeaf, List.mem_filter, true_and,
      and_true, HfmnTree.vertices, List.nil_append, Bool.false_eq_true, not_false_eq_true,
      List.filter_cons_of_neg, List.filter_append, List.mem_append, and_self, true_or])
  have hv₁V : v₁ ∈ l.vertices [false] := (HfmnTree.mem_leaves_iff l [false] v₁).1 hv₁L |>.1
  have hv₂V : v₂ ∈ r.vertices [true] := (HfmnTree.mem_leaves_iff r [true] v₂).1 hv₂R |>.1
  have hneqCode : v₁.code ≠ v₂.code := by
    exact HfmnTree.codes_disjoint_of_nonprefix
      l r [false] [true] (by simp_all) (by simp_all)
      v₁ hv₁V v₂ hv₂V
  grind

/--
If a tree contains at least two characters, then it has at least two distinct
leaf vertices.
-/
theorem HfmnTree.exists_two_distinct_leaves_of_chars_ge_two
    (t : HfmnTree α) (hchars : 2 ≤ t.chars.length) :
    ∃ v₁ v₂,
      v₁ ∈ t.leaves [] ∧
      v₂ ∈ t.leaves [] ∧
      v₁ ≠ v₂ := by
  cases t with
  | Leaf a w =>
      simp [HfmnTree.chars] at hchars
  | Node l r =>
      simpa using HfmnTree.exists_two_distinct_leaves_of_node l r

/--
Existence of a deepest leaf code (maximal code length among leaves).
-/
theorem HfmnTree.exists_deepest_leaf
    (t : HfmnTree α) :
    ∃ v, v ∈ t.leaves [] ∧
      ∀ u, u ∈ t.leaves [] → u.code.length ≤ v.code.length := by
  classical
  let leaves := t.leaves []
  have hne : leaves ≠ [] := HfmnTree.leaves_nonempty t []
  let opt := leaves.argmax (fun v => v.code.length)
  have hopt_ne_none : opt ≠ none := by
    intro hnone
    have hnil : leaves = [] := (List.argmax_eq_none).1 hnone
    exact hne hnil
  rcases hopt : opt with _ | v
  · contradiction
  · refine ⟨v, ?_, ?_⟩
    · have hvopt : v ∈ leaves.argmax (fun w => w.code.length) := by
        simp [opt, hopt]
      exact List.argmax_mem hvopt
    · intro u hu
      have hvopt : v ∈ leaves.argmax (fun w => w.code.length) := by
        simp [opt, hopt]
      exact List.le_of_mem_argmax (f := fun w : Vertex => w.code.length) hu hvopt

lemma HfmnTree.leaf_code_length_pos_of_mem_node_leaves
    (l r : HfmnTree α) {v : Vertex}
    (hv : v ∈ (HfmnTree.Node l r).leaves []) :
    0 < v.code.length := by
  have hvin : v ∈ (HfmnTree.Node l r).vertices [] ∧ v.isLeaf = true :=
    (HfmnTree.mem_leaves_iff (HfmnTree.Node l r) [] v).1 hv
  have hvcases :
      (v ∈ l.vertices [false] ∧ v.isLeaf = true) ∨
      (v ∈ r.vertices [true] ∧ v.isLeaf = true) := by
    rcases hvin with ⟨hmem, hisLeaf⟩
    have hmem' : v = Vertex.Node [] ∨ v ∈ l.vertices [false] ∨ v ∈ r.vertices [true] := by
      simpa [HfmnTree.vertices] using hmem
    rcases hmem' with hroot | hL | hR
    · subst hroot
      simp [Vertex.isLeaf] at hisLeaf
    · exact Or.inl ⟨hL, hisLeaf⟩
    · exact Or.inr ⟨hR, hisLeaf⟩
  rcases hvcases with ⟨hvL, _⟩ | ⟨hvR, _⟩
  · have hlen : v.code.length ≥ [false].length :=
      HfmnTree.vertices_len_geq l [false] v hvL
    simp at hlen
    omega
  · have hlen : v.code.length ≥ [true].length :=
      HfmnTree.vertices_len_geq r [true] v hvR
    simp at hlen
    omega

/--
When there are at least two characters, a deepest leaf has positive code length.
-/
theorem HfmnTree.exists_deepest_leaf_pos_of_chars_ge_two
    (t : HfmnTree α) (hchars : 2 ≤ t.chars.length) :
    ∃ v, v ∈ t.leaves [] ∧
      (∀ u, u ∈ t.leaves [] → u.code.length ≤ v.code.length) ∧
      0 < v.code.length := by
  cases t with
  | Leaf a w =>
      simp [HfmnTree.chars] at hchars
  | Node l r =>
      rcases HfmnTree.exists_deepest_leaf (HfmnTree.Node l r) with ⟨v, hv, hmax⟩
      refine ⟨v, hv, hmax, ?_⟩
      exact HfmnTree.leaf_code_length_pos_of_mem_node_leaves l r hv

/--
If a tree has at least two characters, we can choose a deepest leaf and another
distinct leaf.
-/
theorem HfmnTree.exists_deepest_leaf_with_distinct_partner
    (t : HfmnTree α) (hchars : 2 ≤ t.chars.length) :
    ∃ v w,
      v ∈ t.leaves [] ∧
      w ∈ t.leaves [] ∧
      v ≠ w ∧
      (∀ u, u ∈ t.leaves [] → u.code.length ≤ v.code.length) := by
  rcases HfmnTree.exists_deepest_leaf t with ⟨v, hv, hmax⟩
  rcases HfmnTree.exists_two_distinct_leaves_of_chars_ge_two t hchars with
    ⟨a, b, ha, hb, hab⟩
  grind

lemma BoolList.exists_prefix_bit_of_length_pos
    (code : BoolList) (hpos : 0 < code.length) :
    ∃ p : BoolList, ∃ b : Bool, code = p ++ [b] := by
  have hne : code ≠ [] := by
    exact List.ne_nil_of_length_pos hpos
  refine ⟨code.dropLast, code.getLast hne, ?_⟩
  simpa using (List.dropLast_append_getLast hne).symm

lemma BoolList.exists_prefix_bool_of_length_pos
    (code : BoolList) (hpos : 0 < code.length) :
    ∃ p, code = p ++ [false] ∨ code = p ++ [true] := by
  rcases BoolList.exists_prefix_bit_of_length_pos code hpos with ⟨p, b, hb⟩
  cases b with
  | false =>
      exact ⟨p, Or.inl hb⟩
  | true =>
      exact ⟨p, Or.inr hb⟩

theorem HfmnTree.exists_deepest_leaf_with_code_split
    (t : HfmnTree α) (hchars : 2 ≤ t.chars.length) :
    ∃ v p,
      v ∈ t.leaves [] ∧
      (∀ u, u ∈ t.leaves [] → u.code.length ≤ v.code.length) ∧
      (v.code = p ++ [false] ∨ v.code = p ++ [true]) := by
  rcases HfmnTree.exists_deepest_leaf_pos_of_chars_ge_two t hchars with
    ⟨v, hv, hmax, hpos⟩
  rcases BoolList.exists_prefix_bool_of_length_pos v.code hpos with ⟨p, hp⟩
  exact ⟨v, p, hv, hmax, hp⟩

lemma HfmnTree.leaf_prefix_of_mem_leaves
    (t : HfmnTree α) (c : BoolList) {v : Vertex}
    (hv : v ∈ t.leaves c) :
    c <+: v.code := by
  have hvV : v ∈ t.vertices c := (HfmnTree.mem_leaves_iff t c v).1 hv |>.1
  have hvV' : v ∈ t.vertices (c ++ []) := by
    simpa using hvV
  simpa using HfmnTree.initialCode_prefix_of_code t c [] v hvV'

lemma HfmnTree.leaf_code_length_ge_prefix_len
    (t : HfmnTree α) (c : BoolList) {v : Vertex}
    (hv : v ∈ t.leaves c) :
    c.length ≤ v.code.length := by
  exact List.IsPrefix.length_le (HfmnTree.leaf_prefix_of_mem_leaves t c hv)

lemma HfmnTree.prefixRelSymm :
    Symmetric (fun v₁ v₂ : Vertex =>
      v₁.isLeaf = true → v₂.isLeaf = true → checkPrefixfree v₁.code v₂.code = true) := by
  intro v₁ v₂ h h₂ h₁
  have hpf : checkPrefixfree v₁.code v₂.code = true := h h₁ h₂
  simpa [checkPrefixfree, Bool.and_comm] using hpf

/--
Two distinct leaf vertices have prefix-free codes (in boolean form).
-/
theorem HfmnTree.checkPrefixfree_of_distinct_leaves
    (t : HfmnTree α)
    {v₁ v₂ : Vertex}
    (hv₁ : v₁ ∈ t.leaves [])
    (hv₂ : v₂ ∈ t.leaves [])
    (hneq : v₁ ≠ v₂) :
    checkPrefixfree v₁.code v₂.code = true := by
  have hpairV :
      (t.vertices []).Pairwise
        (fun a b =>
          a.isLeaf = true → b.isLeaf = true → checkPrefixfree a.code b.code = true) :=
    HfmnTree.hfmntree_is_prefix_free t []
  have hpairL :
      (t.leaves []).Pairwise
        (fun a b =>
          a.isLeaf = true → b.isLeaf = true → checkPrefixfree a.code b.code = true) := by
    simpa [HfmnTree.leaves] using (hpairV.filter (fun v => v.isLeaf))
  have hv₁f : v₁ ∈ (t.vertices []).filter (fun v => v.isLeaf) := by
    simpa [HfmnTree.leaves] using hv₁
  have hv₂f : v₂ ∈ (t.vertices []).filter (fun v => v.isLeaf) := by
    simpa [HfmnTree.leaves] using hv₂
  have hv₁Leaf : v₁.isLeaf = true := (List.mem_filter.1 hv₁f).2
  have hv₂Leaf : v₂.isLeaf = true := (List.mem_filter.1 hv₂f).2
  have hrel :
      v₁.isLeaf = true → v₂.isLeaf = true → checkPrefixfree v₁.code v₂.code = true :=
    (List.Pairwise.forall HfmnTree.prefixRelSymm hpairL hv₁ hv₂ hneq)
  exact hrel hv₁Leaf hv₂Leaf

/-- Distinct leaves are not prefixes of each other (propositional form). -/
theorem HfmnTree.not_prefix_of_distinct_leaves
    (t : HfmnTree α)
    {v₁ v₂ : Vertex}
    (hv₁ : v₁ ∈ t.leaves [])
    (hv₂ : v₂ ∈ t.leaves [])
    (hneq : v₁ ≠ v₂) :
    ¬ v₁.code <+: v₂.code ∧ ¬ v₂.code <+: v₁.code := by
  have hpf : checkPrefixfree v₁.code v₂.code = true :=
    HfmnTree.checkPrefixfree_of_distinct_leaves t hv₁ hv₂ hneq
  simpa [checkPrefixfree, List.isPrefixOf_iff_prefix] using hpf

lemma HfmnTree.leaf_code_length_pos_of_chars_ge_two
    (t : HfmnTree α) (hchars : 2 ≤ t.chars.length)
    {v : Vertex} (hv : v ∈ t.leaves []) :
    0 < v.code.length := by
  cases t with
  | Leaf a w =>
      simp [HfmnTree.chars] at hchars
  | Node l r =>
      exact HfmnTree.leaf_code_length_pos_of_mem_node_leaves l r hv

theorem HfmnTree.exists_deepest_leaf_with_prefixfree_partner
    (t : HfmnTree α) (hchars : 2 ≤ t.chars.length) :
    ∃ v w,
      v ∈ t.leaves [] ∧
      w ∈ t.leaves [] ∧
      v ≠ w ∧
      (∀ u, u ∈ t.leaves [] → u.code.length ≤ v.code.length) ∧
      (¬ v.code <+: w.code ∧ ¬ w.code <+: v.code) := by
  rcases HfmnTree.exists_deepest_leaf_with_distinct_partner t hchars with
    ⟨v, w, hv, hw, hneq, hmax⟩
  refine ⟨v, w, hv, hw, hneq, hmax, ?_⟩
  exact HfmnTree.not_prefix_of_distinct_leaves t hv hw hneq

theorem HfmnTree.exists_deepest_leaf_split_with_prefixfree_partner
    (t : HfmnTree α) (hchars : 2 ≤ t.chars.length) :
    ∃ v w p,
      v ∈ t.leaves [] ∧
      w ∈ t.leaves [] ∧
      v ≠ w ∧
      (∀ u, u ∈ t.leaves [] → u.code.length ≤ v.code.length) ∧
      (¬ v.code <+: w.code ∧ ¬ w.code <+: v.code) ∧
      (v.code = p ++ [false] ∨ v.code = p ++ [true]) := by
  rcases HfmnTree.exists_deepest_leaf_with_prefixfree_partner t hchars with
    ⟨v, w, hv, hw, hneq, hmax, hpf⟩
  have hpos : 0 < v.code.length :=
    HfmnTree.leaf_code_length_pos_of_chars_ge_two t hchars hv
  rcases BoolList.exists_prefix_bool_of_length_pos v.code hpos with ⟨p, hsplit⟩
  exact ⟨v, w, p, hv, hw, hneq, hmax, hpf, hsplit⟩

/--
With at least two characters, we can pick two distinct leaves whose codes are
mutually non-prefix.
-/
theorem HfmnTree.exists_distinct_prefixfree_leaves_of_chars_ge_two
    (t : HfmnTree α) (hchars : 2 ≤ t.chars.length) :
    ∃ v₁ v₂,
      v₁ ∈ t.leaves [] ∧
      v₂ ∈ t.leaves [] ∧
      v₁ ≠ v₂ ∧
      (¬ v₁.code <+: v₂.code ∧ ¬ v₂.code <+: v₁.code) := by
  rcases HfmnTree.exists_two_distinct_leaves_of_chars_ge_two t hchars with
    ⟨v₁, v₂, hv₁, hv₂, hneq⟩
  refine ⟨v₁, v₂, hv₁, hv₂, hneq, ?_⟩
  exact HfmnTree.not_prefix_of_distinct_leaves t hv₁ hv₂ hneq

lemma BoolList.not_prefix_true_false_ext (c s : BoolList) :
    ¬ c ++ [true] <+: c ++ [false] ++ s := by
  intro h
  have h2 : c ++ [false] <+: c ++ [false] ++ s := by
    exact List.prefix_append _ _
  have htf : c ++ [true] <+: c ++ [false] := by
    have hlen : (c ++ [true]).length ≤ (c ++ [false]).length := by
      simp_all only [List.append_assoc, List.cons_append, List.nil_append,
        List.prefix_append_right_inj, List.cons_prefix_cons, Bool.true_eq_false, List.nil_prefix,
        and_true]
    exact lenpref_of_pref_isprefix (c ++ [true]) (c ++ [false]) (c ++ [false] ++ s) h h2 hlen
  exact code_tf_not_prefix c htf

lemma BoolList.not_prefix_false_true_ext (c s : BoolList) :
    ¬ c ++ [false] <+: c ++ [true] ++ s := by
  intro h
  have h2 : c ++ [true] <+: c ++ [true] ++ s := by
    exact List.prefix_append _ _
  have htf : c ++ [false] <+: c ++ [true] := by
    have hlen : (c ++ [false]).length ≤ (c ++ [true]).length := by
      simp_all only [List.append_assoc, List.cons_append, List.nil_append,
        List.prefix_append_right_inj, List.cons_prefix_cons, Bool.false_eq_true, List.nil_prefix,
        and_true]
    exact lenpref_of_pref_isprefix (c ++ [false]) (c ++ [true]) (c ++ [true] ++ s) h h2 hlen
  exact code_ft_not_prefix c htf

lemma HfmnTree.leaf_mem_left_of_code_false
    (l r : HfmnTree α) (c p : BoolList) (b : Bool)
    (hv : Vertex.Leaf (c ++ [false] ++ p ++ [b]) ∈ (HfmnTree.Node l r).vertices c) :
    Vertex.Leaf ((c ++ [false]) ++ p ++ [b]) ∈ l.vertices (c ++ [false]) := by
  have hmem :
      Vertex.Leaf (c ++ [false] ++ p ++ [b]) ∈ l.vertices (c ++ [false]) ∨
      Vertex.Leaf (c ++ [false] ++ p ++ [b]) ∈ r.vertices (c ++ [true]) := by
    simp_all only [HfmnTree.vertices, List.append_assoc, List.cons_append, List.nil_append,
      List.mem_cons, reduceCtorEq, List.mem_append, false_or]
  rcases hmem with hL | hR
  · simpa [List.append_assoc] using hL
  · exfalso
    have hR' :
        Vertex.Leaf (c ++ [false] ++ p ++ [b]) ∈ r.vertices ((c ++ [true]) ++ []) := by
      simpa [List.append_assoc] using hR
    have hpref : (c ++ [true]) <+: (c ++ [false] ++ p ++ [b]) :=
      HfmnTree.initialCode_prefix_of_code r (c ++ [true]) [] _ hR'
    have hpref' : (c ++ [true]) <+: (c ++ [false] ++ (p ++ [b])) := by
      simp_all only [HfmnTree.vertices, List.append_assoc, List.cons_append, List.nil_append,
        List.mem_cons, reduceCtorEq, List.mem_append, false_or, List.append_nil,
        List.prefix_append_right_inj, List.cons_prefix_cons, Bool.true_eq_false, List.nil_prefix,
        and_true]
    exact BoolList.not_prefix_true_false_ext c (p ++ [b]) hpref'

lemma HfmnTree.leaf_mem_right_of_code_true
    (l r : HfmnTree α) (c p : BoolList) (b : Bool)
    (hv : Vertex.Leaf (c ++ [true] ++ p ++ [b]) ∈ (HfmnTree.Node l r).vertices c) :
    Vertex.Leaf ((c ++ [true]) ++ p ++ [b]) ∈ r.vertices (c ++ [true]) := by
  have hmem :
      Vertex.Leaf (c ++ [true] ++ p ++ [b]) ∈ l.vertices (c ++ [false]) ∨
      Vertex.Leaf (c ++ [true] ++ p ++ [b]) ∈ r.vertices (c ++ [true]) := by
    simpa [HfmnTree.vertices, List.append_assoc] using hv
  rcases hmem with hL | hR
  · exfalso
    have hL' :
        Vertex.Leaf (c ++ [true] ++ p ++ [b]) ∈ l.vertices ((c ++ [false]) ++ []) := by
      simpa [List.append_assoc] using hL
    have hpref : (c ++ [false]) <+: (c ++ [true] ++ p ++ [b]) :=
      HfmnTree.initialCode_prefix_of_code l (c ++ [false]) [] _ hL'
    have hpref' : (c ++ [false]) <+: (c ++ [true] ++ (p ++ [b])) := by
      simp_all
    exact BoolList.not_prefix_false_true_ext c (p ++ [b]) hpref'
  · simpa [List.append_assoc] using hR

lemma HfmnTree.node_mem_left_of_code_false
    (l r : HfmnTree α) (c p : BoolList)
    (hv : Vertex.Node (c ++ [false] ++ p) ∈ (HfmnTree.Node l r).vertices c) :
    Vertex.Node ((c ++ [false]) ++ p) ∈ l.vertices (c ++ [false]) := by
  have hmem0 :
      Vertex.Node (c ++ [false] ++ p) = Vertex.Node c ∨
      Vertex.Node (c ++ [false] ++ p) ∈ l.vertices (c ++ [false]) ∨
      Vertex.Node (c ++ [false] ++ p) ∈ r.vertices (c ++ [true]) := by
    simp_all only [HfmnTree.vertices, List.append_assoc, List.cons_append, List.nil_append,
      List.mem_cons, List.mem_append]
  have hmem :
      Vertex.Node (c ++ [false] ++ p) ∈ l.vertices (c ++ [false]) ∨
      Vertex.Node (c ++ [false] ++ p) ∈ r.vertices (c ++ [true]) := by
    rcases hmem0 with hroot | hsub
    · exfalso
      injection hroot with hcode
      have hlen := congrArg List.length hcode
      simp at hlen
    · exact hsub
  rcases hmem with hL | hR
  · simpa [List.append_assoc] using hL
  · exfalso
    have hR' :
        Vertex.Node (c ++ [false] ++ p) ∈ r.vertices ((c ++ [true]) ++ []) := by
      simpa [List.append_assoc] using hR
    have hpref : (c ++ [true]) <+: (c ++ [false] ++ p) :=
      HfmnTree.initialCode_prefix_of_code r (c ++ [true]) [] _ hR'
    have hpref' : (c ++ [true]) <+: (c ++ [false] ++ p) := by
      simp_all only [HfmnTree.vertices, List.append_assoc, List.cons_append, List.nil_append,
        List.mem_cons, Vertex.Node.injEq, List.append_right_eq_self, reduceCtorEq, List.mem_append,
        false_or, or_true, List.append_nil, List.prefix_append_right_inj, List.cons_prefix_cons,
        Bool.true_eq_false, List.nil_prefix, and_true]
    exact BoolList.not_prefix_true_false_ext c p hpref'

lemma HfmnTree.node_mem_right_of_code_true
    (l r : HfmnTree α) (c p : BoolList)
    (hv : Vertex.Node (c ++ [true] ++ p) ∈ (HfmnTree.Node l r).vertices c) :
    Vertex.Node ((c ++ [true]) ++ p) ∈ r.vertices (c ++ [true]) := by
  have hmem0 :
      Vertex.Node (c ++ [true] ++ p) = Vertex.Node c ∨
      Vertex.Node (c ++ [true] ++ p) ∈ l.vertices (c ++ [false]) ∨
      Vertex.Node (c ++ [true] ++ p) ∈ r.vertices (c ++ [true]) := by
    simpa [HfmnTree.vertices, List.append_assoc] using hv
  have hmem :
      Vertex.Node (c ++ [true] ++ p) ∈ l.vertices (c ++ [false]) ∨
      Vertex.Node (c ++ [true] ++ p) ∈ r.vertices (c ++ [true]) := by
    rcases hmem0 with hroot | hsub
    · exfalso
      injection hroot with hcode
      have hlen := congrArg List.length hcode
      simp at hlen
    · exact hsub
  rcases hmem with hL | hR
  · exfalso
    have hL' :
        Vertex.Node (c ++ [true] ++ p) ∈ l.vertices ((c ++ [false]) ++ []) := by
      simpa [List.append_assoc] using hL
    have hpref : (c ++ [false]) <+: (c ++ [true] ++ p) :=
      HfmnTree.initialCode_prefix_of_code l (c ++ [false]) [] _ hL'
    have hpref' : (c ++ [false]) <+: (c ++ [true] ++ p) := by
      simp_all only [HfmnTree.vertices, List.append_assoc, List.cons_append, List.nil_append,
        List.mem_cons, Vertex.Node.injEq, List.append_right_eq_self, reduceCtorEq, List.mem_append,
        false_or, or_true, List.append_nil, List.prefix_append_right_inj, List.cons_prefix_cons,
        List.nil_prefix, and_true]
    exact BoolList.not_prefix_false_true_ext c p hpref'
  · simpa [List.append_assoc] using hR

lemma HfmnTree.node_prefix_mem_of_leaf_mem_vertices
    (t : HfmnTree α) (c p : BoolList) (b : Bool)
    (hv : Vertex.Leaf (c ++ p ++ [b]) ∈ t.vertices c) :
    Vertex.Node (c ++ p) ∈ t.vertices c := by
  induction p generalizing t c with
  | nil =>
      cases t with
      | Leaf a w =>
          simp [HfmnTree.vertices] at hv
      | Node l r =>
          simp_all
  | cons d ps ih =>
      cases t with
      | Leaf a w =>
          simp [HfmnTree.vertices] at hv
      | Node l r =>
          cases d with
          | false =>
              have hvL :
                  Vertex.Leaf ((c ++ [false]) ++ ps ++ [b]) ∈ l.vertices (c ++ [false]) :=
                HfmnTree.leaf_mem_left_of_code_false l r c ps b (by simp_all only [List.append_assoc,
                  HfmnTree.vertices, List.cons_append, List.mem_cons, reduceCtorEq, List.mem_append,
                  false_or, List.nil_append, or_true])
              grind
          | true =>
              have hvR :
                  Vertex.Leaf ((c ++ [true]) ++ ps ++ [b]) ∈ r.vertices (c ++ [true]) :=
                HfmnTree.leaf_mem_right_of_code_true l r c ps b (by simp_all only [List.append_assoc,
                  HfmnTree.vertices, List.cons_append, List.mem_cons, reduceCtorEq, List.mem_append,
                  false_or, List.nil_append, or_true])
              grind

lemma HfmnTree.exists_leaf_extension_of_node_prefix_branch
    (t : HfmnTree α) (c p : BoolList) (b : Bool)
    (hnode : Vertex.Node (c ++ p) ∈ t.vertices c) :
    ∃ s, Vertex.Leaf (c ++ p ++ [b] ++ s) ∈ t.leaves c := by
  induction p generalizing t c with
  | nil =>
      cases t with
      | Leaf a w =>
          simp [HfmnTree.vertices] at hnode
      | Node l r =>
          cases b with
          | false =>
              rcases HfmnTree.exists_mem_leaves l (c ++ [false]) with ⟨v, hv⟩
              rcases (HfmnTree.mem_leaves_iff l (c ++ [false]) v).1 hv with ⟨hvV, hvLeaf⟩
              cases v with
              | Node q =>
                  simp [Vertex.isLeaf] at hvLeaf
              | Leaf q =>
                  have hprefix : (c ++ [false]) <+: q :=
                    HfmnTree.leaf_prefix_of_mem_leaves l (c ++ [false]) hv
                  rcases hprefix with ⟨s, hs⟩
                  refine ⟨s, ?_⟩
                  have hvNode : Vertex.Leaf q ∈ (HfmnTree.Node l r).leaves c := by
                    simp [HfmnTree.leaves, HfmnTree.vertices, hvV]
                  simpa [hs, List.append_assoc] using hvNode
          | true =>
              rcases HfmnTree.exists_mem_leaves r (c ++ [true]) with ⟨v, hv⟩
              rcases (HfmnTree.mem_leaves_iff r (c ++ [true]) v).1 hv with ⟨hvV, hvLeaf⟩
              cases v with
              | Node q =>
                  simp [Vertex.isLeaf] at hvLeaf
              | Leaf q =>
                  have hprefix : (c ++ [true]) <+: q :=
                    HfmnTree.leaf_prefix_of_mem_leaves r (c ++ [true]) hv
                  rcases hprefix with ⟨s, hs⟩
                  refine ⟨s, ?_⟩
                  have hvNode : Vertex.Leaf q ∈ (HfmnTree.Node l r).leaves c := by
                    simp [HfmnTree.leaves, HfmnTree.vertices, hvV]
                  simpa [hs, List.append_assoc] using hvNode
  | cons d ps ih =>
      cases t with
      | Leaf a w =>
          simp [HfmnTree.vertices] at hnode
      | Node l r =>
          cases d with
          | false =>
              have hnodeL :
                  Vertex.Node ((c ++ [false]) ++ ps) ∈ l.vertices (c ++ [false]) :=
                HfmnTree.node_mem_left_of_code_false l r c ps (by
                  simpa [List.append_assoc] using hnode)
              rcases ih (t := l) (c := c ++ [false]) hnodeL with ⟨s, hs⟩
              refine ⟨s, ?_⟩
              have hsV :
                  Vertex.Leaf (((c ++ [false]) ++ ps) ++ [b] ++ s) ∈ l.vertices (c ++ [false]) :=
                (HfmnTree.mem_leaves_iff l (c ++ [false]) _).1 hs |>.1
              have hsV' :
                  Vertex.Leaf (c ++ false :: (ps ++ b :: s)) ∈ l.vertices (c ++ [false]) := by
                simpa [List.append_assoc] using hsV
              have hsNodeV :
                  Vertex.Leaf (c ++ false :: (ps ++ b :: s)) ∈ (HfmnTree.Node l r).vertices c := by
                simp [HfmnTree.vertices, hsV']
              have hsNode :
                  Vertex.Leaf (c ++ false :: (ps ++ b :: s)) ∈ (HfmnTree.Node l r).leaves c := by
                exact (HfmnTree.mem_leaves_iff (HfmnTree.Node l r) c _).2
                  ⟨hsNodeV, by simp [Vertex.isLeaf]⟩
              simpa [List.append_assoc] using hsNode
          | true =>
              have hnodeR :
                  Vertex.Node ((c ++ [true]) ++ ps) ∈ r.vertices (c ++ [true]) :=
                HfmnTree.node_mem_right_of_code_true l r c ps (by
                  simpa [List.append_assoc] using hnode)
              rcases ih (t := r) (c := c ++ [true]) hnodeR with ⟨s, hs⟩
              refine ⟨s, ?_⟩
              have hsV :
                  Vertex.Leaf (((c ++ [true]) ++ ps) ++ [b] ++ s) ∈ r.vertices (c ++ [true]) :=
                (HfmnTree.mem_leaves_iff r (c ++ [true]) _).1 hs |>.1
              have hsV' :
                  Vertex.Leaf (c ++ true :: (ps ++ b :: s)) ∈ r.vertices (c ++ [true]) := by
                simpa [List.append_assoc] using hsV
              have hsNodeV :
                  Vertex.Leaf (c ++ true :: (ps ++ b :: s)) ∈ (HfmnTree.Node l r).vertices c := by
                simp [HfmnTree.vertices, hsV']
              have hsNode :
                  Vertex.Leaf (c ++ true :: (ps ++ b :: s)) ∈ (HfmnTree.Node l r).leaves c := by
                exact (HfmnTree.mem_leaves_iff (HfmnTree.Node l r) c _).2
                  ⟨hsNodeV, by simp [Vertex.isLeaf]⟩
              simpa [List.append_assoc] using hsNode

lemma BoolList.suffix_nil_of_length_le
    (p s : BoolList) (b₁ b₂ : Bool)
    (h : (p ++ [b₁] ++ s).length ≤ (p ++ [b₂]).length) :
    s = [] := by
  have hlen : p.length + 1 + s.length ≤ p.length + 1 := by
    simpa [List.length_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
  have hs0 : s.length = 0 := by omega
  cases s with
  | nil => rfl
  | cons x xs =>
      simp at hs0

/--
There exists a sibling leaf pair whose depth is maximal among all leaves.
-/
theorem HfmnTree.exists_deepest_sibling_leaf_pair_of_chars_ge_two
    (t : HfmnTree α) (hchars : 2 ≤ t.chars.length) :
    ∃ p,
      Vertex.Leaf (p ++ [false]) ∈ t.leaves [] ∧
      Vertex.Leaf (p ++ [true]) ∈ t.leaves [] ∧
      (∀ u, u ∈ t.leaves [] → u.code.length ≤ (p ++ [false]).length) := by
  rcases HfmnTree.exists_deepest_leaf_with_code_split t hchars with
    ⟨v, p, hv, hmax, hsplit⟩
  have hvLeaf : v.isLeaf = true := (HfmnTree.mem_leaves_iff t [] v).1 hv |>.2
  cases v with
  | Node q =>
      simp [Vertex.isLeaf] at hvLeaf
  | Leaf q =>
      rcases hsplit with hqFalse | hqTrue
      · have hqFalse' : q = p ++ [false] := by
          simpa [Vertex.code] using hqFalse
        have hleft : Vertex.Leaf (p ++ [false]) ∈ t.leaves [] := by
          simpa [hqFalse'] using hv
        have hleftV : Vertex.Leaf (p ++ [false]) ∈ t.vertices [] :=
          (HfmnTree.mem_leaves_iff t [] (Vertex.Leaf (p ++ [false]))).1 hleft |>.1
        have hnode : Vertex.Node p ∈ t.vertices [] :=
          HfmnTree.node_prefix_mem_of_leaf_mem_vertices t [] p false hleftV
        rcases HfmnTree.exists_leaf_extension_of_node_prefix_branch t [] p true hnode with
          ⟨s, hsExt⟩
        have hsLen : (p ++ [true] ++ s).length ≤ (p ++ [false]).length := by
          have hmaxExt : (p ++ [true] ++ s).length ≤ q.length := by
            simpa [Vertex.code, List.append_assoc] using
              (hmax (Vertex.Leaf (p ++ [true] ++ s)) hsExt)
          simpa [hqFalse'] using hmaxExt
        have hsNil : s = [] :=
          BoolList.suffix_nil_of_length_le p s true false hsLen
        have hright : Vertex.Leaf (p ++ [true]) ∈ t.leaves [] := by
          simpa [hsNil, List.append_assoc] using hsExt
        refine ⟨p, hleft, hright, ?_⟩
        intro u hu
        have huMax := hmax u hu
        simpa [hqFalse', Vertex.code, List.length_append, Nat.add_assoc, Nat.add_left_comm,
          Nat.add_comm] using huMax
      · have hqTrue' : q = p ++ [true] := by
          simpa [Vertex.code] using hqTrue
        have hright : Vertex.Leaf (p ++ [true]) ∈ t.leaves [] := by
          simpa [hqTrue'] using hv
        have hrightV : Vertex.Leaf (p ++ [true]) ∈ t.vertices [] :=
          (HfmnTree.mem_leaves_iff t [] (Vertex.Leaf (p ++ [true]))).1 hright |>.1
        have hnode : Vertex.Node p ∈ t.vertices [] :=
          HfmnTree.node_prefix_mem_of_leaf_mem_vertices t [] p true hrightV
        rcases HfmnTree.exists_leaf_extension_of_node_prefix_branch t [] p false hnode with
          ⟨s, hsExt⟩
        have hsLen : (p ++ [false] ++ s).length ≤ (p ++ [true]).length := by
          have hmaxExt : (p ++ [false] ++ s).length ≤ q.length := by
            simpa [Vertex.code, List.append_assoc] using
              (hmax (Vertex.Leaf (p ++ [false] ++ s)) hsExt)
          simpa [hqTrue'] using hmaxExt
        have hsNil : s = [] :=
          BoolList.suffix_nil_of_length_le p s false true hsLen
        have hleft : Vertex.Leaf (p ++ [false]) ∈ t.leaves [] := by
          simpa [hsNil, List.append_assoc] using hsExt
        refine ⟨p, hleft, hright, ?_⟩
        intro u hu
        have huMax := hmax u hu
        have huMax' : u.code.length ≤ (p ++ [true]).length := by
          simpa [hqTrue', Vertex.code, List.length_append, Nat.add_assoc, Nat.add_left_comm,
            Nat.add_comm] using huMax
        simpa [List.length_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using huMax'

/--
Generalized sibling-leaf witness under an initial prefix `c`.
-/
theorem HfmnTree.exists_sibling_leaves_with_prefix
    (t : HfmnTree α) (c : BoolList) (hnode : ∃ l r, t = HfmnTree.Node l r) :
    ∃ p,
      Vertex.Leaf (c ++ p ++ [false]) ∈ t.vertices c ∧
      Vertex.Leaf (c ++ p ++ [true]) ∈ t.vertices c := by
  induction t generalizing c with
  | Leaf a w =>
      rcases hnode with ⟨l, r, hEq⟩
      cases hEq
  | Node l r ihl ihr =>
      cases l with
      | Leaf la lw =>
          cases r with
          | Leaf ra rw =>
              refine ⟨[], ?_, ?_⟩
              · simp [HfmnTree.vertices]
              · simp [HfmnTree.vertices]
          | Node rl rr =>
              have hrNode : ∃ l' r', (HfmnTree.Node rl rr) = HfmnTree.Node l' r' := ⟨rl, rr, rfl⟩
              rcases ihr (c := c ++ [true]) hrNode with ⟨p, hp0, hp1⟩
              refine ⟨[true] ++ p, ?_, ?_⟩
              · simpa [HfmnTree.vertices, List.append_assoc] using hp0
              · simpa [HfmnTree.vertices, List.append_assoc] using hp1
      | Node ll lr =>
          have hlNode : ∃ l' r', (HfmnTree.Node ll lr) = HfmnTree.Node l' r' := ⟨ll, lr, rfl⟩
          rcases ihl (c := c ++ [false]) hlNode with ⟨p, hp0, hp1⟩
          grind

/--
Every non-leaf tree has a sibling leaf pair (`p++[false]`, `p++[true]`) in
its vertex list.
-/
theorem HfmnTree.exists_sibling_leaves
    (t : HfmnTree α) (hnode : ∃ l r, t = HfmnTree.Node l r) :
    ∃ p,
      Vertex.Leaf (p ++ [false]) ∈ t.vertices [] ∧
      Vertex.Leaf (p ++ [true]) ∈ t.vertices [] := by
  simpa using HfmnTree.exists_sibling_leaves_with_prefix t [] hnode

lemma HfmnTree.exists_node_of_chars_ge_two
    (t : HfmnTree α) (hchars : 2 ≤ t.chars.length) :
    ∃ l r, t = HfmnTree.Node l r := by
  cases t with
  | Leaf a w =>
      simp [HfmnTree.chars] at hchars
  | Node l r =>
      exact ⟨l, r, rfl⟩

theorem HfmnTree.exists_sibling_leaf_pair
    (t : HfmnTree α) (hnode : ∃ l r, t = HfmnTree.Node l r) :
    ∃ p,
      Vertex.Leaf (p ++ [false]) ∈ t.leaves [] ∧
      Vertex.Leaf (p ++ [true]) ∈ t.leaves [] := by
  rcases HfmnTree.exists_sibling_leaves t hnode with ⟨p, hfalse, htrue⟩
  refine ⟨p, ?_, ?_⟩
  · exact (HfmnTree.mem_leaves_iff t [] (Vertex.Leaf (p ++ [false]))).2
      ⟨hfalse, by simp [Vertex.isLeaf]⟩
  · exact (HfmnTree.mem_leaves_iff t [] (Vertex.Leaf (p ++ [true]))).2
      ⟨htrue, by simp [Vertex.isLeaf]⟩

theorem HfmnTree.exists_sibling_leaf_pair_of_chars_ge_two
    (t : HfmnTree α) (hchars : 2 ≤ t.chars.length) :
    ∃ p,
      Vertex.Leaf (p ++ [false]) ∈ t.leaves [] ∧
      Vertex.Leaf (p ++ [true]) ∈ t.leaves [] := by
  rcases HfmnTree.exists_node_of_chars_ge_two t hchars with ⟨l, r, hnode⟩
  exact HfmnTree.exists_sibling_leaf_pair t ⟨l, r, hnode⟩

lemma sibling_leaf_vertices_distinct (p : BoolList) :
    Vertex.Leaf (p ++ [false]) ≠ Vertex.Leaf (p ++ [true]) := by
  intro h
  injection h with hcodes
  simp at hcodes

lemma sibling_leaf_code_lengths_eq (p : BoolList) :
    (Vertex.Leaf (p ++ [false])).code.length =
    (Vertex.Leaf (p ++ [true])).code.length := by
  have hlen : (p ++ [true]).length = (p ++ [false]).length := List.eq_suff_eq_len p
  exact hlen.symm

lemma sibling_leaf_code_length_pos (p : BoolList) :
    0 < (Vertex.Leaf (p ++ [false])).code.length ∧
      0 < (Vertex.Leaf (p ++ [true])).code.length := by
  constructor <;> simp [Vertex.code]

theorem HfmnTree.exists_sibling_leaf_pair_with_properties_of_chars_ge_two
    (t : HfmnTree α) (hchars : 2 ≤ t.chars.length) :
    ∃ p,
      Vertex.Leaf (p ++ [false]) ∈ t.leaves [] ∧
      Vertex.Leaf (p ++ [true]) ∈ t.leaves [] ∧
      Vertex.Leaf (p ++ [false]) ≠ Vertex.Leaf (p ++ [true]) ∧
      (¬ (Vertex.Leaf (p ++ [false])).code <+: (Vertex.Leaf (p ++ [true])).code ∧
        ¬ (Vertex.Leaf (p ++ [true])).code <+: (Vertex.Leaf (p ++ [false])).code) ∧
      (Vertex.Leaf (p ++ [false])).code.length =
        (Vertex.Leaf (p ++ [true])).code.length ∧
      0 < (Vertex.Leaf (p ++ [false])).code.length := by
  rcases HfmnTree.exists_sibling_leaf_pair_of_chars_ge_two t hchars with ⟨p, hfalse, htrue⟩
  have hneq :
      Vertex.Leaf (p ++ [false]) ≠ Vertex.Leaf (p ++ [true]) :=
    sibling_leaf_vertices_distinct p
  have hpf :
      ¬ (Vertex.Leaf (p ++ [false])).code <+: (Vertex.Leaf (p ++ [true])).code ∧
      ¬ (Vertex.Leaf (p ++ [true])).code <+: (Vertex.Leaf (p ++ [false])).code :=
    HfmnTree.not_prefix_of_distinct_leaves t hfalse htrue hneq
  have hlen :
      (Vertex.Leaf (p ++ [false])).code.length =
      (Vertex.Leaf (p ++ [true])).code.length :=
    sibling_leaf_code_lengths_eq p
  grind

theorem HfmnTree.exists_deepest_sibling_leaf_pair_with_properties_of_chars_ge_two
    (t : HfmnTree α) (hchars : 2 ≤ t.chars.length) :
    ∃ p,
      Vertex.Leaf (p ++ [false]) ∈ t.leaves [] ∧
      Vertex.Leaf (p ++ [true]) ∈ t.leaves [] ∧
      Vertex.Leaf (p ++ [false]) ≠ Vertex.Leaf (p ++ [true]) ∧
      (¬ (Vertex.Leaf (p ++ [false])).code <+: (Vertex.Leaf (p ++ [true])).code ∧
        ¬ (Vertex.Leaf (p ++ [true])).code <+: (Vertex.Leaf (p ++ [false])).code) ∧
      (Vertex.Leaf (p ++ [false])).code.length =
        (Vertex.Leaf (p ++ [true])).code.length ∧
      0 < (Vertex.Leaf (p ++ [false])).code.length ∧
      (∀ u, u ∈ t.leaves [] →
        u.code.length ≤ (Vertex.Leaf (p ++ [false])).code.length) := by
  rcases HfmnTree.exists_deepest_sibling_leaf_pair_of_chars_ge_two t hchars with
    ⟨p, hfalse, htrue, hmax⟩
  have hneq :
      Vertex.Leaf (p ++ [false]) ≠ Vertex.Leaf (p ++ [true]) :=
    sibling_leaf_vertices_distinct p
  have hpf :
      ¬ (Vertex.Leaf (p ++ [false])).code <+: (Vertex.Leaf (p ++ [true])).code ∧
      ¬ (Vertex.Leaf (p ++ [true])).code <+: (Vertex.Leaf (p ++ [false])).code :=
    HfmnTree.not_prefix_of_distinct_leaves t hfalse htrue hneq
  have hlen :
      (Vertex.Leaf (p ++ [false])).code.length =
      (Vertex.Leaf (p ++ [true])).code.length :=
    sibling_leaf_code_lengths_eq p
  have hpos : 0 < (Vertex.Leaf (p ++ [false])).code.length :=
    (sibling_leaf_code_length_pos p).1
  exact ⟨p, hfalse, htrue, hneq, hpf, hlen, hpos, hmax⟩

/-- Code-tree shape with labels only (no stored frequencies). -/
inductive CodeTree (α : Type) where
  | leaf (a : α)
  | node (l r : CodeTree α)
deriving Inhabited, Repr

@[simp]
def CodeTree.chars : CodeTree α → List α
  | .leaf a => [a]
  | .node l r => l.chars ++ r.chars

@[simp]
def CodeTree.charInTree (t : CodeTree α) (a : α) : Bool :=
  t.chars.contains a

/-- Depth of `a` in a code-tree (`0` for missing labels, as in `HfmnTree.depth`). -/
@[simp]
def CodeTree.depth : CodeTree α → α → Nat
  | .leaf _, _ => 0
  | .node l r, a =>
      if l.charInTree a then 1 + l.depth a
      else 1 + r.depth a

/-- Weighted path length of a code-tree under an external frequency table. -/
@[simp]
def CodeTree.weightedPathLength (t : CodeTree α) (input : AlphaNumList α) : Nat :=
  input.foldl (fun acc (a, f) => acc + t.depth a * f) 0

/-- Forget leaf weights from an `HfmnTree`, preserving shape and labels. -/
@[simp]
def CodeTree.ofHfmnTree : HfmnTree α → CodeTree α
  | .Leaf a _ => .leaf a
  | .Node l r => .node (ofHfmnTree l) (ofHfmnTree r)

@[simp]
lemma CodeTree.chars_ofHfmnTree (t : HfmnTree α) :
    (CodeTree.ofHfmnTree t).chars = t.chars := by
  induction t with
  | Leaf a w => simp [CodeTree.ofHfmnTree, CodeTree.chars, HfmnTree.chars]
  | Node l r ihl ihr =>
      simp [CodeTree.ofHfmnTree, CodeTree.chars, HfmnTree.chars, ihl, ihr]

@[simp]
lemma CodeTree.charInTree_ofHfmnTree (t : HfmnTree α) (a : α) :
    (CodeTree.ofHfmnTree t).charInTree a = t.charInTree a := by
  simp [CodeTree.charInTree, HfmnTree.charInTree, CodeTree.chars_ofHfmnTree]

@[simp]
lemma CodeTree.depth_ofHfmnTree (t : HfmnTree α) (a : α) :
    (CodeTree.ofHfmnTree t).depth a = t.depth a := by
  induction t with
  | Leaf x w =>
      simp [CodeTree.depth, HfmnTree.depth, CodeTree.ofHfmnTree]
  | Node l r ihl ihr =>
      simp [CodeTree.depth, HfmnTree.depth, CodeTree.ofHfmnTree, ihl, ihr]

/-- Bridge lemma: both models compute the same weighted path length. -/
theorem CodeTree.weightedPathLength_ofHfmnTree
    (t : HfmnTree α) (input : AlphaNumList α) :
    CodeTree.weightedPathLength (CodeTree.ofHfmnTree t) input =
    _root_.weightedPathLength t input := by
  unfold CodeTree.weightedPathLength _root_.weightedPathLength
  apply List.foldl_congr_mem
  grind [CodeTree.depth_ofHfmnTree]

/-- Huffman objective can be read equally in the frequency-independent model. -/
theorem CodeTree.huffmanObjective_eq_leastEncodedData
    (input : AlphaNumList α) :
    CodeTree.weightedPathLength (CodeTree.ofHfmnTree (HfmnTree.tree input)) input =
    Huffman.leastEncodedData input := by
  calc
    CodeTree.weightedPathLength (CodeTree.ofHfmnTree (HfmnTree.tree input)) input
        = _root_.weightedPathLength (HfmnTree.tree input) input :=
          CodeTree.weightedPathLength_ofHfmnTree (HfmnTree.tree input) input
    _ = Huffman.leastEncodedData input :=
          (leastEncodedData_eq_wpl input).symm

-- ─────────────────────────────────────────────────────────────────────────────
-- Step 2: Merge/split frequency decomposition
-- ─────────────────────────────────────────────────────────────────────────────

/-- Helper input used after contracting two symbols into one merged symbol. -/
@[simp]
def mergedInput (z : α) (f₁ f₂ : Nat) (rest : AlphaNumList α) : AlphaNumList α :=
  (z, f₁ + f₂) :: rest

/-- Helper input used before contraction (two explicit symbols). -/
@[simp]
def splitInput (c₁ c₂ : α) (f₁ f₂ : Nat) (rest : AlphaNumList α) : AlphaNumList α :=
  (c₁, f₁) :: (c₂, f₂) :: rest

@[simp]
lemma CodeTree.weightedPathLength_cons
    (t : CodeTree α) (a : α) (f : Nat) (rest : AlphaNumList α) :
    CodeTree.weightedPathLength t ((a, f) :: rest) =
      t.depth a * f + CodeTree.weightedPathLength t rest := by
  unfold CodeTree.weightedPathLength
  have hfold :
      List.foldl (fun acc x => acc + t.depth x.1 * x.2) (t.depth a * f) rest =
      t.depth a * f + List.foldl (fun acc x => acc + t.depth x.1 * x.2) 0 rest := by
    simpa using
      (List.foldl_add_assoc
        (f := fun x : α × Nat => t.depth x.1 * x.2)
        (xs := rest)
        (a := t.depth a * f)
        (b := 0))
  simp [List.foldl_cons, hfold]

@[simp]
lemma CodeTree.weightedPathLength_congr_depth
    (t₁ t₂ : CodeTree α) (input : AlphaNumList α)
    (h : ∀ a f, (a, f) ∈ input → t₁.depth a = t₂.depth a) :
    CodeTree.weightedPathLength t₁ input = CodeTree.weightedPathLength t₂ input := by
  unfold CodeTree.weightedPathLength
  apply List.foldl_congr_mem
  grind

/--
Cost decomposition for a merge/split step.

If `c₁` and `c₂` are one level deeper in `tSplit` than merged symbol `z` in
`tMerge`, and all remaining symbols keep the same depth, then:

`WPL(split) = WPL(merged) + (f₁ + f₂)`.
-/
theorem CodeTree.weightedPathLength_split_eq_merged_plus_sum
    (tSplit tMerge : CodeTree α)
    (c₁ c₂ z : α) (f₁ f₂ : Nat) (rest : AlphaNumList α)
    (h₁ : tSplit.depth c₁ = tMerge.depth z + 1)
    (h₂ : tSplit.depth c₂ = tMerge.depth z + 1)
    (hrest : ∀ a f, (a, f) ∈ rest → tSplit.depth a = tMerge.depth a) :
    CodeTree.weightedPathLength tSplit (splitInput c₁ c₂ f₁ f₂ rest) =
      CodeTree.weightedPathLength tMerge (mergedInput z f₁ f₂ rest) + (f₁ + f₂) := by
  have hrestEq :
      CodeTree.weightedPathLength tSplit rest =
      CodeTree.weightedPathLength tMerge rest := by
    exact CodeTree.weightedPathLength_congr_depth tSplit tMerge rest hrest
  calc
    CodeTree.weightedPathLength tSplit (splitInput c₁ c₂ f₁ f₂ rest)
        = tSplit.depth c₁ * f₁ +
            (tSplit.depth c₂ * f₂ + CodeTree.weightedPathLength tSplit rest) := by
            rw [splitInput, CodeTree.weightedPathLength_cons, CodeTree.weightedPathLength_cons]
    _ = (tMerge.depth z + 1) * f₁ +
          ((tMerge.depth z + 1) * f₂ + CodeTree.weightedPathLength tMerge rest) := by
          rw [h₁, h₂, hrestEq]
    _ = (tMerge.depth z * (f₁ + f₂) + CodeTree.weightedPathLength tMerge rest) + (f₁ + f₂) := by
          nlinarith
    _ = CodeTree.weightedPathLength tMerge (mergedInput z f₁ f₂ rest) + (f₁ + f₂) := by
          rw [mergedInput, CodeTree.weightedPathLength_cons]

/--
Inequality form of the merge/split decomposition:
the merged objective is no larger than the split objective.
-/
theorem CodeTree.weightedPathLength_merged_le_split
    (tSplit tMerge : CodeTree α)
    (c₁ c₂ z : α) (f₁ f₂ : Nat) (rest : AlphaNumList α)
    (h₁ : tSplit.depth c₁ = tMerge.depth z + 1)
    (h₂ : tSplit.depth c₂ = tMerge.depth z + 1)
    (hrest : ∀ a f, (a, f) ∈ rest → tSplit.depth a = tMerge.depth a) :
    CodeTree.weightedPathLength tMerge (mergedInput z f₁ f₂ rest) ≤
      CodeTree.weightedPathLength tSplit (splitInput c₁ c₂ f₁ f₂ rest) := by
  have hEq :
      CodeTree.weightedPathLength tSplit (splitInput c₁ c₂ f₁ f₂ rest) =
        CodeTree.weightedPathLength tMerge (mergedInput z f₁ f₂ rest) + (f₁ + f₂) :=
    CodeTree.weightedPathLength_split_eq_merged_plus_sum
      tSplit tMerge c₁ c₂ z f₁ f₂ rest h₁ h₂ hrest
  calc
    CodeTree.weightedPathLength tMerge (mergedInput z f₁ f₂ rest)
        ≤ CodeTree.weightedPathLength tMerge (mergedInput z f₁ f₂ rest) + (f₁ + f₂) :=
          Nat.le_add_right _ _
    _ = CodeTree.weightedPathLength tSplit (splitInput c₁ c₂ f₁ f₂ rest) := by
          exact hEq.symm

-- ─────────────────────────────────────────────────────────────────────────────
-- Step 3: Induction transfer skeleton (one merge step)
-- ─────────────────────────────────────────────────────────────────────────────

/--
Abstract induction-transfer theorem for one Huffman merge step.

If:
1) the split and merged Huffman candidates differ by the exact additive
   constant `(f₁ + f₂)`,
2) the merged candidate is optimal on its admissible class,
3) every split-admissible candidate contracts to a merged-admissible candidate
   with the same additive relation,

then the split candidate is optimal on the split admissible class.
-/
theorem optimalityTransferOfMergeStep
    (huffSplit huffMerge : CodeTree α)
    (c₁ c₂ z : α) (f₁ f₂ : Nat) (rest : AlphaNumList α)
    (SplitAdm MergeAdm : CodeTree α → Prop)
    (hHuffDecomp :
      CodeTree.weightedPathLength huffSplit (splitInput c₁ c₂ f₁ f₂ rest) =
        CodeTree.weightedPathLength huffMerge (mergedInput z f₁ f₂ rest) + (f₁ + f₂))
    (hMergeOptimal :
      ∀ Tm : CodeTree α,
        MergeAdm Tm →
        CodeTree.weightedPathLength huffMerge (mergedInput z f₁ f₂ rest) ≤
          CodeTree.weightedPathLength Tm (mergedInput z f₁ f₂ rest))
    (hContract :
      ∀ Ts : CodeTree α,
        SplitAdm Ts →
        ∃ Tm : CodeTree α,
          MergeAdm Tm ∧
          CodeTree.weightedPathLength Ts (splitInput c₁ c₂ f₁ f₂ rest) =
            CodeTree.weightedPathLength Tm (mergedInput z f₁ f₂ rest) + (f₁ + f₂)) :
    ∀ Ts : CodeTree α,
      SplitAdm Ts →
      CodeTree.weightedPathLength huffSplit (splitInput c₁ c₂ f₁ f₂ rest) ≤
        CodeTree.weightedPathLength Ts (splitInput c₁ c₂ f₁ f₂ rest) := by
  intro Ts hTs
  rcases hContract Ts hTs with ⟨Tm, hTm, hTsDecomp⟩
  have hoptMerged :
      CodeTree.weightedPathLength huffMerge (mergedInput z f₁ f₂ rest) ≤
      CodeTree.weightedPathLength Tm (mergedInput z f₁ f₂ rest) :=
    hMergeOptimal Tm hTm
  calc
    CodeTree.weightedPathLength huffSplit (splitInput c₁ c₂ f₁ f₂ rest)
        = CodeTree.weightedPathLength huffMerge (mergedInput z f₁ f₂ rest) + (f₁ + f₂) :=
          hHuffDecomp
    _ ≤ CodeTree.weightedPathLength Tm (mergedInput z f₁ f₂ rest) + (f₁ + f₂) :=
          Nat.add_le_add_right hoptMerged (f₁ + f₂)
    _ = CodeTree.weightedPathLength Ts (splitInput c₁ c₂ f₁ f₂ rest) := by
          exact hTsDecomp.symm

end HfmnTreeOptimalityInduction
