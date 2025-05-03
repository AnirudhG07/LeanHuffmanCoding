import Huffman.HuffmanTree
set_option linter.unusedSectionVars false

variable {α : Type} [DecidableEq α] [Inhabited α] [Ord α] [HfmnType α]

instance [Inhabited α] [DecidableEq α] : HfmnType α where
  default := default

/-
The Vertex is a shorthand for Nodes or Leaf of the Tree. They only contain the code of the vertex.
Why it is made? 
* To generalise properties to any vertex in statement than have to write for both Leaf and Node.
-/
inductive Vertex where
  | Node (code : BoolList)
  | Leaf (code : BoolList)
deriving Inhabited, Repr, BEq

def Vertex.code : Vertex → BoolList
  | Node c => c
  | Leaf c => c

-- #eval (Vertex.Leaf [false, true]).code
-- #eval (Vertex.Node [false, true]).code

@[simp]
lemma Vertex_code_eq (c: BoolList): (Vertex.Node c).code = c := by
  exact rfl

/-
The vertices of a Huffman tree are the nodes and leaves of the tree. The function returns Leaf/Node with their corresponding codes.
-/
@[simp]
def HfmnTree.vertices : HfmnTree α → BoolList → List Vertex
  | .Leaf _ _, code => [Vertex.Leaf code]
  | .Node l r, code =>
    let leftVertices := vertices l (code ++ [false])
    let rightVertices := vertices r (code ++ [true])
    Vertex.Node code :: (leftVertices ++ rightVertices)

-- #eval HfmnTree.vertices (HfmnTree.tree eg₁) []

/-
* lemma: The vertices of a Huffman tree are non-empty.
-/
lemma HfmnTree.vertices_nonempty (t : HfmnTree α) (code : BoolList) :
  t.vertices code ≠ [] := by
  induction t generalizing code with
  | Leaf _ _ =>
    simp [vertices]
  | Node _ _ _ _ =>
    simp [vertices]

@[simp]
theorem HfmnTree.vertices_len_finite (t : HfmnTree α) (c : BoolList) :
  ∃ n : ℕ, (t.vertices c).length < n := by
  induction t with
  | Leaf _ _ =>
    -- A single leaf has exactly one vertex, so pick n = 1 + 1 = 2
    use 2
    simp [vertices]

  | Node l r ihl ihr =>
    simp [vertices]
    exact exists_gt ((l.vertices (c ++ [false])).length + (r.vertices (c ++ [true])).length + 1)

/-
* Lemma: If a vertex is in the vertices of initial code as (given_code ++ suffix), then the given_code is a prefix of the vertex code.
-/
@[simp]
lemma HfmnTree.initialCode_in_suffix_inits (t : HfmnTree α) (given_code suffix : BoolList) :
  ∀ v ∈ t.vertices (given_code ++ suffix), given_code ∈ List.inits v.code := by
  intro v hv
  simp only [List.mem_inits]
  cases t with
  | Leaf c w =>
    simp [vertices] at hv
    cases hv with
    | refl =>
      simp only [Vertex.code, List.inits, List.prefix_rfl, List.prefix_append]
  | Node l r =>
    have ihl := initialCode_in_suffix_inits l given_code (suffix ++ [false])
    have ihr := initialCode_in_suffix_inits r given_code (suffix ++ [true])
    simp [vertices] at hv
    cases hv with
    | inl h₁ =>
      rw [h₁]
      simp [Vertex.code]
    | inr h₃  =>
      cases h₃ with
      | inl h₁ =>
        have h' :=  ihl v h₁
        simp at h'
        exact h'
      | inr h₂ =>
        have h' :=  ihr v h₂
        simp at h'
        exact h'

/-
* Lemma: If a vertex is in the vertices of initial code as (given_code ++ suffix), then the given_code is a prefix of the vertex code.
-/
@[simp]
lemma HfmnTree.initialCode_prefix_of_code (t : HfmnTree α) (given_code suffix : BoolList) :
  ∀ v ∈ t.vertices (given_code ++ suffix), given_code <+: v.code := by
  have h := HfmnTree.initialCode_in_suffix_inits t given_code suffix
  simp_all

/-
* Theorem: The length of the code of a vertex is greater than or equal to the length of the initial code.
This is true by construction of the tree.
-/
@[simp]
theorem HfmnTree.vertices_len_geq (t : HfmnTree α) (code : BoolList) :
  ∀ v ∈ t.vertices code, v.code.length ≥ code.length := by
  intro v hv
  induction t with
  -- Leaf: the only vertex has code = `code`
  | Leaf _ _ =>
    simp [vertices] at hv
    cases hv with
    | refl =>
      simp [Vertex.code, ge_iff_le, le_refl]

  | Node l r ihl ihr =>
    simp [vertices] at hv
    cases hv with
    | inl hl =>
      simp_all

    | inr h =>
      -- it lives in one of the two subtrees, with extended prefix
      cases h with
      -- left subtree: prefix = `code ++ [false]`
      | inl hl =>
        apply List.IsPrefix.length_le
        exact initialCode_prefix_of_code l code [false] v hl 

      -- right subtree: prefix = `code ++ [true]`
      | inr hr =>
        apply List.IsPrefix.length_le
        exact initialCode_prefix_of_code r code [true] v hr

/-
* Theorem: The initial code of `vertices` of Huffman tree is a prefix of all the vertex code of the tree.
-/
theorem HfmnTree.initialCodeIsPrefix (t : HfmnTree α) (inicode : BoolList) :
  ∀ v ∈ t.vertices inicode, inicode.isPrefixOf (Vertex.code v) := by
  intro v hv
  simp only [List.isPrefixOf_iff_prefix]
  induction t with
  | Leaf c w =>
    simp [vertices] at hv
    cases hv with
    | refl => 
      simp only [Vertex.code, List.prefix_rfl]

  | Node l r =>
    simp [vertices] at hv
    rename_i ihl ihr
    cases hv with
    | inl hl =>
        apply (List.mem_inits inicode v.code).mp
        rw [hl]
        simp only [Vertex.code, List.mem_inits, List.prefix_rfl]
      
    | inr hr =>
        apply (List.mem_inits inicode v.code).mp
        cases hr with
        | inl h₁ =>
          exact HfmnTree.initialCode_in_suffix_inits _ _ _ v h₁
        | inr h₂ =>
          exact HfmnTree.initialCode_in_suffix_inits _ _ _ v h₂

/-
* Lemma: If two codes are prefixes of a code, and one has lesser length, then that is prefix of the other.
-/
@[simp]
lemma lenpref_of_pref_isprefix (c₁ c₂ : BoolList) (v : BoolList) :
  c₁ <+: v → c₂ <+: v → c₁.length ≤ c₂.length → c₁ <+: c₂  := by
  exact fun a a_1 a_2 ↦ List.prefix_of_prefix_length_le a a_1 a_2

/-
* Theorem: Given two trees with their respective initial codes which are prefix free of each other, then the codes of vertices in the trees are disjoint.
-/
theorem HfmnTree.codes_disjoint_of_nonprefix 
  (t₁ t₂ : HfmnTree α) (c₁ c₂ : BoolList)
  (h₁ : ¬ c₁ <+: c₂) (h₂ : ¬ c₂ <+: c₁) :
  ∀ v₁ ∈ t₁.vertices c₁, ∀ v₂ ∈ t₂.vertices c₂, Vertex.code v₁ ≠ Vertex.code v₂ := by
  intro v₁ hv₁ v₂ hv₂ heq
  -- the initial codes themselves must be unequal
  have hnc : c₁ ≠ c₂ := by
    intro eq; apply h₁;
    simp [eq]

  -- each code of v in tree t has its prefix c
  have p₁ := HfmnTree.initialCodeIsPrefix t₁ c₁ v₁ hv₁
  have p₂ := HfmnTree.initialCodeIsPrefix t₂ c₂ v₂ hv₂

  -- if the codes are equal, then the prefixes must be equal
  have hne₁ : c₁.isPrefixOf v₂.code := by
    simp only [List.isPrefixOf_iff_prefix]
    rw [← heq]
    exact List.isPrefixOf_iff_prefix.mp p₁

  if hl: c₁.length ≤ c₂.length then
    have h': c₁ <+: c₂ := by
      simp at p₁ p₂ hne₁
      exact lenpref_of_pref_isprefix c₁ c₂ v₂.code hne₁ p₂ hl
    contradiction 
  else
    have hl': c₂.length ≤ c₁.length := by
      exact Nat.le_of_not_ge hl
    have h': c₂ <+: c₁ := by
      simp at p₁ p₂ hne₁
      exact lenpref_of_pref_isprefix c₂ c₁ v₂.code p₂ hne₁ hl'
      
    contradiction

/-
* Lemma: For any boolean list c, c ++ [false] is not a prefix of c ++ [true].
-/
@[simp]
lemma code_ft_not_prefix (c : BoolList) : ¬ c ++ [false] <+: c ++ [true] := by
  intro h
  have h₁ : (c ++ [false]).length = (c ++ [true]).length := by
    simp only [List.length_append, List.length_cons, List.length_nil, zero_add]
  have h₂ : c ++ [true] = c ++ [false] := by
    exact Eq.symm (List.IsPrefix.eq_of_length h h₁)
  have h₃ : c ++ [false] ≠ c ++ [true] := by
    simp only [ne_eq, List.append_cancel_left_eq, List.cons.injEq, Bool.false_eq_true, and_true,
      not_false_eq_true]
  simp at h₂

@[simp]
lemma code_tf_not_prefix (c : BoolList) : ¬ c ++ [true] <+: c ++ [false] := by
  have h: ¬ c ++ [false] <+: c ++ [true] := by
    exact code_ft_not_prefix c
  simp only [List.prefix_append_right_inj, List.cons_prefix_cons, Bool.true_eq_false,
    List.prefix_rfl, and_true, not_false_eq_true]

/-
* Theorem - The encodings of all vertices are unique.
This is true by construction of the tree.
-/
@[simp]
theorem HfmnTree.all_codes_distinct (t : HfmnTree α) (c : BoolList) :
  (t.vertices c).Pairwise (fun v₁ v₂ => v₁.code ≠ v₂.code) := by
  induction p:t with
  | Leaf val wt =>
    simp [vertices]

  | Node l r ihl ihr =>
    simp [vertices]
    -- set shorter names for initial codes passed to subtrees
    let cL := c ++ [false]
    let cR := c ++ [true]

    -- Use IHs on subtrees
    have pl := HfmnTree.all_codes_distinct l cL
    have pr := HfmnTree.all_codes_distinct r cR
      
    -- Prove disjointness between left and right vertices
    have disjoint := HfmnTree.codes_disjoint_of_nonprefix l r cL cR
      (by exact code_ft_not_prefix c)  -- c ++ [false] is not a prefix of c ++ [true]
      (by exact code_tf_not_prefix c) -- c ++ [true] is not a prefix of c ++ [false]

    constructor
    case left =>
      intro v₁ hv v₃ 
      cases hv with
      | inl hl =>
        have lv₁ : (v₁.code).length > c.length := by 
          have lv' : (v₁.code).length ≥ (c ++ [false]).length := by
             exact HfmnTree.vertices_len_geq l cL v₁ hl
          have lv'' : (c ++ [false]).length = c.length + 1 := by
            simp only [List.length_append, List.length_cons, List.length_nil, zero_add]
          linarith
        have lv₂ : (v₁.code).length = c.length := by
          exact congrArg List.length (id (Eq.symm v₃))
        rw [lv₂] at lv₁
        simp at lv₁
      | inr hr =>
        have lv₁ : (v₁.code).length > c.length := by 
          have lv' : (v₁.code).length ≥ (c ++ [true]).length := by
             exact HfmnTree.vertices_len_geq r cR v₁ hr
          have lv'' : (c ++ [true]).length = c.length + 1 := by
            simp only [List.length_append, List.length_cons, List.length_nil, zero_add]
          linarith
        have lv₂ : (v₁.code).length = c.length := by
          exact congrArg List.length (id (Eq.symm v₃))
        rw [lv₂] at lv₁
        simp at lv₁

    case right =>
      apply List.pairwise_append.2
      constructor
      · exact pl
      · -- right case
        constructor
        · exact pr
        · exact disjoint
termination_by (t.vertices c).length
