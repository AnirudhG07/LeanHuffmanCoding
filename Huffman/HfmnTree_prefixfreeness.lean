import Huffman.HfmnTree_uniqueness

variable {α : Type} [DecidableEq α] [Inhabited α] [Ord α] [HfmnType α]

instance [Inhabited α] [DecidableEq α] : HfmnType α where
  default := default

/- Check is a vertex is Leaf or not -/
@[simp]
def Vertex.isLeaf (v : Vertex) : Bool :=
  match v with
  | Vertex.Leaf _ => true
  | Vertex.Node _ => false

/-
This function returns the list of vertices of a Huffman tree that are leaves.
-/
@[simp]
def HfmnTree.leaves (t : HfmnTree α) (code : BoolList) : List Vertex :=
  (t.vertices code).filter (fun v => v.isLeaf)

-- #eval HfmnTree.leaves (HfmnTree.tree eg₁) []

/-
* Theorem: All leaves of a Huffman tree are unique. Directly follows from `all_codes_distinct`.
-/
theorem HfmnTree.all_leaves_distinct (t : HfmnTree α) (c : BoolList) :
  (t.leaves c).Pairwise (fun v₁ v₂ => v₁.code ≠ v₂.code) := by
  simp [leaves]
  exact (HfmnTree.all_codes_distinct t c).filter _

/- Check if 2 BoolEncList are prefix free of each other. -/
def checkPrefixfree (bl₁ bl₂: BoolList) : Bool :=
  ¬List.isPrefixOf bl₁ bl₂ ∧ ¬ List.isPrefixOf bl₂ bl₁

-- #eval checkPrefixfree [true, false, false] [true, false] -- false

@[simp]
lemma List.eq_suff_eq_len ( c: BoolList) :
  (c ++ [true]).length = (c ++ [false]).length := by
  have hc₁ : (c++[true]).length = c.length +1 := by
    simp only [length_append, length_cons, length_nil, zero_add]
  have hc₂ : (c++[false]).length = c.length +1 := by
    simp only [length_append, length_cons, length_nil, zero_add]
  rw [hc₁, hc₂]

/-
* Lemma: Equal length prefix of the same list are equal
-/
@[simp]
lemma List.prefix_eqlen_eq (l₁ l₂ bl : BoolList) :
  l₁.length = l₂.length → l₁ <+: bl → l₂ <+: bl → l₁ = l₂ := by
  intro hlen hp₁ hp₂
  -- unpack the prefixes into `bl = l₁ ++ s₁` and `bl = l₂ ++ s₂`
  induction l₁ generalizing l₂ bl with
  | nil =>
    have : l₂ = [] := by
      exact eq_nil_iff_length_eq_zero.mpr (id (Eq.symm hlen))
    simp [this]
  | cons x xs ih =>
    -- Both lists must be non-empty since length > 0
    match l₂ with
    | nil => 
      simp at hlen  -- Contradiction since lengths don't match
    | cons y ys =>
      -- Extract the first elements
      cases hp₁ with | intro h₁t h₁r =>
      cases hp₂ with | intro h₂t h₂r =>
      -- First elements must be equal

      sorry 
 
/-
* Theorem: The Huffman tree is prefix-free.
-/
theorem HfmnTree.hfmntree_is_prefix_free (t : HfmnTree α) (c : BoolList) :
  (t.vertices c).Pairwise (fun v₁ v₂ => v₁.isLeaf → v₂.isLeaf → checkPrefixfree v₁.code v₂.code) := by
  induction p:t with
  | Leaf _ _ =>
    exact List.pwFilter_eq_self.mp rfl
  | Node l r =>
    simp [vertices]

    let cL := c ++ [false]
    let cR := c ++ [true]

    let pl := HfmnTree.hfmntree_is_prefix_free l cL
    let pr := HfmnTree.hfmntree_is_prefix_free r cR
     
    apply List.pairwise_append.2
    constructor
    case left =>
      exact pl
    case right =>
      constructor
      · exact pr
      · intro v₁ hv₁ v₂ hv₂ vl₁ vl₂
        unfold checkPrefixfree 
        simp only [List.isPrefixOf_iff_prefix, Bool.decide_and, decide_not, Bool.and_eq_true,
          Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
        
        have pr₁: ( c++ [false]).isPrefixOf v₁.code := by
          exact initialCodeIsPrefix l cL v₁ hv₁
        have pr₂: ( c++ [true]).isPrefixOf v₂.code := by
          exact initialCodeIsPrefix r cR v₂ hv₂ 
        simp at pr₁ pr₂
        have cleq : cL.length = cR.length := by
          exact Eq.symm (List.eq_suff_eq_len c)
        have cneq : ¬ cL = cR := by
          unfold cL cR
          simp only [List.append_cancel_left_eq, List.cons.injEq, Bool.false_eq_true, and_true,
            not_false_eq_true]

        constructor
        · intro h₁
          have h' : (c ++ [false]) <+: v₂.code := by
            exact List.IsPrefix.trans pr₁ h₁
          have ceq : cL = cR := by
            exact List.prefix_eqlen_eq cL cR v₂.code cleq h' pr₂
          contradiction
            
        · intro h₂
          have h' : (c ++ [true]) <+: v₁.code := by
            exact List.IsPrefix.trans pr₂ h₂
          have ceq : cL = cR := by
            exact List.prefix_eqlen_eq cL cR v₁.code cleq pr₁ h'
          contradiction
