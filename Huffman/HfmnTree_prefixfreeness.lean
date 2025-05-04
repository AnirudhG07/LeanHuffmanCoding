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


@[simp]
lemma List.prefix_eqlen_eq (l₁ l₂ bl : BoolList) :
  l₁.length = l₂.length → l₁.isPrefixOf bl → l₂.isPrefixOf bl → l₁ = l₂ := by
  intro hlen hp₁ hp₂
  -- unpack the prefixes into `bl = l₁ ++ s₁` and `bl = l₂ ++ s₂`
  induction p:l₁ with
  | nil =>
    have : l₂ = [] := by
      have : l₂.length = 0 := by
        rw [← hlen]; exact eq_nil_iff_length_eq_zero.mp p 
      exact eq_nil_iff_length_eq_zero.mpr this
    simp [this]
  | cons x xs ih =>
    -- Both lists must be non-empty since length > 0
    match q:l₂ with
    | nil => 
      simp at hlen 
      rw [p] at hlen; assumption
     | cons y ys =>
      have head_eq : x = y := by
        cases bl with
        | nil => 
          simp at hp₁ hp₂
        | cons b bs =>
          simp_all
      have tail_eq : xs = ys := by
        simp_all
        have hp₁' : [y] ++ ys <+: bl := by
          exact hp₂
        have hp₂' : [y] ++ xs <+: bl := by
          exact hp₁
        sorry
      
      apply cons_eq_cons.mpr
      constructor
      · assumption
      · assumption

 
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
