import Huffman.HfmnTree_uniqueness

variable {α : Type} [DecidableEq α] [Inhabited α] [Ord α] [HfmnType α]

instance [Inhabited α] [DecidableEq α] : HfmnType α where
  default := default

/- Check is a vertex is Leaf or not -/
@[simp, grind .]
def Vertex.isLeaf (v : Vertex) : Bool :=
  match v with
  | Vertex.Leaf _ => true
  | Vertex.Node _ => false

/-
This function returns the list of vertices of a Huffman tree that are leaves.
-/
@[simp, grind .]
def HfmnTree.leaves (t : HfmnTree α) (code : BoolList) : List Vertex :=
  (t.vertices code).filter (fun v => v.isLeaf)

-- #eval HfmnTree.leaves (HfmnTree.tree eg₁) []

/-
* Theorem: All leaves of a Huffman tree are unique. Directly follows from `all_codes_distinct`.
-/
theorem HfmnTree.all_leaves_distinct (t : HfmnTree α) (c : BoolList) :
  (t.leaves c).Pairwise (fun v₁ v₂ => v₁.code ≠ v₂.code) := by
  simp [leaves]
  exact (HfmnTree.all_codes_unique t c).filter _

/- Check if 2 BoolEncList are prefix free of each other. -/
def checkPrefixfree (bl₁ bl₂: BoolList) : Bool :=
  ¬List.isPrefixOf bl₁ bl₂ ∧ ¬ List.isPrefixOf bl₂ bl₁

-- #eval checkPrefixfree [true, false, false] [true, false] -- false

@[simp, grind .]
lemma List.eq_suff_eq_len ( c: BoolList) :
  (c ++ [true]).length = (c ++ [false]).length := by grind

/-
* Lemma - Two lists of equal length and prefix of the same list are equal.
-/
lemma List.prefix_eqlen_eq_n (n : ℕ) : ∀ (l₁ l₂ bl : BoolList),
  l₁.length = n → l₂.length = n → l₁.isPrefixOf bl → l₂.isPrefixOf bl → l₁ = l₂ := by
    induction n with
    | zero =>
      intro l₁ l₂ bl hlength₁ hlength₂ hpref₁ hpref₂
      rw [length_eq_zero_iff] at hlength₁ hlength₂
      grind
    | succ m ih =>
      intro l₁ l₂ bl hlength₁ hlength₂ hpref₁ hpref₂
      match bl with
      | [] => simp_all
      | b :: bs =>
        match l₁, l₂ with
        | [], _ => simp at hlength₁
        | _, [] => simp at hlength₂
        | a₁ :: as₁, a₂ :: as₂ =>
          grind
/-
* Lemma - Two lists of equal length and prefix of the same list are equal.
Simplified version of the above lemma.
-/
lemma List.prefix_eqlen_eq (l₁ l₂ bl : BoolList) :
  l₁.length = l₂.length → l₁.isPrefixOf bl → l₂.isPrefixOf bl → l₁ = l₂ := by
  have h := prefix_eqlen_eq_n l₁.length l₁ l₂ bl
  grind

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
        simp only [List.isPrefixOf_iff_prefix, Bool.decide_and, decide_not, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
        have pr₁: (c++ [false]).isPrefixOf v₁.code := by
          exact initialCodeIsPrefix l cL v₁ hv₁
        have pr₂: (c++ [true]).isPrefixOf v₂.code := by
          exact initialCodeIsPrefix r cR v₂ hv₂
        grind +suggestions
