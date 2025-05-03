import Huffman.HfmnTree_uniqueness

variable {α : Type} [DecidableEq α] [Inhabited α] [Ord α] [HfmnType α]

instance [Inhabited α] [DecidableEq α] : HfmnType α where
  default := default

/-
All the leaves of the tree, paired with the Huffman‐code (as a BoolList) you accumulate along the path down to each leaf.
-/
@[simp]
def HfmnTree.leafVertices (t : HfmnTree α) : BoolList → List Vertex
  | code => (t.vertices code).filter (fun v => match v with
      | Vertex.Leaf _ => true
      | Vertex.Node _ => false)

/- All leaf‐vertices of `t`, starting with the `code`. -/
@[simp]
def HfmnTree.leaves (t : HfmnTree α) (code : BoolList) : List Vertex :=
  t.leafVertices code

-- #eval HfmnTree.leaves (HfmnTree.tree eg₁) []

/-
* Theorem: All leaves of a Huffman tree are unique. Directly follows from `all_codes_distinct`.
-/
theorem HfmnTree.all_leaves_distinct (t : HfmnTree α) (c : BoolList) :
  (t.leaves c).Pairwise (fun v₁ v₂ => v₁.code ≠ v₂.code) := by
  simp [leaves, leafVertices]
  exact (HfmnTree.all_codes_distinct t c).filter _

/- Check if 2 BoolEncList are prefix free of each other. -/
def checkPrefixfree (bl₁ bl₂: BoolList) : Bool :=
  ¬ List.isPrefixOf bl₁ bl₂ ∧ ¬ List.isPrefixOf bl₂ bl₁

-- #eval checkPrefixfree [true, false, false] [true, false] -- false

/-
Check if the encoded list is prefix free, i.e. compares each encoded string with all other strings.
-/
def isPrefixfree (vs : List Vertex) : Bool :=
  vs.Pairwise (fun v₁ v₂ => checkPrefixfree v₁.code v₂.code)

/-
* Property - A Huffman tree is prefix‐free precisely when its leaves’ codes are.
-/
def prefixFreeTree (t : HfmnTree α) (code: BoolList) : Prop :=
  isPrefixfree (t.leaves code) = True

-- #eval isPrefixfree (HfmnTree.leaves (HfmnTree.tree eg₁) [])

/-
* Theorem: The Huffman tree is prefix-free.
-/
/-- A tree is prefix-free if none of its **leaf** codes is a prefix of another. -/
theorem HfmnTree.hfmntree_is_prefix_free (t : HfmnTree α) (c : BoolList) :
  isPrefixfree (t.leaves c) := by
  simp only [leaves, leafVertices, isPrefixfree]
  sorry
