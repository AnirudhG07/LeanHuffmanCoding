import Huffman.HfmnTree_uniqueness
/-
* Property: The characters/values in the left and right subtrees of a node are disjoint.
-/
def disjointChars (t : HfmnTree α) : Prop :=
  match t with 
  | HfmnTree.Leaf _ _ => True
  | HfmnTree.Node l r =>
    [] = l.chars.inter r.chars

/-
* Theorem: Merge of two trees with disjoint characters is disjoint
-/
theorem merge_preserves_disjoint_chars {α : Type} [DecidableEq α] (l r : HfmnTree α) :
  disjointChars l → disjointChars r → l.chars.inter r.chars = [] → disjointChars (HfmnTree.mergeTrees l r) := by
  intro h₁ h₂ h₃
  simp [HfmnTree.mergeTrees, disjointChars] 
  assumption

/-
* Theorem: disjointChars Property holds true for the Huffman tree.
This is to show that the same character can not be present in more than one Leaf.
If vertex at leaf₁ = vertex at leaf₂, then the characters are same.
-/
theorem left_right_tree_disjoint_chars (huffinput: AlphaNumList α) :
  disjointChars (HfmnTree.tree huffinput) := by
  induction huffinput with
  | nil => 
    constructor
  | cons a rest ih =>
    match rest with 
    | [] => -- Base case: if the list is empty, the tree is a leaf
      sorry
      
    | [b] => -- Only 1 element      
      sorry
    | b :: rest' =>
      sorry 
    
