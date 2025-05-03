import Huffman.HuffmanTree
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
    

/- Check if 2 BoolEncList are prefix free of each other. -/
def checkPrefixfree (bl₁ bl₂: BoolList) : Bool :=
  bl₁ ≠ bl₂ ∧ ¬(bl₁.isPrefixOf bl₂ ∨ bl₂.isPrefixOf bl₁)

-- #eval checkPrefixfree [true, false, false] [true, false] -- false

/-
Check if the encoded list is prefix free, i.e. compares each encoded string with all other strings.
-/
def isPrefixfree : BoolEncList α → Bool
  | [] => true
  | (_, bl) :: rest => rest.all (fun al => checkPrefixfree bl al.2) && isPrefixfree rest

/-
* Property: A tree is prefix-free if no code is a prefix of another code.
-/
def prefixFreeTree (huffinput : AlphaNumList α) : Prop :=
  let enc_list := HfmnTree.encodedList huffinput
  isPrefixfree enc_list

-- #eval isPrefixfree (HfmnTree.encoded_tree eg₁).1 -- true

-- #eval isPrefixfree (conv_str_freq_boollist [('a', "0"),('b', "101"),('c', "100"),('d', "011"),('e', "1101"),('f', "1100")]) -- false


/-
* Theorem: The Huffman tree is prefix-free.
-/
theorem HfmnTree.hfmntree_is_prefix_free (t : HfmnTree α) :
  (t.vertices []).Pairwise (fun v₁ v₂ => v₁ ≠ v₂ → checkPrefixfree v₁.code v₂.code) := by
  induction t with
  | Leaf c w =>
    simp [vertices]
  | Node l r code =>
    simp [vertices]
    rename_i ihl ihr
    constructor

    case left =>
      intro v hl hr
      cases hl with
      | inl hl =>
        have h': Vertex.code v ∈ (l.vertices [false]).map Vertex.code := by
          simp [List.mem_map]; exact ⟨v, hl, rfl⟩
        simp [List.mem_map] at h'
        sorry
        
      | inr hr' =>
        have h': Vertex.code v ∈ (r.vertices [true]).map Vertex.code := by
          simp [List.mem_map]; exact ⟨v, hr', rfl⟩
        simp [List.mem_map] at h' 
        sorry

    case right =>
      sorry
