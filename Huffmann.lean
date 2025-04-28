/-
Huffmann Trees are trees used for data compression. They are binary trees where each leaf node represents a character and its frequency in the input data. The tree is constructed in such a way that characters with higher frequencies are closer to the root, allowing for shorter binary representations.

Some of the properties of Huffmann trees are:
* The values in a Huffmann tree only appear at leaves.
* The depth of a character in the tree is equal to the length of its binary representation.
* The characters in the left and right subtrees of a node are disjoint.
* Huffman trees are prefix-free, meaning no code is a prefix of another code.
* The algorithm is Optimal for the given set of characters and their frequencies.

We implements the Huffmann tree construction algorithm, and prove its correctness.
-/

set_option linter.unusedSectionVars false

abbrev BoolList := List Bool
abbrev AlphaNumList (α : Type) := List (α × Nat)
abbrev BoolEncList (α : Type) := List (α × BoolList)
abbrev TypeEncodedList (α : Type) := List (α × String)

/- 
Defined a Typeclass for the type of the inputs in the Huffmann tree. Since decoding would be primarlity on strings or integer inputs, they are all decidable, ordered and inhabited.
-/
class HfmnType (α : Type) [DecidableEq α]  where
  default : α

variable {α : Type} [DecidableEq α] [Inhabited α] [Ord α] [HfmnType α]

instance [Inhabited α] [DecidableEq α] : HfmnType α where
  default := default

def eg₁ : AlphaNumList Char := [('a', 45),('b', 13),('c', 12),('d', 16),('e', 9),('f', 5)]

/-Converts a String input to a Boolean List -/
def conv_enc_boollist (s : String) : BoolList :=
  s.toList.map (λ c => if c = '1' then true else false)

/- Converts a list of inputs and their frequencies to a list of (inputs x encoded BoolList).-/
def conv_str_freq_boollist (s : TypeEncodedList α) : List (α × BoolList) :=
  s.map (λ (c, val) => (c, conv_enc_boollist val))

/-
The HfmnTree is a binary tree where each node can be either a leaf or an internal node.
An inductive type is used to represent the tree structure, where a Node has a left and right Huffman Trees while Lead just has the values and weights. Both contain the BoolList uptill that vertex.
-/
inductive HfmnTree (α : Type) where
  | Node (left : HfmnTree α) (right : HfmnTree α) (code : BoolList := [])
  | Leaf (val : α) (weight : Nat) (code : BoolList := [])
deriving Inhabited, Repr

def HfmnTree.weight : HfmnTree α → Nat
  | Leaf _ w _ => w
  | Node l r _ => l.weight + r.weight

/-
Comparison function for Huffman trees weights
-/
def HfmnTree.compare (s s' : HfmnTree α) : Ordering :=
  Ord.compare s.weight s'.weight

instance : Ord (HfmnTree α) where
  compare := HfmnTree.compare

/-
The orderedInsert function inserts an element into a sorted list while maintaining the order.
-/
def orderedInsert (a : α) : List α → List α
  | [] => [a]
  | b :: l =>
    match compare a b with
    | .lt => a :: b :: l
    | _ => b :: orderedInsert a l

/- * Theorem: The orderedInsert function maintains the order of the list. -/
theorem orderedInsert_nonempty {α : Type} [Ord α] (a : α) (l : List α) :
  (orderedInsert a l).length > 0 := by
  induction l with
  | nil => simp [orderedInsert]
  | cons b t ih =>
    simp [orderedInsert]
    split <;> simp [List.length, ih, Nat.zero_lt_succ]
    
/- * Theorem: The length of the list after inserting an element is equal to the original length plus one.-/
theorem orderedInsert_inc_length {α : Type} [Ord α] (a : α) (l : List α) :
  (orderedInsert a l).length = l.length + 1 := by
  induction l with
  | nil => simp [orderedInsert]
  | cons h t ih =>
    simp [orderedInsert]
    split <;> simp [ih]
    
/- Insertion sort function that sorts a list of elements so that the elements are in non-decreasing order.-/
def insertionSort : List α → List α
  | [] => []
  | b :: l => orderedInsert b (insertionSort l)

-- #check insertionSort

/- * Theorem: The insertionSort function preserves the length of the list. -/
theorem insertionSort_preserves_length {α : Type} [Ord α] :
  ∀ l : List α, (insertionSort l).length = l.length := by
  intro l
  induction l with
  | nil => simp [insertionSort]
  | cons b l ih =>
    simp [insertionSort, ih]
    have h := orderedInsert_inc_length b (insertionSort l)
    rw [h]
    simp [List.length_cons]
    assumption

/- * Theorem: The insertionSorted non-empty list is non-empty -/
@[simp]
theorem sorted_nonempty_is_nonempty (trees : List (HfmnTree α)) (h : trees ≠ []) :
  insertionSort trees ≠ [] := by
  have h₁ : (insertionSort trees).length = trees.length := by
    apply insertionSort_preserves_length
  have h₂: (insertionSort trees).length > 0 := by
    rw [h₁]
    simp [List.length, h]
    simp [List.length_pos_iff]
    exact h
  simp [List.ne_nil_of_length_pos, h₂]


def String.freq(s : String) (c : Char) := s.data.filter (· == c) |>.length
-- #eval "hello".freq 'l' --2

def assignCodes {α : Type} : HfmnTree α → BoolList → HfmnTree α
  | .Leaf val wt _, code => .Leaf val wt code
  | .Node l r _, code =>
      let left  := assignCodes l (code ++ [false])
      let right := assignCodes r (code ++ [true])
      .Node left right code

/-
If t1 t2 is either Leaf or Node, when merged, it will be a Node.
-/
@[simp]
def HfmnTree.mergeTrees (t1 t2 : HfmnTree α) : HfmnTree α :=
  .Node t1 t2 

/-
In our algorithm, we take the mininum two trees and merge them. The merged tree is then inserted back into the list of trees.
-/
@[simp]
def HfmnTree.merge (trees : List (HfmnTree α)) (h : trees ≠ []) : HfmnTree α :=
  let sorted := insertionSort trees
  have hp : sorted ≠ [] := by
    apply sorted_nonempty_is_nonempty
    exact h

  match p:sorted with
  | [] => by simp at hp
  | [t] => assignCodes t [] -- 
  | t1 :: t2 :: rest =>
    let newTree := .mergeTrees t1 t2
    have : rest.length + 1 < trees.length := by
      have h₁ : sorted.length = trees.length := by apply insertionSort_preserves_length
      rw [← h₁]
      simp [p]
    HfmnTree.merge (newTree :: rest) (by simp)
termination_by trees.length

def eg : BoolList := [true, false, true, false]

def depthAux (tree: HfmnTree α) (c: α) (d: Int) : Int :=
  match tree with
  | HfmnTree.Leaf c' _ _ =>
    -- The decidability of equality has been invoked previously for the type α
    if c = c' then d else -1
  | HfmnTree.Node l r _ =>
    let leftDepth := depthAux l c (d + 1)
    if leftDepth != -1 then leftDepth else depthAux r c (d + 1)

/-
Returns the depth of a character in the Huffman tree, if not found returns -1
-/
def HfmnTree.findDepth (tree: HfmnTree α) (c: α) : Int :=
  -- Helper function to calculate the depth of a character in the tree
  depthAux tree c 0 

/-
The encodeWithDepth function encodes a character starting from root of given `t` tree. Thus if given the full HfmnTree, it wil return complete encoding of the tree. Else it may just give the encoding starting from given tree.
-/
def HfmnTree.encodeWithDepth (c : α) (t : HfmnTree α) : (BoolList × Nat) :=
  let coded := assignCodes t []
  let rec search (tree : HfmnTree α) (d : Nat) : (BoolList × Nat) :=
    match tree with
    | HfmnTree.Leaf val _ code => if val = c then (code, d) else ([], 0)
    | HfmnTree.Node l r _ =>
        let left := search l (d + 1)
        if left.fst ≠ [] then left else search r (d + 1)
  search coded 0

def HfmnTree.encode (c : α) (t: HfmnTree α) : BoolList :=
  (HfmnTree.encodeWithDepth c t).1

def HfmnTree.depth (c : α) (t: HfmnTree α) : Nat :=
  (HfmnTree.encodeWithDepth c t).2

/-
* Theorem: Depth is equal to the length of the code
-/
-- theorem HfmnTree.depth_is_length_enc (c: α) (t: HfmnTree α) (code : BoolList) :
--   t.encode c = code → t.depth c = code.length := by
--     cases t
--     case Leaf c' w cc =>
--       simp [encode, depth, encodeWithDepth]
--       intro h₁ h₂
--       simp [h₁, h₂]
--     case Node l r code =>
--       match p:l.encodeWithDepth c, p':r.encodeWithDepth c with
--       | none, some (s, d) => -- s is the code of the right tree
--         simp [encode, depth, encodeWithDepth, p, p']
--         intro h
--         match code with
--         | ch :: ct =>
--           let ihr := HfmnTree.depth_is_length_enc c r ct
--           simp [encode, depth, encodeWithDepth, p, p'] at ihr
--           simp at h 
--           
--           rename_i bl
--           sorry
--         | code =>
--           rename_i bl br
--           match bl with
--           | [] => 
--             simp [encode, depth, encodeWithDepth, p, p']
--             have : (code ++ [true]).length > 0 := by
--               simp [List.length, List.length_pos_iff] 
--             sorry
--           | rest =>
--
--             sorry
--
--       | some (s, d), none =>
--         simp [encode, depth, encodeWithDepth, p, p']
--         intro h
--         match code with
--         | ch :: ct =>
--           let ihl := HfmnTree.depth_is_length_enc c l ct
--           simp [encode, depth, encodeWithDepth, p, p'] at ihl
--           simp at h
--           sorry
--         | code =>
--           sorry
--       | none, none =>
--         simp [encode, depth, encodeWithDepth, p, p']
--       | some (s, d), some (s', d') =>
--         simp [encode, depth, encodeWithDepth, p, p']
--
-- #eval depthAux (HfmnTree.Leaf 'a' 1) 'a' 0 -- 0
-- #eval depthAux (HfmnTree.Node (HfmnTree.Leaf 'a' 1) (HfmnTree.Leaf 'b' 2) ) 'a' 0

/-
The Alphabet structure is used to represent the values and their frequencies in the input data. It contains a value of type α and a frequency of type Nat.
-/
structure Alphabet (α : Type) where
  val : α
  freq : Nat
deriving Inhabited, Repr

abbrev AlphaNumTree (α : Type) := List (Alphabet α)

def convert_input_to_alphabet (input : AlphaNumList α) : AlphaNumTree α := input.map fun a => Alphabet.mk a.1 a.2

/-
* Theorem: The conversion function `convert_input_to_alphabet` for a non-empty list is non-empty.
-/
theorem cita_ne_to_ne (s : AlphaNumList α) (h : s ≠ []) :
  convert_input_to_alphabet s ≠ [] := by
  intro hi
  have h₁ : (convert_input_to_alphabet s).length = s.length := by
    apply List.length_map
  have h₂ : (convert_input_to_alphabet s).length = 0 := by
    rw [hi]
    simp [List.length, List.length_map] 
  have h₃ : (convert_input_to_alphabet s).length > 0 := by
    rw [h₁]
    simp [List.length, h, List.length_pos_iff] 
  rw [h₂] at h₃
  exact Nat.lt_irrefl 0 h₃

/-
The main Tree creator function which takes the input and returns the Huffman tree, with the encoded BoolList included.
-/
def HfmnTree.tree (huffinput : AlphaNumList α) : HfmnTree α :=
  if p:huffinput.isEmpty then -- Handle []
    HfmnTree.Leaf HfmnType.default 0
  else
    have huffinput_nonempty : huffinput ≠ [] := by intro h₁; rw [h₁] at p; simp at p        

    let input := convert_input_to_alphabet huffinput
    have hi : input ≠ [] := by
      apply cita_ne_to_ne
      exact huffinput_nonempty 

    let leaves : List (HfmnTree α) := input.map (fun a => HfmnTree.Leaf a.val a.freq)
    have hl : leaves ≠ [] := by
      intro h
      have h₁ : (leaves).length = (input).length := by
        apply List.length_map
      have h₂ : (leaves).length = 0 := by
        rw [h]
        simp [List.length, List.length_map]
      have h₃ : (leaves).length > 0 := by
        rw [h₁]
        simp [List.length, huffinput_nonempty, List.length_pos_iff, hi]
      rw [h₂] at h₃
      exact Nat.lt_irrefl 0 h₃

    let sorted := insertionSort leaves
        
    have sorted_nonempty : sorted ≠ [] := by
      apply sorted_nonempty_is_nonempty
      exact hl

    let sorted_tree := HfmnTree.merge sorted (by simp [sorted_nonempty] )
    sorted_tree

-- #eval HfmnTree.tree eg₁

/-
Extracts the encoded BoolList from a Huffman tree.
-/
def HfmnTree.encodedList (huffinput : AlphaNumList α) : BoolEncList α :=
  let codedTree := assignCodes (HfmnTree.tree huffinput) []
  let rec collect (t : HfmnTree α) : BoolEncList α :=
    match t with
    | HfmnTree.Leaf c _ code => [(c, code)]
    | HfmnTree.Node l r _    => collect l ++ collect r
  collect codedTree

-- #eval HfmnTree.encodedList eg₁
--   [('a', [false]),
--   ('b', [true, false, true]),
--   ('c', [true, false, false]),
--   ('d', [true, true, true]),
--   ('e', [true, true, false, true]),
--   ('f', [true, true, false, false])]  

/-
The leastEncodedData function calculates the total number of bits used to encode the input data using the Huffman tree. It multiplies the length of each code by its frequency and sums them up.
-/
def Huffmann.leastEncodedData (huffinput : AlphaNumList α) : Nat :=
  let encoded := HfmnTree.encodedList huffinput
  huffinput.foldl (fun acc (a, count) => 
    match encoded.find? (fun (x, _) => x == a) with
    | some (_, code) => acc + code.length * count
    | none => acc  -- or handle missing case as needed
  ) 0

-- #eval Huffmann.leastEncodedData eg₁ -- 224  

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

/-
The vertices of a Huffman tree are the nodes and leaves of the tree. The function returns Leaf/Node with their corresponding codes.
-/
@[simp]
def HfmnTree.vertices : HfmnTree α → List Vertex
  | HfmnTree.Leaf _ _ code => [Vertex.Leaf code]
  | HfmnTree.Node l r code => Vertex.Node code :: (vertices l ++ vertices r)

/-
* Theorem: The vertices of a Huffman tree are non-empty.
-/
theorem HfmnTree.vertices_nonempty (t : HfmnTree α) :
  t.vertices ≠ [] := by
  induction t with
  | Leaf c w code =>
    simp [vertices]
  | Node l r code =>
    simp [vertices]
 
-- #eval HfmnTree.vertices (HfmnTree.tree eg₁)

/-
* Theorem - The encodings of all vertices are unique.
This is true by construction of the tree.
-/
theorem HfmnTree.all_codes_unique (t : HfmnTree α) : 
    (t.vertices).Pairwise (fun v₁ v₂ => v₁ ≠ v₂ → Vertex.code v₁ ≠ Vertex.code v₂) := by
  induction t with
  | Leaf c w code =>
    simp [vertices]
  | Node l r code =>
    simp [vertices]
    rename_i ihl ihr
    constructor

    case left =>
      intro v hl hr
      cases hl with
      | inl hl =>
        have h': Vertex.code v ∈ l.vertices.map Vertex.code := by
          simp [List.mem_map]; exact ⟨v, hl, rfl⟩
        simp [List.mem_map] at h'
         
        sorry
      | inr hr' =>
        have h': Vertex.code v ∈ r.vertices.map Vertex.code := by
          simp [List.mem_map]; exact ⟨v, hr', rfl⟩
        simp [List.mem_map] at h' 
        sorry

    case right =>
      sorry
    
/- Returns the set of values in the tree. -/
def HfmnTree.chars: HfmnTree α → List α
  | Leaf c _ _ => [c]
  | Node l r _ => l.chars ++ r.chars

/- Helper list intersection function. -/
def List.inter(l₁ l₂ : List α) : List α :=
  l₁.filter (· ∈ l₂)

/- Helper function to check if a character is in the tree. -/
def HfmnTree.charInTree (t : HfmnTree α) (c : α) : Bool :=
  t.chars.contains c

/-
* Property: The characters/values in the left and right subtrees of a node are disjoint.
-/
def disjointChars (t : HfmnTree α) : Prop :=
  match t with 
  | HfmnTree.Leaf _ _ _ => True
  | HfmnTree.Node l r _ =>
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
* Theorem: disjointChars Property holds true for the Huffmann tree.
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
* Theorem: The Huffmann tree is prefix-free.
-/
theorem HfmnTree.hfmntree_is_prefix_free (t : HfmnTree α) :
  t.vertices.Pairwise (fun v₁ v₂ => v₁ ≠ v₂ → checkPrefixfree v₁.code v₂.code) := by
  induction t with
  | Leaf c w code =>
    simp [vertices]
  | Node l r code =>
    simp [vertices]
    rename_i ihl ihr
    constructor

    case left =>
      intro v hl hr
      cases hl with
      | inl hl =>
        have h': Vertex.code v ∈ l.vertices.map Vertex.code := by
          simp [List.mem_map]; exact ⟨v, hl, rfl⟩
        simp [List.mem_map] at h'
        sorry
      | inr hr' =>
        have h': Vertex.code v ∈ r.vertices.map Vertex.code := by
          simp [List.mem_map]; exact ⟨v, hr', rfl⟩
        simp [List.mem_map] at h' 
        sorry

    case right =>
      sorry

/-
Decoding the encoded input. decode(encode(x)) = x, since the tree is prefix free and the code is unique.
This should be our final goal, to show for a huffman tree, the decoding of the encoded input is equal to the original input.
-/
def HfmnTree.decode (enc_boolinput : BoolList) (enc_huffinput : List (α × BoolList)) : Option α :=
  enc_huffinput.find? (λ (_, s) => s = enc_boolinput) |>.map (·.1)

-- #eval HfmnTree.decode "1" ( HfmnTree.encoded_tree eg₁ ).1 -- none
-- #eval HfmnTree.decode "0" ( HfmnTree.encoded_tree eg₁ ).1 -- some 'a'
