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
import Mathlib
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
  | Node (left : HfmnTree α) (right : HfmnTree α)
  | Leaf (val : α) (weight : Nat)
deriving Inhabited, Repr

def HfmnTree.weight : HfmnTree α → Nat
  | Leaf _ w => w
  | Node l r => l.weight + r.weight

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
    exact List.length_pos_iff.mpr h
  simp [List.ne_nil_of_length_pos, h₂]


def String.freq(s : String) (c : Char) := s.data.filter (· == c) |>.length
-- #eval "hello".freq 'l' --2

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
  | [t] => t
  | t1 :: t2 :: rest =>
    let newTree := .mergeTrees t1 t2
    have : rest.length + 1 < trees.length := by
      have h₁ : sorted.length = trees.length := by apply insertionSort_preserves_length
      rw [← h₁]
      simp [p]
    HfmnTree.merge (newTree :: rest) (by simp)
termination_by trees.length

def eg : BoolList := [true, false, true, false]

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
    exact List.eq_nil_iff_length_eq_zero.mp hi
  have h₃ : (convert_input_to_alphabet s).length > 0 := by
    rw [h₁]
    exact List.length_pos_iff.mpr h
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
      assumption

    let leaves : List (HfmnTree α) := input.map (fun a => HfmnTree.Leaf a.val a.freq)
    have hl : leaves ≠ [] := by
      intro h
      have h₁ : (leaves).length = (input).length := by
        apply List.length_map
      have h₂ : (leaves).length = 0 := by
        exact List.eq_nil_iff_length_eq_zero.mp h 
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
    
/- Returns the set of values in the tree. -/
def HfmnTree.chars: HfmnTree α → List α
  | Leaf c _  => [c]
  | Node l r  => l.chars ++ r.chars

/- Helper function to check if a character is in the tree. -/
def HfmnTree.charInTree (t : HfmnTree α) (c : α) : Bool :=
  t.chars.contains c

def HfmnTree.encode (c: α) (t : HfmnTree α) : BoolList :=
  match t with
  | .Leaf c' _ =>
    if c = c' then [] else panic! "-1" -- This should never happen
  | .Node l r =>
    if l.charInTree c then
      false :: encode c l
    else
      true :: encode c r

-- #eval HfmnTree.encode 'a' (HfmnTree.tree eg₁) -- [false]

/-
Extracts the encoded BoolList from a Huffman tree.
-/
def HfmnTree.encodedList (huffinput : AlphaNumList α) : BoolEncList α :=
  let huffTree := HfmnTree.tree huffinput
  let chars := huffTree.chars
  chars.map (fun c => (c, HfmnTree.encode c huffTree))

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

-- #eval (Vertex.Leaf [false, true]).code
-- #eval (Vertex.Node [false, true]).code

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
* Theorem: The vertices of a Huffman tree are non-empty.
-/
theorem HfmnTree.vertices_nonempty (t : HfmnTree α) (code : BoolList) :
  t.vertices code ≠ [] := by
  induction t generalizing code with
  | Leaf _ _ =>
    simp [vertices]
  | Node _ _ _ _ =>
    simp [vertices]

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

@[simp]
lemma lenpref_of_pref_isprefix (c₁ c₂ : BoolList) (v : BoolList) :
  c₁ <+: v → c₂ <+: v → c₁.length ≤ c₂.length → c₁ <+: c₂  := by
  exact fun a a_1 a_2 ↦ List.prefix_of_prefix_length_le a a_1 a_2

theorem HfmnTree.codes_disjoint_of_nonprefix 
  (t₁ t₂ : HfmnTree α) (c₁ c₂ : BoolList)
  (h₁ : ¬ c₁ <+: c₂) (h₂ : ¬ c₂ <+: c₁) :
  ∀ v₁ ∈ t₁.vertices c₁, ∀ v₂ ∈ t₂.vertices c₂, Vertex.code v₁ ≠ Vertex.code v₂ := by
  intro v₁ hv₁ v₂ hv₂
  -- the initial codes themselves must be unequal
  have hnc : c₁ ≠ c₂ := by
    intro eq; apply h₁;
    simp [eq]

  -- each code of v in tree t has its prefix c
  have p₁ := HfmnTree.initialCodeIsPrefix t₁ c₁ v₁ hv₁
  have p₂ := HfmnTree.initialCodeIsPrefix t₂ c₂ v₂ hv₂

  intro heq
  -- if the codes are equal, then the prefixes must be equal
  have hne₁ : c₁.isPrefixOf v₂.code := by
    simp only [List.isPrefixOf_iff_prefix]
    rw [← heq]
    exact List.isPrefixOf_iff_prefix.mp p₁

  have hne₂ : c₂.isPrefixOf v₁.code := by
    simp only [List.isPrefixOf_iff_prefix]
    rw [heq]
    exact List.isPrefixOf_iff_prefix.mp p₂

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
* Theorem - The encodings of all vertices are unique.
This is true by construction of the tree.
-/
theorem HfmnTree.all_codes_unique (t : HfmnTree α) : 
    (t.vertices []).Pairwise (fun v₁ v₂ => Vertex.code v₁ ≠ Vertex.code v₂) := by
  induction t with
  | Leaf c w =>
    simp [vertices]

  | Node l r =>
    simp [vertices]
    rename_i ihl ihr
    constructor

    case left =>
      intro v hl
      cases hl with
      | inl hl =>
        have h' : Vertex.code v ∈ (l.vertices [false]).map Vertex.code := by
          simp [List.mem_map]; exact ⟨v, hl, rfl⟩
        simp [List.mem_map] at h'
        by_contra hc
        sorry
      | inr hr' =>
        have h': Vertex.code v ∈ (r.vertices [true]).map Vertex.code := by
          simp [List.mem_map]; exact ⟨v, hr', rfl⟩
        simp [List.mem_map] at h' 
        by_contra hc
        sorry 

    case right =>
      sorry

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

/-
Decoding the encoded input. decode(encode(x)) = x, since the tree is prefix free and the code is unique.
This should be our final goal, to show for a huffman tree, the decoding of the encoded input is equal to the original input.
-/
def HfmnTree.decode (enc_boolinput : BoolList) (enc_huffinput : List (α × BoolList)) : Option α :=
  enc_huffinput.find? (λ (_, s) => s = enc_boolinput) |>.map (·.1)

-- #eval HfmnTree.decode "1" ( HfmnTree.encoded_tree eg₁ ).1 -- none
-- #eval HfmnTree.decode "0" ( HfmnTree.encoded_tree eg₁ ).1 -- some 'a'
