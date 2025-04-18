/-
# This contains the definition of a huffmann tree, a binary tree used to encode data.
We will initially define the binary treee for encoding and get the minimum encoded data for the list of input data.
-/

abbrev BoolList := List Bool
abbrev AlphaNumList (α : Type) := List (α × Nat)
abbrev BoolEncList (α : Type) := List (α × BoolList)
abbrev TypeEncodedList (α : Type) := List (α × String)

-- This is made so that I can use for any type of data which is HuffmanType, etc. like Char, Int, etc.
class HfmnType (α : Type) [DecidableEq α]  where
  default : α

variable {α : Type} [DecidableEq α] [Inhabited α] [Ord α] [HfmnType α]

def eg₁ : AlphaNumList Char := [('a', 45),('b', 13),('c', 12),('d', 16),('e', 9),('f', 5)]

def conv_enc_boollist (s : String) : BoolList :=
  s.toList.map (λ c => if c = '1' then true else false)

def conv_str_freq_boollist (s : TypeEncodedList α) : List (α × BoolList) :=
  s.map (λ (c, str) => (c, conv_enc_boollist str))

-- Huffman Tree Definition
inductive HfmnTree (α : Type) where
  | Node (left : HfmnTree α) (right : HfmnTree α)
  | Leaf (val : α) (weight : Nat) (code : BoolList := [])
deriving Inhabited, Repr

-- Theorem: Values in a Huffman tree only appear at leaves
theorem vals_at_leaves {α : Type} (tree : HfmnTree α) :
  ∀ (x : α), (∃ (w : Nat) (code : BoolList), tree = HfmnTree.Leaf x w code) ↔ 
             (∃ (leaf : HfmnTree α), (∃ (w : Nat) (code : BoolList), leaf = HfmnTree.Leaf x w code) ∧ tree = leaf) := by
  intro x
  constructor
  -- Forward: If x appears in tree, it must be in a Leaf
  · intro h
    rcases h with ⟨w, code, h_eq⟩
    exists HfmnTree.Leaf x w code
    simp [h_eq]
  -- Backward: If some Leaf equals tree and holds x, then x is in tree
  · intro h
    rcases h with ⟨leaf, ⟨w, code, h_leaf⟩, h_tree⟩
    exists w, code
    rw [h_tree, h_leaf]


def HfmnTree.weight : HfmnTree α → Nat
  | Leaf _ w _ => w
  | Node l r => l.weight + r.weight

-- Comparison function for Huffman trees weights
def HfmnTree.compare (s s' : HfmnTree α) : Ordering :=
  Ord.compare s.weight s'.weight

instance : Ord (HfmnTree α) where
  compare := HfmnTree.compare

-- Insert an element in a way that does not break the order of the sorted list.
def orderedInsert (a : α) : List α → List α
  | [] => [a]
  | b :: l =>
    match compare a b with
    | .lt => a :: b :: l
    | _ => b :: orderedInsert a l

theorem orderedInsert_nonempty {α : Type} [Ord α] (a : α) (l : List α) :
  (orderedInsert a l).length > 0 := by
  induction l with
  | nil => simp [orderedInsert]
  | cons b t ih =>
    simp [orderedInsert]
    split <;> simp [List.length, ih, Nat.zero_lt_succ]
    
theorem orderedInsert_inc_length {α : Type} [Ord α] (a : α) (l : List α) :
  (orderedInsert a l).length = l.length + 1 := by
  induction l with
  | nil => simp [orderedInsert]
  | cons h t ih =>
    simp [orderedInsert]
    split <;> simp [ih]
    
-- insertion sort 
def insertionSort : List α → List α
  | [] => []
  | b :: l => orderedInsert b (insertionSort l)

-- #check insertionSort

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

-- def HfmnTree.sort (trees : List HfmnTree) : List HfmnTree := insertionSort trees

def String.freq(s : String) (c : Char) := s.data.filter (· == c) |>.length
-- #eval "hello".freq 'l' --2

def mergeTrees (t1 t2 : HfmnTree α) : HfmnTree α :=
  -- If t1 t2 is either Leaf or Node, when merged, it will be a Node
  HfmnTree.Node t1 t2 

theorem sorted_nonempty_is_nonempty {α : Type} (trees : List (HfmnTree α)) (h : trees ≠ []) :
  insertionSort trees ≠ [] := by
  have h₁ : (insertionSort trees).length = trees.length := by
    apply insertionSort_preserves_length
  have h₂: (insertionSort trees).length > 0 := by
    rw [h₁]
    simp [List.length, h]
    simp [List.length_pos_iff]
    exact h
  simp [List.ne_nil_of_length_pos, h₂]


def HfmnTree.merge (trees: List (HfmnTree α)) (h: trees ≠ []) : HfmnTree α :=
  let sorted := insertionSort trees
  have hp: sorted ≠ [] := by
    apply sorted_nonempty_is_nonempty
    exact h

  match p:sorted with
  | [] => by simp at hp
  | [t] => t
  | t1 :: t2 :: rest =>
    let newTree := mergeTrees t1 t2
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
  | HfmnTree.Node l r =>
    let leftDepth := depthAux l c (d + 1)
    if leftDepth != -1 then leftDepth else depthAux r c (d + 1)

-- Returns the depth of a character in the Huffman tree, if not found returns -1
def HfmnTree.findDepth (tree: HfmnTree α) (c: α) : Int :=
  -- Helper function to calculate the depth of a character in the tree
  depthAux tree c 0 

-- Encode a character in a Huffman tree
def HfmnTree.encodeWithDepth (c : α) : HfmnTree α → Option (BoolList × Nat)
  | .Leaf c' _ _ => 
    if c = c' then some ([], 0) else none
  | Node l r =>
    -- Has an underlying assumption, every digit increase in code, depth +=1 too, which is proved in the next theorem
    match l.encodeWithDepth c, r.encodeWithDepth c with
    | none, some (s, d) => some ([true] ++ s, d + 1)
    | some (s, d), none => some ([false] ++ s, d + 1)
    | _, _ => none

def HfmnTree.encode (c : α) (t : HfmnTree α) : Option BoolList :=
  (t.encodeWithDepth c).map (·.1)

def HfmnTree.depth (c : α) (t : HfmnTree α) : Option Nat :=
  (t.encodeWithDepth c).map (·.2)

-- Theorem: Depth is equal to the length of the code
theorem HfmnTree.depth_is_length_enc {α : Type} [DecidableEq α] (c: α) (t: HfmnTree α) (code : BoolList) :
  t.encode c = code → t.depth c = code.length := by
    cases t
    case Leaf c' w cc =>
      simp [encode, depth, encodeWithDepth]
      intro h₁ h₂
      simp [h₁, h₂]
    case Node l r =>
      match p:l.encodeWithDepth c, p':r.encodeWithDepth c with
      | none, some (s, d) =>
        simp [encode, depth, encodeWithDepth, p, p']
        intro h
        match code with
        | ch :: ct =>
          let ihr := HfmnTree.depth_is_length_enc c r ct
          simp [encode, depth, encodeWithDepth, p, p'] at ihr
          simp at h
          simp [List.length_cons, ihr, h]
      | some (s, d), none =>
        simp [encode, depth, encodeWithDepth, p, p']
        intro h
        match code with
        | ch :: ct =>
          let ihl := HfmnTree.depth_is_length_enc c l ct
          simp [encode, depth, encodeWithDepth, p, p'] at ihl
          simp at h
          simp [List.length_cons, ihl, h]
      | none, none =>
        simp [encode, depth, encodeWithDepth, p, p']
      | some (s, d), some (s', d') =>
        simp [encode, depth, encodeWithDepth, p, p']

-- #eval depthAux (HfmnTree.Leaf 'a' 1) 'a' 0 -- 0
-- #eval depthAux (HfmnTree.Node (HfmnTree.Leaf 'a' 1) (HfmnTree.Leaf 'b' 2) 3) 'a' 0

theorem HfmnTree.find_depth_is_length_enc {α : Type} (c: α) [DecidableEq α] (t: HfmnTree α) (code : BoolList) :
  t.encode c = code → t.findDepth c = code.length := by
    cases t
    case Leaf c' w cc =>
      simp [encode, HfmnTree.findDepth, encodeWithDepth]
      intro h₁ h₂
      simp [h₁, h₂, depthAux]

    case Node l r =>
      match p: l.encodeWithDepth c, p': r.encodeWithDepth c with
      | none, some (s, d) =>
        simp [encode, HfmnTree.findDepth, encodeWithDepth, p, p']
        intro h
        match code with
        | ch :: ct =>
          let ihr := find_depth_is_length_enc c r ct
          simp [encode, HfmnTree.findDepth, encodeWithDepth, p, p'] at ihr
          simp at h
          simp [List.length_cons, ihr, h, depthAux]
          
          -- TODO:
          
          sorry 

      | some (s, d), none =>
        simp [encode, HfmnTree.findDepth, encodeWithDepth, p, p']
        intro h
        match code with
        | ch :: ct =>
          let ihl := find_depth_is_length_enc c l ct
          simp [encode, HfmnTree.findDepth, encodeWithDepth, p, p'] at ihl
          simp at h
          simp [List.length_cons, depthAux]

          -- TODO:
          sorry
      | none, none =>
        simp [encode, HfmnTree.findDepth, encodeWithDepth, p, p']
      | some (s, d), some (s', d') =>
        simp [encode, HfmnTree.findDepth, encodeWithDepth, p, p']

structure Alphabet (α : Type) where
  char : α
  freq : Nat
deriving Inhabited, Repr

abbrev AlphaNumTree (α : Type) := List (Alphabet α)

def convert_input_to_alphabet (input : AlphaNumList α) : AlphaNumTree α := input.map fun a => Alphabet.mk a.1 a.2

theorem cita_ne_to_ne {α : Type} (s : AlphaNumList α) (h : s ≠ []) :
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

-- Returns the Binary Tree of the Huffman encoding, without the encoded strings
def HfmnTree.tree (huffinput : AlphaNumList α) : HfmnTree α :=
  if p:huffinput.isEmpty then -- Handle []
    HfmnTree.Leaf HfmnType.default 0
  else
    have huffinput_nonempty : huffinput ≠ [] := by intro h₁; rw [h₁] at p; simp at p        

    let input := convert_input_to_alphabet huffinput
    have hi : input ≠ [] := by
      apply cita_ne_to_ne
      exact huffinput_nonempty 

    let leaves : List (HfmnTree α) := input.map (fun a => HfmnTree.Leaf a.char a.freq)
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

    HfmnTree.merge sorted (by simp [sorted_nonempty] )

-- Encode a string in a Huffman tree
def HfmnTree.encodedList (huffinput : AlphaNumList α) : BoolEncList α :=
  let tree := HfmnTree.tree huffinput
  let input := convert_input_to_alphabet huffinput
  input.map (fun a => 
    let encoding := tree.encode a.char
    (a.char, encoding.getD [])  -- getD provides a default value
  )
-- #eval (HfmnTree.encodedList eg₁)
--   [('a', [false]),
--   ('b', [true, false, true]),
--   ('c', [true, false, false]),
--   ('d', [true, true, true]),
--   ('e', [true, true, false, true]),
--   ('f', [true, true, false, false])]

def Huffmann.leastEncodedData (huffinput : AlphaNumList α) : Nat :=
  let encoded := HfmnTree.encodedList huffinput
  huffinput.foldl (fun acc (a, count) => 
    match encoded.find? (fun (x, _) => x == a) with
    | some (_, code) => acc + code.length * count
    | none => acc  -- or handle missing case as needed
  ) 0

-- #eval Huffmann.leastEncodedData eg₁ -- 224

-- #eval HfmnTree.manual_depth (HfmnTree.tree eg₁ ) 'a' -- 1

-- Valid path function, considers a path to the leaf as valid, path to Node as invalid
def HfmnTree.valid_leaf_or_node (bl: BoolList) (tree: HfmnTree α) : Bool :=
  match tree with
  | HfmnTree.Leaf _ _ _ => bl.isEmpty
  | Node l r =>
    match bl with
    | [] => false
    | b :: bs =>
      if b then valid_leaf_or_node bs r
      else valid_leaf_or_node bs l

-- #eval HfmnTree.valid_path_of_tree [true, false, true] (HfmnTree.tree eg₁) -- true

-- chars returns the set of characters in the tree
def HfmnTree.chars: HfmnTree α → List α
  | Leaf c _ _ => [c]
  | Node l r => l.chars ++ r.chars

-- Helper list intersection function
def List.inter(l₁ l₂ : List α) : List α :=
  l₁.filter (· ∈ l₂)

def HfmnTree.charInTree (t : HfmnTree α) (c : α) : Bool :=
  t.chars.contains c

def disjointChars (t : HfmnTree α) : Prop :=
  match t with 
  | HfmnTree.Leaf _ _ _ => True
  | HfmnTree.Node l r =>
    [] = l.chars.inter r.chars

-- Theorem: Merge of two trees with disjoint characters is disjoint
theorem merge_preserves_disjoint_chars {α : Type} [DecidableEq α] (l r : HfmnTree α) :
  disjointChars l → disjointChars r → l.chars.inter r.chars = [] → disjointChars (mergeTrees l r) := by
  intro h₁ h₂ h₃
  simp [mergeTrees, disjointChars] 
  assumption

-- the characters in any left and right tree are disjoint
theorem left_right_tree_disjoint_chars {α : Type} [DecidableEq α] [HfmnType α](huffinput: AlphaNumList α) :
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
    
-- check if 2 BoolEncList are prefix free of each other
def checkPrefixfree (bl₁ bl₂: BoolList) : Bool :=
  bl₁ ≠ bl₂ ∧ ¬(bl₁.isPrefixOf bl₂ ∨ bl₂.isPrefixOf bl₁)

-- #eval checkPrefixfree [true, false, false] [true, false] -- false

-- Check if the encoded list is prefix free, i.e. compares each encoded string with all other strings
def isPrefixfree : BoolEncList α → Bool
  | [] => true
  | (_, bl) :: rest => rest.all (fun al => checkPrefixfree bl al.2) && isPrefixfree rest

def prefixFreeTree (huffinput : AlphaNumList α) : Prop :=
  let enc_list := HfmnTree.encodedList huffinput
  isPrefixfree enc_list

-- #eval isPrefixfree (HfmnTree.encoded_tree eg₁).1 -- true

-- #eval isPrefixfree (conv_str_freq_boollist [('a', "0"),('b', "101"),('c', "100"),('d', "011"),('e', "1101"),('f', "1100")]) -- false

def HfmnTree.decode (enc_boolinput : BoolList) (enc_huffinput : List (α × BoolList)) : Option α :=
  enc_huffinput.find? (λ (_, s) => s = enc_boolinput) |>.map (·.1)

-- #eval HfmnTree.decode "1" ( HfmnTree.encoded_tree eg₁ ).1 -- none
-- #eval HfmnTree.decode "0" ( HfmnTree.encoded_tree eg₁ ).1 -- some 'a'
