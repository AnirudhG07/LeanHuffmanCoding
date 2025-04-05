/-
# This contains the definition of a huffmann tree, a binary tree used to encode data.
We will initially define the binary treee for encoding and get the minimum encoded data for the list of input data.
-/

abbrev BoolList := List Bool
abbrev AlphaNumList := List (Char × Nat)
abbrev BoolEncList := List (Char × BoolList)
abbrev CharEncodedList := List (Char × String)

def eg₁ : AlphaNumList := [('a', 45),('b', 13),('c', 12),('d', 16),('e', 9),('f', 5)]

def conv_enc_boollist (s : String) : BoolList :=
  s.toList.map (λ c => if c = '1' then true else false)

def conv_str_freq_boollist (s : CharEncodedList) : BoolEncList :=
  s.map (λ (c, str) => (c, conv_enc_boollist str))

-- Huffman Tree Definition
inductive HfmnTree where
  | node (left : HfmnTree) (right : HfmnTree) (weight : Nat)
  | Leaf (c : Char) (weight : Nat) (code : BoolList := [])
deriving Inhabited, Repr

-- Theorem: Strings inputs in a Huffman tree are only at the leaves
theorem inputs_at_leaves (tree : HfmnTree) :
  ∀ (c : Char), (∃ (w : Nat) (code : BoolList), tree = HfmnTree.Leaf c w code) ↔ 
  (∃ (leaf : HfmnTree), (∃ (w : Nat) (code : BoolList), leaf = HfmnTree.Leaf c w code) ∧ tree = leaf) := by
  intro c
  constructor
  -- Forward direction: If a character exists in the tree, it must be in a Leaf
  · intro h
    rcases h with ⟨w, code, h⟩
    exists HfmnTree.Leaf c w code
    simp [h]
  -- Backward direction: If a Leaf exists with the character, then the character is in the tree
  · intro h
    rcases h with ⟨leaf, ⟨w, code, h_leaf⟩, h_tree⟩
    exists w, code
    rw [h_tree, h_leaf]

def HfmnTree.weight : HfmnTree → Nat
  | Leaf _ w _ => w
  | node _ _ w => w

-- Comparison function for Huffman trees weights
def HfmnTree.compare (s s' : HfmnTree) : Ordering :=
  Ord.compare s.weight s'.weight

instance : Ord HfmnTree where
  compare := HfmnTree.compare

-- Insert an element in a way that does not break the order of the sorted list.
def orderedInsert {α : Type} [Ord α] (a : α) : List α → List α
  | [] => [a]
  | b :: l =>
    match compare a b with
    | .lt => a :: b :: l
    | _ => b :: orderedInsert a l

-- insertion sort 
def insertionSort {α : Type} [Ord α] : List α → List α
  | [] => []
  | b :: l => orderedInsert b (insertionSort l)

-- #check insertionSort

def HfmnTree.sort (trees : List HfmnTree) : List HfmnTree := insertionSort trees

def String.freq (s : String) (c : Char) := s.data.filter (· == c) |>.length
-- #eval "hello".freq 'l' --2

partial def HfmnTree.merge (trees : List HfmnTree) : List HfmnTree :=
  let sorted := HfmnTree.sort trees
  match sorted with
  | [] => []
  | [tree] => [tree]
  | t1 :: t2 :: rest =>
    let t' := HfmnTree.node t1 t2 (t1.weight + t2.weight)
    HfmnTree.merge (t' :: rest)

def eg : BoolList := [true, false, true, false]

def depthAux (tree: HfmnTree) (c: Char) (d: Int) : Int :=
  -- c is the character to find, d is the depth in the tree
  match tree with
  | HfmnTree.Leaf c' _ _ => if c = c' then d else -1
  | HfmnTree.node l r _ =>
    let leftDepth := depthAux l c (d + 1)
    if leftDepth != -1 then leftDepth else depthAux r c (d + 1) 

-- Returns the depth of a character in the Huffman tree, if not found returns -1
def HfmnTree.findDepth (tree: HfmnTree) (c: Char) : Int :=
  -- Helper function to calculate the depth of a character in the tree
  depthAux tree c 0 

-- Encode a character in a Huffman tree
def HfmnTree.encodeWithDepth (c : Char) : HfmnTree → Option (BoolList × Nat)
  | .Leaf c' _ _ => 
    if c = c' then some ([], 0) else none
  | .node l r _w =>
    -- Has an underlying assumption, every digit increase in code, depth +=1 too, which is proved in the next theorem
    match l.encodeWithDepth c, r.encodeWithDepth c with
    | none, some (s, d) => some ([true] ++ s, d + 1)
    | some (s, d), none => some ([false] ++ s, d + 1)
    | _, _ => none

def HfmnTree.encode (c : Char) (t : HfmnTree) : Option BoolList :=
  (t.encodeWithDepth c).map (·.1)

def HfmnTree.depth (c : Char) (t : HfmnTree) : Option Nat :=
  (t.encodeWithDepth c).map (·.2)

theorem HfmnTree.depth_is_length_enc (c: Char) (t: HfmnTree) (code : BoolList) :
  t.encode c = code → t.depth c = code.length := by
    cases t
    case Leaf c' w cc =>
      simp [encode, depth, encodeWithDepth]
      intro h₁ h₂
      simp [h₁, h₂]
    case node l r _w =>
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
#eval depthAux (HfmnTree.node (HfmnTree.Leaf 'a' 1) (HfmnTree.Leaf 'b' 2) 3) 'a' 0

theorem HfmnTree.find_depth_is_length_enc (c: Char) (t: HfmnTree) (code : BoolList) :
  t.encode c = code → t.findDepth c = code.length := by
    cases t
    case Leaf c' w cc =>
      simp [encode, HfmnTree.findDepth, encodeWithDepth]
      intro h₁ h₂
      simp [h₁, h₂, depthAux]

    case node l r _w =>
      match p: l.encodeWithDepth c, p': r.encodeWithDepth c with
      | none, some (s, d) =>
        simp [encode, HfmnTree.findDepth, encodeWithDepth, p, p']
        intro h
        match code with
        | ch :: ct =>
          let ihr := find_depth_is_length_enc c r ct
          simp [encode, HfmnTree.findDepth, encodeWithDepth, p, p'] at ihr
          simp at h
          simp [List.length_cons, ihr, h]
          simp [depthAux]
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
          simp [List.length_cons, ihl, h]
          -- TODO:
          sorry

      | none, none =>
        simp [encode, HfmnTree.findDepth, encodeWithDepth, p, p']
      | some (s, d), some (s', d') =>
        simp [encode, HfmnTree.findDepth, encodeWithDepth, p, p']

structure Alphabet where
  char : Char
  freq : Nat
deriving Inhabited, Repr

abbrev AlphaNumTree := List Alphabet

def convert_input_to_alphabet (input : AlphaNumList) : AlphaNumTree := input.map fun a => Alphabet.mk a.1 a.2

-- Returns the Binary Tree of the Huffman encoding, without the encoded strings
def HfmnTree.tree (huffinput : AlphaNumList) : HfmnTree :=
  let input := convert_input_to_alphabet huffinput
  let leaves : List HfmnTree := input.map (fun a => HfmnTree.Leaf a.char a.freq)
  let tree : HfmnTree := HfmnTree.merge leaves |>.head!
  tree

-- #eval HfmnTree.tree eg₁

-- Encode a string in a Huffman tree
def HfmnTree.encoded_tree (huffinput : AlphaNumList) : (BoolEncList × HfmnTree):=
  let tree := HfmnTree.tree huffinput
  let input := convert_input_to_alphabet huffinput
  let enc_list := input.map (fun a => (a.char, tree.encode a.char |>.get!))
  -- Add this to the tree
  let rec addCode (tree : HfmnTree) (code : BoolList) : HfmnTree :=
    match tree with
    | HfmnTree.Leaf c w _ => HfmnTree.Leaf c w code
    | HfmnTree.node l r w => HfmnTree.node (addCode l (code ++ [false])) (addCode r (code ++ [true])) w

  let tree' := addCode tree []
  (enc_list, tree')

-- #eval (HfmnTree.encoded_tree eg₁).1 =
--   [('a', [false]),
--   ('b', [true, false, true]),
--   ('c', [true, false, false]),
--   ('d', [true, true, true]),
--   ('e', [true, true, false, true]),
--   ('f', [true, true, false, false])]

-- #eval (HfmnTree.encoded_tree [('B', 7),('C', 6),('A', 3),('D', 1),('E', 1),]).1 = 
-- [('B', [false]),
--  ('C', [true, true]),
--  ('A', [true, false, true]),
--  ('D', [true, false, false, true]),
--  ('E', [true, false, false, false])]

def Huffmann.least_encoded_data (huffinput : AlphaNumList) : Nat :=
  let encoded := (HfmnTree.encoded_tree huffinput).1
  huffinput.foldl (fun acc a => acc + (encoded.find? (·.1 = a.1) |>.get!.2).length * a.2) 0

-- #eval Huffmann.least_encoded_data eg₁ -- 224

-- #eval HfmnTree.manual_depth (HfmnTree.tree eg₁ ) 'a' -- 1

-- Valid path function, considers a path to the leaf as valid, path to Node as invalid
def HfmnTree.valid_leaf_or_node (bl: BoolList) (tree: HfmnTree) : Bool :=
  match tree with
  | HfmnTree.Leaf _ _ _ => bl.isEmpty
  | HfmnTree.node l r _ =>
    match bl with
    | [] => false
    | b :: bs =>
      if b then valid_leaf_or_node bs r
      else valid_leaf_or_node bs l

-- #eval HfmnTree.valid_path_of_tree [true, false, true] (HfmnTree.tree eg₁) -- true

def HfmnTree.charInTree (tree: HfmnTree) (c: Char) : Bool :=
  match tree with
  | HfmnTree.Leaf c' _ _ => c = c'
  | HfmnTree.node l r _ =>
    HfmnTree.charInTree l c || HfmnTree.charInTree r c

-- the characters in any left and right tree are disjoint
theorem left_right_tree_disjoint_chars (tree: HfmnTree) :

-- check if 2 BoolEncList are prefix free of each other
def checkPrefixfree (bl₁ bl₂: BoolList) : Bool :=
  bl₁ ≠ bl₂ ∧ ¬(bl₁.isPrefixOf bl₂ ∨ bl₂.isPrefixOf bl₁)

-- #eval checkPrefixfree [true, false, false] [true, false] -- false

-- Check if the encoded list is prefix free, i.e. compares each encoded string with all other strings
def isPrefixfree : BoolEncList → Bool
  | [] => true
  | (_, bl) :: rest => rest.all (fun al => checkPrefixfree bl al.2) && isPrefixfree rest

-- #eval isPrefixfree (HfmnTree.encoded_tree eg₁).1 -- true

-- #eval isPrefixfree (conv_str_freq_boollist [('a', "0"),('b', "101"),('c', "100"),('d', "011"),('e', "1101"),('f', "1100")]) -- false

def HfmnTree.decode (enc_boolinput: BoolList) (enc_huffinput: BoolEncList) : Option Char :=
  -- Iterate through the list and find the matching encoded string
  enc_huffinput.find? (λ (_, s) => s = enc_boolinput) |>.map (·.1)

-- #eval HfmnTree.decode "1" ( HfmnTree.encoded_tree eg₁ ).1 -- none
-- #eval HfmnTree.decode "0" ( HfmnTree.encoded_tree eg₁ ).1 -- some 'a'
