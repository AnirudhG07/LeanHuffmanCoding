/-
# This contains the definition of a huffmann tree, a binary tree used to encode data.
We will initially define the binary treee for encoding and get the minimum encoded data for the list of input data.
-/
/-- Insert an element in a way that
does not break the order of the sorted list. -/
def orderedInsert {α : Type} [Ord α] (a : α) : List α → List α
  | [] => [a]
  | b :: l =>
    match compare a b with
    | .lt => a :: b :: l
    | _ => b :: orderedInsert a l

/-- insertion sort -/
def insertionSort {α : Type} [Ord α] : List α → List α
  | [] => []
  | b :: l => orderedInsert b (insertionSort l)

#check insertionSort

/-- Huffman Tree -/
inductive HfmnTree where
  | node (left : HfmnTree) (right : HfmnTree) (weight : Nat)
  | Leaf (c : Char) (weight : Nat)
deriving Inhabited, Repr

def HfmnTree.weight : HfmnTree → Nat
  | Leaf _ w => w
  | node _ _ w => w

-- Comparison function for Huffman trees weights
def HfmnTree.compare (s s' : HfmnTree) : Ordering :=
  let w := s.weight
  let w' := s'.weight
  Ord.compare w w'

instance : Ord HfmnTree where
  compare := HfmnTree.compare

def HfmnTree.sort (trees : List HfmnTree) : List HfmnTree := insertionSort trees

def String.freq (s : String) (c : Char) := s.data.filter (· == c) |>.length
-- #eval "hello".freq 'l' --2

def String.toLeaves (s : String) : List HfmnTree :=
  let allChars : List Char := s.data.eraseDups
  allChars.map fun c => HfmnTree.Leaf c (s.freq c)

partial def HfmnTree.merge (trees : List HfmnTree) : List HfmnTree :=
  let sorted := HfmnTree.sort trees
  match sorted with
  | [] => []
  | [tree] => [tree]
  | t1 :: t2 :: rest =>
    let t' := HfmnTree.node t1 t2 (t1.weight + t2.weight)
    HfmnTree.merge (t' :: rest)


abbrev Code := String

def HfmnTree.encode (c : Char) : HfmnTree → Option Code
  | .Leaf c' _ => if c = c' then some "" else none
  | .node l r _w =>
    match l.encode c, r.encode c with
    | none, some s => some ("1" ++ s)
    | some s, none => some ("0" ++ s)
    | _, _ => none

def huffman (input : List (Char × Nat)) : List (Char × Code) :=
  let leaves : List HfmnTree := input.map (fun (c, w) => HfmnTree.Leaf c w)
  let tree : HfmnTree := HfmnTree.merge leaves |>.head!
  input.map (fun (c, _) => (c, tree.encode c |>.get!))

def Huffmann.least_encoded_data (input : List (Char × Nat)) : Nat :=
  let encoded := huffman input
  input.foldl (fun acc (c, w) => acc + (encoded.find? (·.1 = c) |>.get!.2).length * w) 0
    

-- #eval huffman [('a', 45),('b', 13),('c', 12),('d', 16),('e', 9),('f', 5)] =
--   [('a', "0"),('b', "101"),('c', "100"),('d', "111"),('e', "1101"),('f', "1100")]
--
-- #eval huffman [('B', 7),('C', 6),('A', 3),('D', 1),('E', 1),] =
--   [('B', "0"), ('C', "11"), ('A', "101"), ('D', "1001"), ('E', "1000")]
--
-- #eval Huffmann.least_encoded_data [('a', 45),('b', 13),('c', 12),('d', 16),('e', 9),('f', 5)] -- 224
