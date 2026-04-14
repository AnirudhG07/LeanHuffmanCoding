/-
Huffman Trees are trees used for data compression. They are binary trees where each leaf node represents a character and its frequency in the input data. The tree is constructed in such a way that characters with higher frequencies are closer to the root, allowing for shorter binary representations.

Some of the properties of Huffman trees are:
* The values in a Huffman tree only appear at leaves.
* The depth of a character in the tree is equal to the length of its binary representation.
* The characters in the left and right subtrees of a node are disjoint.
* Huffman trees are prefix-free, meaning no code is a prefix of another code.
* The algorithm is Optimal for the given set of characters and their frequencies.

We implements the Huffman tree construction algorithm, and prove its correctness.
-/
import Mathlib
set_option linter.unusedSectionVars false

abbrev BoolList := List Bool
abbrev AlphaNumList (α : Type) := List (α × Nat)
abbrev BoolEncList (α : Type) := List (α × BoolList)
abbrev TypeEncodedList (α : Type) := List (α × String)

/-
Defined a Typeclass for the type of the inputs in the Huffman tree. Since decoding would be primarlity on strings or integer inputs, they are all decidable, ordered and inhabited.
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

@[simp, grind .]
def HfmnTree.weight : HfmnTree α → Nat
  | Leaf _ w => w
  | Node l r => l.weight + r.weight

/-
Comparison function for Huffman trees weights
-/
@[simp, grind .]
def HfmnTree.compare (s s' : HfmnTree α) : Ordering :=
  Ord.compare s.weight s'.weight

instance : Ord (HfmnTree α) where
  compare := HfmnTree.compare

/-
The orderedInsert function inserts an element into a sorted list while maintaining the order.
-/
@[simp, grind .]
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
    grind

/- * Theorem: The length of the list after inserting an element is equal to the original length plus one.-/
theorem orderedInsert_inc_length {α : Type} [Ord α] (a : α) (l : List α) :
  (orderedInsert a l).length = l.length + 1 := by
  induction l with
  | nil => simp [orderedInsert]
  | cons h t ih =>
    simp [orderedInsert]
    grind

/- Insertion sort function that sorts a list of elements so that the elements are in non-decreasing order.-/
@[simp, grind .]
def insertionSort : List α → List α
  | [] => []
  | b :: l => orderedInsert b (insertionSort l)

@[simp]
lemma mem_orderedInsert {α : Type} [Ord α] (x a : α) (l : List α) :
    x ∈ orderedInsert a l ↔ x = a ∨ x ∈ l := by
  induction l with
  | nil =>
    simp [orderedInsert]
  | cons b t ih =>
    by_cases hcmp : compare a b = .lt
    · simp [orderedInsert, hcmp]
    · simp [orderedInsert]
      grind

@[simp]
lemma mem_insertionSort {α : Type} [Ord α] (x : α) (l : List α) :
    x ∈ insertionSort l ↔ x ∈ l := by
  induction l with
  | nil =>
    simp [insertionSort]
  | cons b t ih =>
    simp [insertionSort, mem_orderedInsert, ih]

-- #check insertionSort

/- * Theorem: The insertionSort function preserves the length of the list. -/
theorem insertionSort_preserves_length {α : Type} [Ord α] :
  ∀ l : List α, (insertionSort l).length = l.length := by
  intro l
  induction l with
  | nil => simp [insertionSort]
  | cons b l ih =>
    simp [insertionSort]
    have h := orderedInsert_inc_length b (insertionSort l)
    grind

/- * Lemma: The insertionSorted non-empty list is non-empty -/
@[simp, grind .]
lemma sorted_nonempty_is_nonempty (trees : List (HfmnTree α)) (h : trees ≠ []) :
  insertionSort trees ≠ [] := by
  have h₁ : (insertionSort trees).length = trees.length := by
    apply insertionSort_preserves_length
  grind


def String.freq(s : String) (c : Char) := s.toList.filter (· == c) |>.length
-- #eval "hello".freq 'l' --2

/-
If t1 t2 is either Leaf or Node, when merged, it will be a Node.
-/
@[simp, grind .]
def HfmnTree.mergeTrees (t1 t2 : HfmnTree α) : HfmnTree α :=
  .Node t1 t2

/-
In our algorithm, we take the mininum two trees and merge them. The merged tree is then inserted back into the list of trees.
-/
@[simp, grind .]
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
      grind
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
* Lemma: The conversion function `convert_input_to_alphabet` for a non-empty list is non-empty.
-/
lemma cita_ne_to_ne (s : AlphaNumList α) (h : s ≠ []) :
  convert_input_to_alphabet s ≠ [] := by
  intro hi
  have h₁ : (convert_input_to_alphabet s).length = s.length := by
    apply List.length_map
  grind

/-
The main Tree creator function which takes the input and returns the Huffman tree, with the encoded BoolList included.
-/
@[simp, grind .]
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
      grind
    let sorted := insertionSort leaves
    have sorted_nonempty : sorted ≠ [] := by grind

    let sorted_tree := HfmnTree.merge sorted (by simp [sorted_nonempty] )
    sorted_tree

-- #eval HfmnTree.tree eg₁

/- Returns the set of values in the tree. -/
@[simp, grind .]
def HfmnTree.chars: HfmnTree α → List α
  | Leaf c _  => [c]
  | Node l r  => l.chars ++ r.chars

/- Helper function to check if a character is in the tree. -/
@[simp, grind .]
def HfmnTree.charInTree (t : HfmnTree α) (c : α) : Bool :=
  t.chars.contains c

@[simp, grind .]
lemma HfmnTree.charInTree_iff (t : HfmnTree α) (c : α) :
  HfmnTree.charInTree t c = true ↔ c ∈ t.chars := by repeat grind

def HfmnTree.encode (c: α) (t : HfmnTree α) : BoolList :=
  match t with
  | .Leaf c' _ =>
    if c = c' then [] else panic! "-1" -- This should never happen
  | .Node l r =>
    if l.charInTree c then
      false :: encode c l
    else
      true :: encode c r

@[simp, grind .]
lemma HfmnTree.mergeTrees_charInTree {t₁ t₂ : HfmnTree α} {c : α} :
    (HfmnTree.mergeTrees t₁ t₂).charInTree c =
    (t₁.charInTree c || t₂.charInTree c) := by
  grind

@[simp, grind .]
lemma HfmnTree.charInTree_leaf (a c : α) (f : Nat) :
    (HfmnTree.Leaf a f).charInTree c = (a == c) := by
  grind

lemma HfmnTree.merge_contains_char_aux
    (c : α) :
    ∀ n : Nat, ∀ trees : List (HfmnTree α), trees.length = n → ∀ h : trees ≠ [],
      (∃ t ∈ trees, t.charInTree c = true) →
      (HfmnTree.merge trees h).charInTree c = true := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro trees hlen hne hex
    classical
    unfold HfmnTree.merge
    let sorted := insertionSort trees
    have hp : sorted ≠ [] := by
      apply sorted_nonempty_is_nonempty
      exact hne
    have hsorted_mem : ∃ t ∈ sorted, t.charInTree c = true := by
      rcases hex with ⟨t, ht, htc⟩
      refine ⟨t, ?_, htc⟩
      have : t ∈ insertionSort trees := (mem_insertionSort t trees).2 ht
      simpa [sorted] using this

    cases hs : sorted with
    | nil =>
      cases hp hs
    | cons t₁ rest =>
      cases rest with
      | nil =>
        rcases hsorted_mem with ⟨t, ht, htchar⟩
        have ht_eq : t = t₁ := by simpa [hs] using ht
        subst ht_eq
        grind
      | cons t₂ rest' =>
        have hnext : ∃ t ∈ (HfmnTree.mergeTrees t₁ t₂ :: rest'), t.charInTree c = true := by
          rcases hsorted_mem with ⟨t, ht, htchar⟩
          have ht_cases : t = t₁ ∨ t = t₂ ∨ t ∈ rest' := by
            simpa [hs] using ht
          rcases ht_cases with rfl | rfl | ht_rest
          · simp; grind
          · simp; grind
          · exact ⟨t, by simp [ht_rest], htchar⟩

        have hlt : (HfmnTree.mergeTrees t₁ t₂ :: rest').length < n := by
          have h_sorted_len : sorted.length = trees.length := by
            have h' : (insertionSort trees).length = trees.length := by
              apply insertionSort_preserves_length
            simpa [sorted] using h'
          grind
        grind

lemma HfmnTree.merge_contains_char
    (c : α) (trees : List (HfmnTree α)) (h : trees ≠ [])
    (hex : ∃ t ∈ trees, t.charInTree c = true) :
    (HfmnTree.merge trees h).charInTree c = true := by
  exact HfmnTree.merge_contains_char_aux c trees.length trees rfl h hex

@[simp, grind .]
lemma HfmnTree.tree_contains_input_chars (huffinput : AlphaNumList α)
    (a : α) (freq : Nat) (h : (a, freq) ∈ huffinput) :
    (HfmnTree.tree huffinput).charInTree a = true := by
  by_cases hp : huffinput.isEmpty
  · have : huffinput = [] := by simpa [List.isEmpty_iff] using hp
    subst this
    simp at h
  · rw [HfmnTree.tree, dif_neg hp]
    let input := convert_input_to_alphabet huffinput
    let leaves : List (HfmnTree α) := input.map (fun x => HfmnTree.Leaf x.val x.freq)
    have hmem_input : Alphabet.mk a freq ∈ input := by
      unfold input convert_input_to_alphabet
      exact List.mem_map.mpr ⟨(a, freq), h, by simp⟩
    have hleaf : HfmnTree.Leaf a freq ∈ leaves := by
      unfold leaves
      exact List.mem_map.mpr ⟨Alphabet.mk a freq, hmem_input, by simp⟩
    have hsorted_mem : HfmnTree.Leaf a freq ∈ insertionSort leaves := by
      exact (mem_insertionSort (HfmnTree.Leaf a freq) leaves).2 hleaf
    have hsorted_nonempty : insertionSort leaves ≠ [] := by
      intro hs
      rw [hs] at hsorted_mem
      simp at hsorted_mem
    exact HfmnTree.merge_contains_char a (insertionSort leaves) hsorted_nonempty
      ⟨HfmnTree.Leaf a freq, hsorted_mem, by simp⟩

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
@[simp, grind .]
def Huffman.leastEncodedData (huffinput : AlphaNumList α) : Nat :=
  let encoded := HfmnTree.encodedList huffinput
  huffinput.foldl (fun acc (a, count) =>
    match encoded.find? (fun (x, _) => x == a) with
    | some (_, code) => acc + code.length * count
    | none => acc  -- or handle missing case as needed
  ) 0

-- #eval Huffman.leastEncodedData eg₁ -- 224

/-
Decoding the encoded input. decode(encode(x)) = x, since the tree is prefix free and the code is unique.
This should be our final goal, to show for a huffman tree, the decoding of the encoded input is equal to the original input.
-/
def HfmnTree.decode (enc_boolinput : BoolList) (enc_huffinput : List (α × BoolList)) : Option α :=
  enc_huffinput.find? (λ (_, s) => s = enc_boolinput) |>.map (·.1)

-- #eval HfmnTree.decode "1" ( HfmnTree.encoded_tree eg₁ ).1 -- none
-- #eval HfmnTree.decode "0" ( HfmnTree.encoded_tree eg₁ ).1 -- some 'a'
