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
import Huffman.HfmnTree_Construction
import Mathlib
set_option linter.unusedSectionVars false

abbrev BoolList := List Bool
abbrev AlphaNumList (α : Type) := List (α × Nat)
abbrev BoolEncList (α : Type) := List (α × BoolList)
abbrev TypeEncodedList (α : Type) := List (α × String)

namespace AlphaNumList

variable {α : Type}

/-- Input alphabet as a list of symbols (first projections of `(symbol, freq)` pairs). -/
@[simp]
def symbols (input : AlphaNumList α) : List α :=
  input.map Prod.fst

/-- Sum of all frequencies in the input table. -/
@[simp]
def totalFreq (input : AlphaNumList α) : Nat :=
  input.foldl (fun acc x => acc + x.2) 0

/-- No duplicate symbols in the input table. -/
def WellFormed (input : AlphaNumList α) : Prop :=
  input.symbols.Nodup

/-- All frequencies are strictly positive. -/
def Positive (input : AlphaNumList α) : Prop :=
  ∀ a f, (a, f) ∈ input → 0 < f

/-- Canonical bundle used in final theorem assumptions. -/
def Valid (input : AlphaNumList α) : Prop :=
  WellFormed input ∧ Positive input

/-- Lookup frequency of symbol `a` in an input table (`0` if absent). -/
@[simp]
def lookupFreq [DecidableEq α] (input : AlphaNumList α) (a : α) : Nat :=
  match input.find? (fun x => x.1 == a) with
  | some (_, f) => f
  | none => 0

@[simp]
lemma symbols_nil : symbols ([] : AlphaNumList α) = [] := rfl

@[simp]
lemma symbols_cons (x : α × Nat) (xs : AlphaNumList α) :
    symbols (x :: xs) = x.1 :: symbols xs := rfl

@[simp]
lemma totalFreq_nil : totalFreq ([] : AlphaNumList α) = 0 := rfl

lemma totalFreq_cons (x : α × Nat) (xs : AlphaNumList α) :
    totalFreq (x :: xs) = x.2 + totalFreq xs := by
  unfold totalFreq
  have haux : ∀ (ys : AlphaNumList α) (n : Nat),
      List.foldl (fun acc x => acc + x.2) n ys =
      n + List.foldl (fun acc x => acc + x.2) 0 ys := by
    intro ys n
    induction ys generalizing n with
    | nil =>
        simp
    | cons y ys ih =>
      grind
  simpa using haux xs x.2

lemma mem_symbols_iff {a : α} {input : AlphaNumList α} :
    a ∈ symbols input ↔ ∃ f, (a, f) ∈ input := by
  constructor
  · intro ha
    exact List.mem_map.1 ha |> fun ⟨x, hx, hxeq⟩ => by grind
  · intro h
    rcases h with ⟨f, hf⟩
    exact List.mem_map.2 ⟨(a, f), hf, rfl⟩

lemma not_mem_symbols_iff {a : α} {input : AlphaNumList α} :
    a ∉ symbols input ↔ ∀ f, (a, f) ∉ input := by
  constructor
  · intro hnot f hf
    exact hnot ((mem_symbols_iff).2 ⟨f, hf⟩)
  · intro hnot hmem
    rcases (mem_symbols_iff).1 hmem with ⟨f, hf⟩
    exact hnot f hf

end AlphaNumList

/-
Defined a Typeclass for the type of the inputs in the Huffman tree. Since decoding would be primarlity on strings or integer inputs, they are all decidable, ordered and inhabited.
-/
class HfmnType (α : Type) [DecidableEq α]  where
  default : α

variable {α : Type} [DecidableEq α] [Inhabited α] [Ord α] [HfmnType α]

instance [Inhabited α] [DecidableEq α] : HfmnType α where
  default := default

/-!
# Proof-side Huffman construction

The public `HfmnTree` API is backed by the proof-side `HuffmanTree` algorithm
defined here, so construction lives with the library-facing tree module rather
than in a separate proof-only file.
-/

/--
Condition stating that a forest `ts` is sorted by weight.
-/
def sortedByWeight {α} : Forest α → Prop
  | [] => true
  | [_] => true
  | t1 :: t2 :: ts => weight t1 ≤ weight t2 ∧ sortedByWeight (t2 :: ts)

/--
If a forest `(t :: ts)` is sorted by weight, then its tail is also sorted by weight.
-/
@[simp]
lemma sortedByWeight_Cons_imp_sortedByWeight {α}
  (t : HuffmanTree α) (ts : Forest α) :
  sortedByWeight (t :: ts) → sortedByWeight ts := by
  cases ts <;> simp [sortedByWeight]

/--
If a forest `(t :: ts)` is sorted by weight, then every tree
in the tail has weight greater than or equal to the weight of `t`.
`t` has minimal weight among all trees in the forest.
-/
@[simp]
lemma sortedByWeight_Cons_imp_forall_weight_ge {α}
  (t : HuffmanTree α) (ts : Forest α) :
  sortedByWeight (t :: ts) → ∀ u ∈ ts, weight u ≥ weight t := by
  induction ts generalizing t <;> grind [sortedByWeight]

/--
The weight that is stored in the node.
-/
def cachedWeight {α} : HuffmanTree α → Nat
  | HuffmanTree.leaf w _ => w
  | HuffmanTree.node w _ _ => w

/--
For trees of height zero, the cached weight is the actual weight.
-/
@[simp]
lemma height_0_imp_cachedWeight_eq_weight {α} (t : HuffmanTree α) :
  height t = 0 → cachedWeight t = weight t := by
  aesop (add norm [weight, cachedWeight, height])

/--
Combine two Huffman trees into a single tree.

The final tree has as children the input trees and sum of their weights as its weight.
-/
def uniteTrees {α} (t1 t2 : HuffmanTree α) : HuffmanTree α :=
  HuffmanTree.node (cachedWeight t1 + cachedWeight t2) t1 t2

/--
The alphabet of a united tree is the union of the alphabets of its input trees.
-/
@[simp]
lemma alphabet_uniteTrees {α : Type} [DecidableEq α] (t1 t2 : HuffmanTree α) :
  alphabet (uniteTrees t1 t2) = alphabet t1 ∪ alphabet t2 := by
  simp [uniteTrees, alphabet]

/--
Uniting two consistent trees with disjoint alphabets creates a consistent tree.
-/
@[simp]
lemma consistent_uniteTrees {α : Type} [DecidableEq α] (t1 t2 : HuffmanTree α)
  (h_consistent_t1 : consistent t1) (h_consisstent_t2 : consistent t2)
  (h_disj : alphabet t1 ∩ alphabet t2 = ∅) :
  consistent (uniteTrees t1 t2) := by
  simp_all [uniteTrees, consistent]

@[simp]
lemma freq_uniteTrees {α : Type} [DecidableEq α] (t1 t2 : HuffmanTree α) (a : α) :
  freq (uniteTrees t1 t2) a = freq t1 a + freq t2 a := by
  simp [uniteTrees, freq]

/--
Insert a Huffman tree into a forest, preserving the ordering by weight.
-/
def insortTree {α} (u : HuffmanTree α) : List (HuffmanTree α) → List (HuffmanTree α)
  | [] => [u]
  | t :: ts =>
      if cachedWeight u ≤ cachedWeight t then
        u :: t :: ts
      else
        t :: insortTree u ts

/--
Inserting a tree into a list `ts` using `insortTree`
increases the length of the list by one.
-/
@[simp]
lemma insortTree_length {α} (u : HuffmanTree α) (ts : List (HuffmanTree α)) :
    (insortTree u ts).length = ts.length + 1 := by
  induction ts <;> aesop (add norm [insortTree])

/--
Inserting a tree into any list `ts` using `insortTree`
produces a non-empty list.
-/
@[simp]
lemma insortTree_ne_nil {α} (u : HuffmanTree α) (ts : List (HuffmanTree α)) :
    insortTree u ts ≠ [] := by
  grind [insortTree, insortTree_length]

/--
Inserting a tree into a forest joins its alphabet to the forest alphabet.
-/
@[simp]
lemma alphabetF_insortTree {α : Type} [DecidableEq α] (u : HuffmanTree α) (ts : Forest α) :
  alphabetF (insortTree u ts) = alphabet u ∪ alphabetF ts := by
  induction ts <;> aesop (add norm [insortTree, alphabetF, alphabet])

@[simp]
lemma consistentF_insortTree {α : Type} [DecidableEq α] (u : HuffmanTree α) (ts : Forest α) :
  consistentF (insortTree u ts) = consistentF (u :: ts) := by
  induction ts <;> grind [consistentF, alphabetF_insortTree, alphabetF, insortTree]

@[simp]
lemma freqF_insortTree {α : Type} [DecidableEq α] (u : HuffmanTree α) (ts : Forest α) :
  freqF (insortTree u ts) = fun a => freq u a + freqF ts a := by
  ext a
  induction ts <;> aesop (add norm [insortTree, freq, freqF, add_left_comm])

@[simp]
lemma heightF_insortTree {α : Type} (u : HuffmanTree α) (ts : Forest α) :
  heightF (insortTree u ts) = max (height u) (heightF ts) := by
  induction ts <;> aesop (add norm [heightF, max_left_comm, height, insortTree])

/--
Inserting a tree into a forest that is sorted by weight preserves sorting.
-/
@[simp]
lemma sortedByWeight_insortTree {α}
  (t : HuffmanTree α) (ts : Forest α)
  (h_sbw : sortedByWeight ts) (h_height_t : height t = 0) (h_height_ts : heightF ts = 0) :
  sortedByWeight (insortTree t ts) := by
  induction ts using sortedByWeight.induct <;>
    grind [heightF, insortTree, height_0_imp_cachedWeight_eq_weight, sortedByWeight]

/--
Construct a Huffman tree from a non-empty forest.

At each step, two trees are combined and inserted into the forest until only a tree is left.
-/
def huffman {α} (xs : Forest α) (h : xs ≠ []) : HuffmanTree α :=
  match xs with
  | [t] => t
  | t1 :: t2 :: ts =>
      huffman (insortTree (uniteTrees t1 t2) ts) (insortTree_ne_nil _ _)
termination_by xs.length

/--
The alphabet of the Huffman tree constructed from a forest is exactly the alphabet of the forest.
-/
@[simp]
lemma alphabet_huffman {α} [DecidableEq α] (ts : Forest α) (h : ts ≠ []) :
  alphabet (huffman ts h) = alphabetF ts := by
  induction ts, h using huffman.induct with
  | case1 t h1 h2 =>
      simp [alphabetF, huffman]
      exact Finset.inter_eq_left.mp rfl
  | case2 t1 t2 ts h1 h2 ih =>
      simp [huffman, alphabetF, ih, Finset.union_left_comm, Finset.union_comm]

/--
If the input forest is consistent, then the Huffman tree constructed is also consistent.
-/
@[simp]
lemma consistent_huffman {α} [DecidableEq α] (ts : Forest α) (h : ts ≠ []) :
  consistentF ts → consistent (huffman ts h) := by
  induction ts, h using huffman.induct <;>
    simp [consistentF, huffman, alphabetF, Finset.inter_union_distrib_left] at *
  grind [consistent_uniteTrees, consistent, huffman, consistentF]

/--
The frequency of a symbol in the Huffman tree constructed is its total frequency in the forest.
-/
@[simp]
lemma freq_huffman {α} [DecidableEq α] (ts : Forest α) (a : α) (h : ts ≠ []) :
  freq (huffman ts h) a = freqF ts a := by
  induction ts, h using huffman.induct <;>
    grind [freq, freqF, huffman, uniteTrees, freqF_insortTree]

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

def String.freq(s : String) (c : Char) := s.toList.filter (· == c) |>.length

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
lemma HfmnTree.charInTree_leaf (a c : α) (f : Nat) :
    (HfmnTree.Leaf a f).charInTree c = (a == c) := by
  grind

/- Convert the canonical proof-side Huffman tree into the public runtime tree. -/
@[simp]
def HfmnTree.ofProofTree : HuffmanTree α → HfmnTree α
  | .leaf w a => .Leaf a w
  | .node _ t1 t2 => .Node (HfmnTree.ofProofTree t1) (HfmnTree.ofProofTree t2)

@[simp]
lemma HfmnTree.weight_ofProofTree (t : HuffmanTree α) :
    (HfmnTree.ofProofTree t).weight = _root_.weight t := by
  induction t <;> simp [HfmnTree.ofProofTree, HfmnTree.weight, _root_.weight, *]

@[simp]
lemma HfmnTree.mem_chars_ofProofTree (t : HuffmanTree α) (a : α) :
    a ∈ (HfmnTree.ofProofTree t).chars ↔ a ∈ alphabet t := by
  induction t with
  | leaf w b =>
      simp [HfmnTree.ofProofTree, HfmnTree.chars, alphabet]
  | node w t1 t2 ih1 ih2 =>
      simp [HfmnTree.ofProofTree, HfmnTree.chars, alphabet, ih1, ih2]

@[simp]
lemma HfmnTree.charInTree_ofProofTree_iff (t : HuffmanTree α) (a : α) :
    (HfmnTree.ofProofTree t).charInTree a = true ↔ a ∈ alphabet t := by
  rw [HfmnTree.charInTree_iff, HfmnTree.mem_chars_ofProofTree]

/- A single proof-side leaf corresponding to one `(symbol, frequency)` entry. -/
@[simp]
def HfmnTree.proofLeaf (x : α × Nat) : HuffmanTree α :=
  HuffmanTree.leaf x.2 x.1

/- Sorted proof-side forest built from the public input format. -/
@[simp]
def HfmnTree.proofForest : AlphaNumList α → Forest α
  | [] => []
  | x :: xs => insortTree (HfmnTree.proofLeaf x) (HfmnTree.proofForest xs)

@[simp]
lemma HfmnTree.alphabetF_proofForest (input : AlphaNumList α) :
    alphabetF (HfmnTree.proofForest input) = input.symbols.toFinset := by
  induction input with
  | nil =>
      rfl
  | cons x xs ih =>
      simp [HfmnTree.proofForest, AlphaNumList.symbols, ih,
        alphabetF_insortTree, HfmnTree.proofLeaf, alphabet]

@[simp]
lemma HfmnTree.heightF_proofForest (input : AlphaNumList α) :
    heightF (HfmnTree.proofForest input) = 0 := by
  induction input with
  | nil =>
      simp [HfmnTree.proofForest, heightF]
  | cons x xs ih =>
      simp [HfmnTree.proofForest, ih, heightF_insortTree,
        HfmnTree.proofLeaf, height]

@[simp]
lemma HfmnTree.sortedByWeight_proofForest (input : AlphaNumList α) :
    sortedByWeight (HfmnTree.proofForest input) := by
  induction input with
  | nil =>
      simp [HfmnTree.proofForest, sortedByWeight]
  | cons x xs ih =>
      have hsorted :=
        sortedByWeight_insortTree
          (t := HfmnTree.proofLeaf x)
          (ts := HfmnTree.proofForest xs)
          ih
          (by simp [HfmnTree.proofLeaf, height])
          (HfmnTree.heightF_proofForest (α := α) xs)
      simpa [HfmnTree.proofForest, HfmnTree.proofLeaf] using hsorted

lemma HfmnTree.proofForest_ne_nil {input : AlphaNumList α} (h : input ≠ []) :
    HfmnTree.proofForest input ≠ [] := by
  cases input with
  | nil =>
      contradiction
  | cons x xs =>
      simp [HfmnTree.proofForest]

/- Canonical proof-side Huffman tree for a non-empty public input. -/
@[simp]
def HfmnTree.proofTree (huffinput : AlphaNumList α) (h : huffinput ≠ []) : HuffmanTree α :=
  huffman (HfmnTree.proofForest huffinput) (HfmnTree.proofForest_ne_nil h)

/- Convert a public runtime tree back into the proof-side model, using input frequencies. -/
@[simp]
def HfmnTree.toProofTree (huffinput : AlphaNumList α) : HfmnTree α → HuffmanTree α
  | .Leaf a _ => HuffmanTree.leaf (AlphaNumList.lookupFreq huffinput a) a
  | .Node l r => HuffmanTree.node 0 (HfmnTree.toProofTree huffinput l) (HfmnTree.toProofTree huffinput r)

@[simp, grind .]
lemma HfmnTree.alphabet_toProofTree (huffinput : AlphaNumList α) (t : HfmnTree α) :
    alphabet (HfmnTree.toProofTree huffinput t) = t.chars.toFinset := by
  induction t with
  | Leaf a w =>
      simp [HfmnTree.toProofTree, HfmnTree.chars, alphabet]
  | Node l r ihl ihr =>
      simp [HfmnTree.toProofTree, HfmnTree.chars, alphabet, ihl, ihr]

/- Public constructor: canonical proof-side Huffman algorithm, re-exposed as `HfmnTree`. -/
@[simp, grind .]
def HfmnTree.tree (huffinput : AlphaNumList α) : HfmnTree α :=
  if h : huffinput = [] then
    HfmnTree.Leaf HfmnType.default 0
  else
    HfmnTree.ofProofTree (HfmnTree.proofTree huffinput h)

@[simp, grind .]
lemma HfmnTree.tree_contains_input_chars (huffinput : AlphaNumList α)
    (a : α) (freq : Nat) (h : (a, freq) ∈ huffinput) :
    (HfmnTree.tree huffinput).charInTree a = true := by
  have hne : huffinput ≠ [] := by
    intro hnil
    simp [hnil] at h
  have hsym : a ∈ AlphaNumList.symbols huffinput :=
    (AlphaNumList.mem_symbols_iff).2 ⟨freq, h⟩
  have halphabetF : a ∈ alphabetF (HfmnTree.proofForest huffinput) := by
    rw [HfmnTree.alphabetF_proofForest]
    simpa using hsym
  have halphabet :
      a ∈ alphabet
        (huffman (HfmnTree.proofForest huffinput)
          (HfmnTree.proofForest_ne_nil hne)) := by
    simpa [alphabet_huffman (HfmnTree.proofForest huffinput)
      (HfmnTree.proofForest_ne_nil hne)] using halphabetF
  have hchar :
      (HfmnTree.ofProofTree
        (huffman (HfmnTree.proofForest huffinput)
          (HfmnTree.proofForest_ne_nil hne))).charInTree a = true :=
    (HfmnTree.charInTree_ofProofTree_iff
      (huffman (HfmnTree.proofForest huffinput)
        (HfmnTree.proofForest_ne_nil hne)) a).2 halphabet
  simpa [HfmnTree.tree, hne] using hchar

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

/-- A tree is admissible for an input if it encodes exactly the same symbol list. -/
def AdmissibleToInput (input : AlphaNumList α) (t : HfmnTree α) : Prop :=
  t.chars.Perm (AlphaNumList.symbols input)

/--
Admissibility aligned to Huffman's tree output.
This is the notion used by the optimality bridge theorem.
-/
def AdmissibleToHuffman (input : AlphaNumList α) (t : HfmnTree α) : Prop :=
  t.chars.Perm (HfmnTree.tree input).chars

-- #eval HfmnTree.decode "1" ( HfmnTree.encoded_tree eg₁ ).1 -- none
-- #eval HfmnTree.decode "0" ( HfmnTree.encoded_tree eg₁ ).1 -- some 'a'
