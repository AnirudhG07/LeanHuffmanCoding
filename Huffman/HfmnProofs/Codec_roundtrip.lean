import Huffman.Codec

/-!
# Round-trip correctness of the runtime codec

`decodeBits codec (encodeSymbols codec xs) = .ok xs`: the tree-walk decoder
inverts the codebook encoder. Built up from:

* `decodeOne_encode?` — the decoder walking the bits of a symbol's tree path
  (`HfmnTree.encode?`) returns that symbol (Lemma A);
* `lookupCode_eq_encode?` — the codebook code for a symbol equals its tree path
  (Lemma C), for non-degenerate (`Node`-rooted) trees;
* assembled into `decodeBits_encodeSymbols`.
-/

namespace Huffman

set_option linter.unusedSectionVars false

variable {α : Type} [DecidableEq α] [Inhabited α] [Ord α] [HfmnType α]

/-- **Lemma D.** A symbol has an encode path iff it occurs in the tree. -/
theorem encode?_isSome_iff (t : HfmnTree α) (c : α) :
    (HfmnTree.encode? c t).isSome ↔ c ∈ t.chars := by
  induction t with
  | Leaf c' w =>
      simp only [HfmnTree.encode?, HfmnTree.chars, List.mem_singleton]
      by_cases h : c = c' <;> simp [h]
  | Node l r ihl ihr =>
      simp only [HfmnTree.encode?, HfmnTree.chars, List.mem_append]
      by_cases hin : l.charInTree c
      · have hl : c ∈ l.chars := (HfmnTree.charInTree_iff l c).1 hin
        simp [hin, Option.isSome_map, ihl, hl]
      · have hnl : c ∉ l.chars := fun h => hin ((HfmnTree.charInTree_iff l c).2 h)
        simp [hin, Option.isSome_map, ihr, hnl]

/-- **Lemma C.** The codebook entry for `c` is its tree path, prefixed by `pref`
(for non-empty `pref`, i.e. away from a degenerate single-leaf root). -/
theorem codebookAux_find (t : HfmnTree α) :
    ∀ (c : α) (pref : BitStream), pref ≠ [] →
      (codebookAux t pref).find? (fun e => e.1 == c)
        = (HfmnTree.encode? c t).map (fun p => (c, pref ++ p)) := by
  induction t with
  | Leaf c' w =>
      intro c pref hpref
      have hpe : pref.isEmpty = false := by
        cases pref with | nil => exact absurd rfl hpref | cons => rfl
      simp only [codebookAux, hpe, if_false, HfmnTree.encode?]
      by_cases h : c = c'
      · subst h; simp
      · have hbeq : (c' == c) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]; exact fun hh => h hh.symm
        simp [List.find?_cons, hbeq, h]
  | Node l r ihl ihr =>
      intro c pref hpref
      simp only [codebookAux, List.find?_append,
                 ihl c (pref ++ [false]) (by simp), ihr c (pref ++ [true]) (by simp),
                 HfmnTree.encode?]
      cases hcl : HfmnTree.encode? c l with
      | some pl =>
          have hin : c ∈ l.chars := (encode?_isSome_iff l c).1 (by simp [hcl])
          simp [hin, hcl, List.append_assoc, Function.comp]
      | none =>
          have hin : c ∉ l.chars := by
            intro h
            have h1 := (encode?_isSome_iff l c).2 h
            rw [hcl] at h1; simp at h1
          simp [hin, hcl, List.append_assoc, Option.map_map]
          rfl

/-- **Lemma A.** Walking the decoder along a symbol's encode path returns it. -/
theorem decodeOne_encode? (root : HfmnTree α) :
    ∀ (t : HfmnTree α) (c : α) (p rest : BitStream) (fuel : Nat),
      HfmnTree.encode? c t = some p → p.length < fuel →
      decodeOne root fuel t (p ++ rest) = .ok (c, rest) := by
  intro t
  induction t with
  | Leaf c' w =>
      intro c p rest fuel hp hf
      simp only [HfmnTree.encode?] at hp
      split at hp
      · rename_i hcc
        injection hp with hp; subst hp; subst hcc
        cases fuel with
        | zero => exact absurd hf (by omega)
        | succ f => simp [decodeOne]
      · exact absurd hp (by simp)
  | Node l r ihl ihr =>
      intro c p rest fuel hp hf
      simp only [HfmnTree.encode?] at hp
      cases fuel with
      | zero => exact absurd hf (by omega)
      | succ f =>
          split at hp
          · obtain ⟨p', hpl, rfl⟩ := Option.map_eq_some_iff.1 hp
            have hf' : p'.length < f := by simp only [List.length_cons] at hf; omega
            show decodeOne root f l (p' ++ rest) = .ok (c, rest)
            exact ihl c p' rest f hpl hf'
          · obtain ⟨p', hpr, rfl⟩ := Option.map_eq_some_iff.1 hp
            have hf' : p'.length < f := by simp only [List.length_cons] at hf; omega
            show decodeOne root f r (p' ++ rest) = .ok (c, rest)
            exact ihr c p' rest f hpr hf'

/-- One step of `decodeMany`: when `bits` decodes one symbol to `(sym, rest)`,
the decode continues on `rest` with `sym` accumulated. -/
private theorem decodeMany_step (t : HfmnTree α) (f : Nat) (bits : BitStream)
    (acc : List α) (sym : α) (rest : BitStream)
    (hne : bits ≠ []) (hone : decodeOne t (bits.length + 1) t bits = .ok (sym, rest)) :
    decodeMany t (f + 1) bits acc = decodeMany t f rest (sym :: acc) := by
  cases bits with
  | nil => exact absurd rfl hne
  | cons b bs => simp only [decodeMany, hone]

/-- **Lemma B.** The decoder inverts the tree-path encoder on a whole symbol
list: decoding the concatenated codes of `xs` returns `xs`. -/
theorem decodeMany_encode? (t : HfmnTree α) :
    ∀ (xs acc : List α) (fuel : Nat),
      (∀ x ∈ xs, ∃ p, HfmnTree.encode? x t = some p ∧ p ≠ []) →
      xs.length < fuel →
      decodeMany t fuel (xs.flatMap (fun x => (HfmnTree.encode? x t).getD [])) acc
        = .ok (acc.reverse ++ xs) := by
  intro xs
  induction xs with
  | nil =>
      intro acc fuel _ hf
      cases fuel with
      | zero => exact absurd hf (by omega)
      | succ f => simp [decodeMany]
  | cons x xs ih =>
      intro acc fuel hsy hf
      obtain ⟨px, hpx, hpne⟩ := hsy x (by simp)
      cases fuel with
      | zero => exact absurd hf (by omega)
      | succ f =>
          have hxs : xs.length < f := by simp only [List.length_cons] at hf; omega
          rw [show (x :: xs).flatMap (fun y => (HfmnTree.encode? y t).getD [])
                = px ++ xs.flatMap (fun y => (HfmnTree.encode? y t).getD [])
              from by simp [List.flatMap_cons, hpx]]
          set rest := xs.flatMap (fun y => (HfmnTree.encode? y t).getD [])
          have hne : px ++ rest ≠ [] := by simp [hpne]
          have hA : decodeOne t ((px ++ rest).length + 1) t (px ++ rest) = .ok (x, rest) :=
            decodeOne_encode? t t x px rest _ hpx (by simp only [List.length_append]; omega)
          rw [decodeMany_step t f (px ++ rest) acc x rest hne hA,
              ih (x :: acc) f (fun y hy => hsy y (by simp [hy])) hxs]
          simp

/-- The codebook lookup equals the tree path, for a `Node`-rooted codec tree. -/
theorem lookupCode_eq_encode? (codec : Codec α) (l r : HfmnTree α)
    (htree : codec.tree = .Node l r)
    (hcb : codec.codebook = runtimeCodebook codec.tree) (c : α) :
    lookupCode codec c = HfmnTree.encode? c codec.tree := by
  rw [lookupCode, hcb, htree]
  simp only [runtimeCodebook, codebookAux, List.nil_append, List.find?_append,
             codebookAux_find l c [false] (by simp), codebookAux_find r c [true] (by simp),
             HfmnTree.encode?]
  cases hcl : HfmnTree.encode? c l with
  | some pl =>
      have hin : c ∈ l.chars := (encode?_isSome_iff l c).1 (by simp [hcl])
      simp [hin, hcl, Option.map_map]
  | none =>
      have hin : c ∉ l.chars := by
        intro h; have h1 := (encode?_isSome_iff l c).2 h; rw [hcl] at h1; simp at h1
      simp [hin, hcl, Option.map_map]
      rfl

/-- With every per-symbol code non-empty, the stream is at least as long as the
symbol list (so `bits.length + 1` is enough decoder fuel). -/
private theorem length_le_flatMap (t : HfmnTree α) :
    ∀ xs : List α, (∀ x ∈ xs, ∃ p, HfmnTree.encode? x t = some p ∧ p ≠ []) →
      xs.length ≤ (xs.flatMap (fun x => (HfmnTree.encode? x t).getD [])).length := by
  intro xs
  induction xs with
  | nil => simp
  | cons x xs ih =>
      intro h
      obtain ⟨p, hp, hpne⟩ := h x (by simp)
      have hp1 : 1 ≤ p.length := by cases p with | nil => exact absurd rfl hpne | cons => simp
      have ih' := ih (fun y hy => h y (by simp [hy]))
      simp only [List.flatMap_cons, List.length_append, List.length_cons, hp, Option.getD_some]
      omega

/-- Computational unfolding of `encodeSymbols` on a cons (bind-free). -/
private theorem encodeSymbols_cons (codec : Codec α) (x : α) (xs : List α) :
    encodeSymbols codec (x :: xs)
      = match lookupCode codec x, encodeSymbols codec xs with
        | some code, .ok tbits => .ok (code ++ tbits)
        | none, _ => .error "Symbol is not present in codec alphabet."
        | _, .error e => .error e := by
  simp only [encodeSymbols, encodeSymbol]
  cases lookupCode codec x <;> cases encodeSymbols codec xs <;> rfl

/-- Successful encoding produces exactly the concatenated tree-path codes, each
non-empty (for a `Node`-rooted codec tree). -/
private theorem encodeSymbols_flatMap (codec : Codec α) (l r : HfmnTree α)
    (htree : codec.tree = .Node l r) (hcb : codec.codebook = runtimeCodebook codec.tree) :
    ∀ (xs : List α) (bits : BitStream), encodeSymbols codec xs = .ok bits →
      bits = xs.flatMap (fun x => (HfmnTree.encode? x codec.tree).getD []) ∧
      (∀ x ∈ xs, ∃ p, HfmnTree.encode? x codec.tree = some p ∧ p ≠ []) := by
  intro xs
  induction xs with
  | nil =>
      intro bits h
      simp only [encodeSymbols, Except.ok.injEq] at h
      subst h; simp
  | cons x xs ih =>
      intro bits h
      rw [encodeSymbols_cons] at h
      cases hl : lookupCode codec x with
      | none => simp [hl] at h
      | some code =>
          cases htl : encodeSymbols codec xs with
          | error e => simp [hl, htl] at h
          | ok tbits =>
              simp only [hl, htl, Except.ok.injEq] at h
              have hcode : HfmnTree.encode? x codec.tree = some code := by
                rw [← lookupCode_eq_encode? codec l r htree hcb]; exact hl
              have hne1 : code ≠ [] := by
                have hc := hcode
                rw [htree] at hc
                simp only [HfmnTree.encode?] at hc
                split at hc
                all_goals (obtain ⟨q, _, hq⟩ := Option.map_eq_some_iff.1 hc; subst hq; simp)
              obtain ⟨ihflat, ihne⟩ := ih tbits htl
              refine ⟨?_, ?_⟩
              · subst h
                simp only [List.flatMap_cons, hcode, Option.getD_some]
                rw [ihflat]
              · intro y hy
                rcases List.mem_cons.1 hy with rfl | hy
                · exact ⟨code, hcode, hne1⟩
                · exact ihne y hy

/-- **Round-trip correctness.** Decoding the encoding of `xs` returns `xs`, for
any codec whose tree is a `Node` (any alphabet of at least two symbols). -/
theorem decodeBits_encodeSymbols (codec : Codec α) (l r : HfmnTree α)
    (htree : codec.tree = .Node l r)
    (hcb : codec.codebook = runtimeCodebook codec.tree)
    (xs : List α) (bits : BitStream)
    (henc : encodeSymbols codec xs = .ok bits) :
    decodeBits codec bits = .ok xs := by
  obtain ⟨hflat, hne⟩ := encodeSymbols_flatMap codec l r htree hcb xs bits henc
  rw [htree] at hflat hne
  have hlen : xs.length <
      (xs.flatMap (fun x => (HfmnTree.encode? x (.Node l r)).getD [])).length + 1 := by
    have hle := length_le_flatMap (.Node l r) xs hne; omega
  simp only [decodeBits, htree]
  rw [hflat, decodeMany_encode? (.Node l r) xs [] _ hne hlen]
  simp

end Huffman
