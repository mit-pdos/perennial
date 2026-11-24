/-
Shared definitions of the proofs of the Go `strings` package: its `isPkgInit`,
the models of what `Fields`, `Compare`, `TrimPrefix` and `Split` return, and
lemmas about them.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Code.strings
public import Perennial.GeneratedProof.strings
public import Perennial.Proof.internal.stringslite.Base
public import Perennial.Proof.sync.Base
public import Perennial.Proof.io.Base
public import Perennial.Proof.internal.bytealg.Base
public import Perennial.Proof.unicode.utf8.Base
public import Perennial.Proof.internal.gomodel.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace strings

/-- Model for Go's `unicode.IsSpace` for ASCII-range bytes. Based on
https://cs.opensource.google/go/go/+/refs/tags/go1.26.1:src/strings/strings.go;l=377 -/
def isAsciiSpace (b : w8) : Bool :=
  [9#8,    -- \t  (0x09)
   10#8,   -- \n  (0x0A)
   11#8,   -- \v  (0x0B)
   12#8,   -- \f  (0x0C)
   13#8,   -- \r  (0x0D)
   32#8    -- space (0x20)
  ].contains b

def splitFieldsAux : GoString → Option GoString → List GoString
  | [], w => match w with | none => [] | some w => [w]
  | x :: s, w =>
    if isAsciiSpace x then
      match w with
      | none => splitFieldsAux s none
      | some w => w :: splitFieldsAux s none
    else splitFieldsAux s (some (w.getD [] ++ [x]))

def splitFields (s : GoString) : List GoString := splitFieldsAux s none

/-! Tests of `splitFields`, which is part of the `wp_Fields` axiom. -/

example : splitFields go!"hello" = [go!"hello"] := by decide

example : splitFields go!"   hello world" = [go!"hello", go!"world"] := by decide

example : splitFields go!"hello world" = [go!"hello", go!"world"] := by decide

example : splitFields go!"" = [] := by decide

def bsTab : w8 := 9#8
def bsNl : w8 := 10#8
def bsCr : w8 := 13#8
def bsSp : w8 := 32#8

def helloWorldWs : GoString :=
  [bsSp, bsTab] ++ go!"hello" ++ [bsNl] ++ go!"world" ++ [bsCr, bsSp]

example : splitFields helloWorldWs = [go!"hello", go!"world"] := by decide

example : splitFields go!"  hello\tthere\ngeneral\rkenobi " =
    [go!"hello", go!"there", go!"general", go!"kenobi"] := by decide

/-! ### `LastIndex` -/

/-- The last index at or below `j` at which `sep` occurs in `s`, or `-1`. -/
def lastIndexFrom (s sep : GoString) : Nat → Int
  | 0 => if sep <+: s then 0 else -1
  | j + 1 => if sep <+: s.drop (j + 1) then ((j + 1 : Nat) : Int) else lastIndexFrom s sep j

/-- What `strings.LastIndex(s, substr)` returns: the last index at which `substr` occurs in `s`,
or `-1` (`len(s)` for an empty `substr`). -/
def lastIndex (s sep : GoString) : Int := lastIndexFrom s sep s.length

theorem lastIndexFrom_eq_neg (s sep : GoString) :
    ∀ j, (∀ k ≤ j, ¬ sep <+: s.drop k) → lastIndexFrom s sep j = -1
  | 0, h => by simp [lastIndexFrom, show ¬ sep <+: s from by simpa using h 0 (Nat.le_refl 0)]
  | j + 1, h => by
    simp only [lastIndexFrom, h (j + 1) (Nat.le_refl _), ↓reduceIte]
    exact lastIndexFrom_eq_neg s sep j (fun k hk => h k (by omega))

theorem lastIndexFrom_eq_of (s sep : GoString) (i : Nat) (h : sep <+: s.drop i)
    (hmax : ∀ k, i < k → k ≤ s.length → ¬ sep <+: s.drop k) :
    ∀ j, i ≤ j → j ≤ s.length → lastIndexFrom s sep j = i
  | 0, hj, _ => by
    have : i = 0 := by omega
    subst this; simp [lastIndexFrom, show sep <+: s from by simpa using h]
  | j + 1, hj, hjs => by
    rcases Nat.lt_or_ge i (j + 1) with hij | hij
    · simp only [lastIndexFrom, hmax (j + 1) hij hjs, ↓reduceIte]
      exact lastIndexFrom_eq_of s sep i h hmax j (by omega) (by omega)
    · have : i = j + 1 := by omega
      subst this; simp [lastIndexFrom, h]

theorem lastIndexFrom_nil (s : GoString) : ∀ j, lastIndexFrom s [] j = j
  | 0 => by simp [lastIndexFrom]
  | j + 1 => by simp [lastIndexFrom]

/-- An empty `sep` occurs last at the end: `lastIndex s [] = len(s)`. -/
theorem lastIndex_nil (s : GoString) : lastIndex s [] = s.length := lastIndexFrom_nil s _

/-- `sep` occurs at `i` and nowhere after: `lastIndex s sep = i`. -/
theorem lastIndex_eq_of (s sep : GoString) (i : Nat) (hi : i ≤ s.length) (h : sep <+: s.drop i)
    (hmax : ∀ k, i < k → k ≤ s.length → ¬ sep <+: s.drop k) : lastIndex s sep = i :=
  lastIndexFrom_eq_of s sep i h hmax s.length hi (Nat.le_refl _)

/-- `sep` occurs nowhere in `s`: `lastIndex s sep = -1`. -/
theorem lastIndex_eq_neg (s sep : GoString) (h : ∀ k, k ≤ s.length → ¬ sep <+: s.drop k) :
    lastIndex s sep = -1 :=
  lastIndexFrom_eq_neg s sep s.length h

/-! ### `TrimLeft` -/

/-- What `strings.TrimLeft(s, cutset)` returns: `s` without its longest prefix of bytes of
`cutset`. Go's `TrimLeft` removes Unicode code points; for an ASCII `cutset` (every byte below
128, the only case `wp_TrimLeft` covers) it removes bytes (`trimLeftByte`, `trimLeftASCII`). -/
def trimLeft (s cutset : GoString) : GoString := s.dropWhile (fun b => decide (b ∈ cutset))

/-- Whether the `asciiSet` `aset` (`[8]uint32`, a bit per byte value) has `c`: bit `c % 32` of word
`c / 32` (`(*asciiSet).contains`). -/
def asciiSetHas (aset : GoArray w32 8) (c : w8) : Bool :=
  !decide (aset.arr.getD (c.toNat / 32) 0 &&& W32 1 <<< W64 (uint.Z (c % W8 32)) = W32 0)

/-! ### `Count` -/

/-- The number of non-overlapping instances of `sep` in `s`, found left to right, each search
starting after the last instance found (what `strings.Count` returns for a non-empty `sep`); `0`
for an empty `sep`. -/
def countOcc (s sep : GoString) : Nat :=
  if hsep : sep = [] then 0 else
  if h : 0 ≤ internal.bytealg.index s sep then
    countOcc (s.drop ((internal.bytealg.index s sep).toNat + sep.length)) sep + 1
  else 0
termination_by s.length
decreasing_by
  have := internal.bytealg.index_bounds s sep
  have : 0 < sep.length := by cases sep <;> simp_all
  simp only [List.length_drop]; omega

/-- What `strings.Count(s, substr)` returns: for an empty `substr`, one more than the number of
runes a range loop over `s` decodes (Go: "the number of Unicode code points in s" plus one, an
invalid UTF-8 sequence counting one per byte); otherwise the number of non-overlapping instances
of `substr` in `s` (`countOcc`). -/
def count (s substr : GoString) : Nat :=
  if substr = [] then (go.runes s).length + 1 else countOcc s substr

theorem countOcc_found (s sep : GoString) (hsep : sep ≠ []) (h : 0 ≤ internal.bytealg.index s sep) :
    countOcc s sep =
      countOcc (s.drop ((internal.bytealg.index s sep).toNat + sep.length)) sep + 1 := by
  rw [countOcc]; simp only [hsep, h, ↓reduceDIte]

theorem countOcc_not_found (s sep : GoString) (h : ¬ 0 ≤ internal.bytealg.index s sep) :
    countOcc s sep = 0 := by
  rw [countOcc]; simp only [h, ↓reduceDIte, dite_eq_ite, ite_self]

/-- For a one-byte `sep`, the instances are the bytes equal to it. -/
theorem countOcc_single (c : w8) : ∀ (n : Nat) (s : GoString), s.length ≤ n →
    countOcc s [c] = s.count c := by
  intro n
  induction n with
  | zero =>
    intro s hs
    have : s = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    rw [countOcc]; simp [internal.bytealg.index, internal.bytealg.indexBelow]
  | succ n ih =>
    intro s hs
    rw [countOcc]
    simp only [List.cons_ne_nil, ↓reduceDIte, List.length_singleton]
    rcases internal.bytealg.index_cases s [c] with ⟨i, hi, hp, hmin⟩ | ⟨hi, hn⟩
    · rw [dite_eq_left (by rw [hi]; omega), hi, Int.toNat_natCast]
      have hc : s[i]? = some c := (internal.bytealg.singleton_prefix_drop s c i).1 hp
      have hil : i < s.length := (List.getElem?_eq_some_iff.1 hc).1
      rw [ih _ (by simp only [List.length_drop]; omega)]
      have hs' : s = s.take i ++ c :: s.drop (i + 1) := by
        have h := List.take_append_drop i s
        rw [List.drop_eq_getElem_cons hil, (List.getElem?_eq_some_iff.1 hc).2] at h
        exact h.symm
      have htake : (s.take i).count c = 0 := by
        refine List.count_eq_zero.2 fun hm => ?_
        obtain ⟨j, hj, hjc⟩ := List.getElem_of_mem hm
        rw [List.length_take] at hj
        refine hmin j (by omega) ((internal.bytealg.singleton_prefix_drop s c j).2 ?_)
        rw [← hjc, List.getElem_take]; exact List.getElem?_eq_getElem (by omega)
      have hcnt := congrArg (List.count c) hs'
      rw [List.count_append, List.count_cons_self, htake] at hcnt
      omega
    · rw [dite_eq_right (by rw [hi]; omega)]
      symm
      refine List.count_eq_zero.2 fun hm => ?_
      obtain ⟨j, hj, hjc⟩ := List.getElem_of_mem hm
      exact hn j ((internal.bytealg.singleton_prefix_drop s c j).2 (by
        rw [← hjc]; exact List.getElem?_eq_getElem hj))

/-! ### `IndexRune` and `IndexAny` -/

/-- Whether `r` is a Unicode code point that UTF-8 can encode (`utf8.ValidRune`). -/
def validRune (r : w32) : Prop :=
  0 ≤ sint.Z r ∧ sint.Z r < 0xD800 ∨ 0xDFFF < sint.Z r ∧ sint.Z r ≤ 0x10FFFF

instance (r : w32) : Decidable (validRune r) := by unfold validRune; infer_instance

/-- The index of the first rune a range loop over `s` decodes to `utf8.RuneError`, or `-1`. -/
def runeErrorIndex (s : GoString) : Int :=
  match (go.runes s).find? (fun e => decide (e.2 = go.runeError)) with
  | some e => (e.1 : Int)
  | none => -1

theorem runeErrorIndex_eq_of (s : GoString) (i : Nat) (e : Nat × w32)
    (h : (go.runes s)[i]? = some e) (he : e.2 = go.runeError)
    (hmin : ∀ e' ∈ (go.runes s).take i, e'.2 ≠ go.runeError) : runeErrorIndex s = e.1 := by
  have hl : i < (go.runes s).length := (List.getElem?_eq_some_iff.1 h).1
  have hs : go.runes s = (go.runes s).take i ++ e :: (go.runes s).drop (i + 1) := by
    have h' := List.take_append_drop i (go.runes s)
    rw [List.drop_eq_getElem_cons hl, (List.getElem?_eq_some_iff.1 h).2] at h'
    exact h'.symm
  unfold runeErrorIndex
  rw [hs, List.find?_append, List.find?_eq_none.2 (fun e' he' => by simpa using hmin e' he')]
  simp [he]

theorem runeErrorIndex_eq_neg (s : GoString) (h : ∀ e ∈ go.runes s, e.2 ≠ go.runeError) :
    runeErrorIndex s = -1 := by
  unfold runeErrorIndex
  rw [List.find?_eq_none.2 (fun e he => by simpa using h e he)]

/-- What `strings.IndexRune(s, r)` returns, case by case as Go's: for an ASCII `r`, the first
index of the byte `r`; for `utf8.RuneError`, the index of the first rune a range loop over `s`
decodes to `RuneError` (an invalid UTF-8 sequence, or U+FFFD itself); for another valid code
point, the first index of its UTF-8 encoding (`string(r)`); `-1` if there is none, or if `r` is
not a valid code point. -/
def indexRune (s : GoString) (r : w32) : Int :=
  if 0 ≤ sint.Z r ∧ sint.Z r < 0x80 then internal.bytealg.indexByte s (W8 (sint.Z r))
  else if r = go.runeError then runeErrorIndex s
  else if validRune r then internal.bytealg.index s (go.runeString (sint.Z r))
  else -1

/-- The first index of a byte of `chars` in `s`, or `-1`: what `strings.IndexAny(s, chars)`
returns for an ASCII `chars` (every byte below `0x80`). -/
def indexAnyByte (s chars : GoString) : Int :=
  if s.findIdx (fun b => decide (b ∈ chars)) < s.length then s.findIdx (fun b => decide (b ∈ chars))
  else -1

theorem indexAnyByte_eq_of (s chars : GoString) (i : Nat) (b : w8) (hb : s[i]? = some b)
    (hin : b ∈ chars) (hmin : ∀ j < i, ∀ b', s[j]? = some b' → b' ∉ chars) :
    indexAnyByte s chars = i := by
  have hil : i < s.length := (List.getElem?_eq_some_iff.1 hb).1
  have hf : s.findIdx (fun b => decide (b ∈ chars)) = i := by
    rw [List.findIdx_eq hil]
    refine ⟨?_, fun j hj => ?_⟩
    · rw [(List.getElem?_eq_some_iff.1 hb).2]; simpa using hin
    · simpa using hmin j hj _ (List.getElem?_eq_getElem (by omega))
  unfold indexAnyByte; rw [hf]; simp [hil]

theorem indexAnyByte_eq_neg (s chars : GoString) (h : ∀ (j : Nat) (b : w8), s[j]? = some b → b ∉ chars) :
    indexAnyByte s chars = -1 := by
  have hf : s.findIdx (fun b => decide (b ∈ chars)) = s.length := by
    rw [List.findIdx_eq_length]
    intro x hx
    obtain ⟨j, hj, hjx⟩ := List.getElem_of_mem hx
    simpa using h j x (by rw [← hjx]; exact List.getElem?_eq_getElem hj)
  unfold indexAnyByte; rw [hf]; simp

/-- The UTF-8 encoding of a non-ASCII code point (or of U+FFFD, for an invalid one) starts with a
byte of `0x80` or above. -/
theorem runeString_head (v : Int) (hv : ¬ (0 ≤ v ∧ v < 0x80)) :
    ∃ b rest, go.runeString v = b :: rest ∧ 0x80 ≤ uint.Z b := by
  unfold go.runeString
  have hc : 0x7f < (if 0 ≤ v ∧ v.toNat.isValidChar then Char.ofNat v.toNat else '\uFFFD').val.toNat := by
    split
    · rename_i h
      rw [Char.ofNat, dite_eq_left h.2]
      change 0x7f < v.toNat
      omega
    · decide
  generalize (if 0 ≤ v ∧ v.toNat.isValidChar then Char.ofNat v.toNat else '\uFFFD') = c at hc ⊢
  unfold String.utf8EncodeChar
  simp only [show ¬ c.val.toNat ≤ 0x7f by omega, ↓reduceIte]
  repeat' split
  all_goals (refine ⟨_, _, List.map_cons .., ?_⟩; rw [UInt8.toNat_ofNat']; word)

theorem indexByte_nonneg_iff (s : GoString) (c : w8) :
    0 ≤ internal.bytealg.indexByte s c ↔ c ∈ s := by
  unfold internal.bytealg.indexByte
  rcases internal.bytealg.index_cases s [c] with ⟨i, hi, hp, -⟩ | ⟨hi, hn⟩
  · rw [hi]
    have hc := (internal.bytealg.singleton_prefix_drop s c i).1 hp
    exact ⟨fun _ => List.mem_of_getElem? hc, fun _ => by omega⟩
  · rw [hi]
    refine ⟨fun h => by omega, fun hm => ?_⟩
    obtain ⟨j, hj, hjc⟩ := List.getElem_of_mem hm
    exact absurd ((internal.bytealg.singleton_prefix_drop s c j).2 (by
      rw [← hjc]; exact List.getElem?_eq_getElem hj)) (hn j)

theorem indexAnyByte_single (s : GoString) (c : w8) :
    indexAnyByte s [c] = internal.bytealg.indexByte s c := by
  unfold internal.bytealg.indexByte
  rcases internal.bytealg.index_cases s [c] with ⟨i, hi, hp, hmin⟩ | ⟨hi, hn⟩
  · rw [hi]
    refine indexAnyByte_eq_of s [c] i c ((internal.bytealg.singleton_prefix_drop s c i).1 hp)
      (List.mem_singleton_self c) (fun j hj b' hb' hm => ?_)
    rw [List.mem_singleton.1 hm] at hb'
    exact hmin j hj ((internal.bytealg.singleton_prefix_drop s c j).2 hb')
  · rw [hi]
    refine indexAnyByte_eq_neg s [c] (fun j b' hb' hm => ?_)
    rw [List.mem_singleton.1 hm] at hb'
    exact hn j ((internal.bytealg.singleton_prefix_drop s c j).2 hb')

/-- `IndexRune` on an ASCII `chars` finds only an ASCII rune, the byte it is. -/
theorem indexRune_ascii_chars (chars : GoString) (hascii : ∀ b ∈ chars, uint.Z b < 0x80)
    (c : w32) :
    0 ≤ indexRune chars c ↔ (0 ≤ sint.Z c ∧ sint.Z c < 0x80 ∧ W8 (sint.Z c) ∈ chars) := by
  unfold indexRune
  by_cases hA : 0 ≤ sint.Z c ∧ sint.Z c < 0x80
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hA), indexByte_nonneg_iff]
    exact ⟨fun h => ⟨hA.1, hA.2, h⟩, fun h => h.2.2⟩
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hA)]
    refine ⟨fun h => ?_, fun h => absurd ⟨h.1, h.2.1⟩ hA⟩
    exfalso
    split at h
    · have : runeErrorIndex chars = -1 := by
        refine runeErrorIndex_eq_neg chars (fun e he herr => ?_)
        obtain ⟨hl, he2⟩ := go.runes_mem chars e he
        obtain ⟨b, hb⟩ : ∃ b, chars[e.1]? = some b := ⟨_, List.getElem?_eq_getElem hl⟩
        have hb128 := hascii b (List.mem_of_getElem? hb)
        rw [go.decodeRune_ascii chars e.1 b hb hb128] at he2
        rw [he2] at herr
        have := congrArg sint.Z herr
        rw [go.runeError_sint] at this
        revert this; word
      rw [this] at h; omega
    · split at h
      · obtain ⟨b, rest, hrs, hb⟩ := runeString_head (sint.Z c) hA
        have : internal.bytealg.index chars (go.runeString (sint.Z c)) = -1 := by
          refine internal.bytealg.index_eq_neg chars _ (fun i => ?_)
          rw [hrs]
          refine internal.bytealg.not_prefix_drop_of_head chars rest b i (fun hi => ?_)
          have := hascii b (List.mem_of_getElem? hi)
          omega
        rw [this] at h; omega
      · omega

theorem indexRune_bounds (s : GoString) (r : w32) :
    -1 ≤ indexRune s r ∧ indexRune s r < s.length + 1 := by
  unfold indexRune
  split
  · have := internal.bytealg.indexByte_bounds s (W8 (sint.Z r)); omega
  · split
    · unfold runeErrorIndex
      split
      · rename_i e he
        have := (go.runes_mem s e (List.mem_of_find?_eq_some he)).1
        omega
      · omega
    · split
      · have := internal.bytealg.index_bounds s (go.runeString (sint.Z r))
        rcases Int.lt_or_le (internal.bytealg.index s (go.runeString (sint.Z r))) 0 with h | h
        · omega
        · have := this.2 h; omega
      · omega

/-- The runes of a range loop are in increasing order of their indices. -/
theorem runes_idx_lt (s : GoString) (j j' : Nat) (e e' : Nat × w32)
    (hj : (go.runes s)[j]? = some e) (hj' : (go.runes s)[j']? = some e') (hlt : e'.1 < e.1) :
    j' < j := by
  have hp := List.pairwise_iff_getElem.1 (go.runes_pairwise s)
  obtain ⟨hjl, rfl⟩ := List.getElem?_eq_some_iff.1 hj
  obtain ⟨hj'l, rfl⟩ := List.getElem?_eq_some_iff.1 hj'
  refine Classical.byContradiction fun hc => ?_
  rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt hc) with h | h
  · have := hp j j' hjl hj'l h; omega
  · subst h; omega

/-- No byte of an ASCII `chars` occurs in `s` before index `K` if `IndexRune(chars, c)` is
negative for every rune `c` of `s` among the first `j`, and every rune before `K` is among
them. -/
theorem no_byte_of_chars (s chars : GoString) (hascii : ∀ b ∈ chars, uint.Z b < 0x80) (j K : Nat)
    (hP : ∀ j' < j, ∀ e, (go.runes s)[j']? = some e → indexRune chars e.2 < 0)
    (hK : ∀ j' e, (go.runes s)[j']? = some e → e.1 < K → j' < j) :
    ∀ p < K, ∀ b', s[p]? = some b' → b' ∉ chars := by
  intro p hp b' hb' hm
  have h128 := hascii b' hm
  obtain ⟨j', hj'⟩ := List.mem_iff_getElem?.1 (go.runes_ascii s p b' hb' h128)
  have h1 := hP j' (hK j' _ hj' hp) _ hj'
  have hb'eq : W8 (sint.Z (W32 (uint.Z b'))) = b' := by word
  have h2 := (indexRune_ascii_chars chars hascii (W32 (uint.Z b'))).2
    ⟨by word, by word, by rw [hb'eq]; exact hm⟩
  simp only at h1
  omega

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : strings.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.strings :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.strings :=
  build_get_is_pkg_init_wf

/-- A join with one more element at the end. -/
theorem intercalate_snoc (sep : GoString) :
    ∀ (ys : List GoString) (x : GoString), ys ≠ [] →
      sep.intercalate (ys ++ [x]) = sep.intercalate ys ++ sep ++ x
  | [], _, h => absurd rfl h
  | [y], x, _ => by simp [List.intercalate]
  | y :: y' :: ys, x, _ => by
    have ih := intercalate_snoc sep (y' :: ys) x (List.cons_ne_nil _ _)
    simp only [List.cons_append, List.intercalate_cons_cons] at ih ⊢
    rw [ih]; simp only [List.append_assoc]

/-- One more element of a join: the first alone, then after a separator. -/
theorem intercalate_take_succ (sep : GoString) (xs : List GoString) (n : Nat) (x : GoString)
    (hn : n < xs.length) (hx : xs[n] = x) :
    sep.intercalate (xs.take (n + 1)) =
      if n = 0 then x else sep.intercalate (xs.take n) ++ sep ++ x := by
  rw [List.take_succ, List.getElem?_eq_getElem hn, hx]
  split
  · subst_vars
    cases xs with
    | nil => simp at hn
    | cons y ys => simp [List.intercalate]
  · have : xs.take n ≠ [] := by
      simp only [ne_eq, List.take_eq_nil_iff, not_or]
      exact ⟨by omega, List.ne_nil_of_length_pos (by omega)⟩
    simp only [Option.toList_some]
    exact intercalate_snoc sep _ x this

/-- What `strings.Compare(a, b)` returns: `-1`, `0` or `+1` as `a` is lexicographically less
than, equal to or greater than `b` (Go's `<` on strings, `GoStringLt`), as `bytes.compareResult`. -/
def compareResult (a b : GoString) : w64 :=
  if go.GoStringLt a b then W64 (-1) else if a = b then W64 0 else W64 1

/-- What `strings.TrimPrefix(s, pfx)` returns: `s` without the prefix `pfx` if it has it,
else `s`. -/
def trimPrefix (s pfx : GoString) : GoString :=
  if pfx <+: s then s.drop pfx.length else s

/-- The fields that Go's `strings.Split` makes of the rest `r` of a string when the current field
is `field`: at an occurrence of `sep` the field ends and the next one starts after the
occurrence; any other byte goes to the current field. For an empty `sep` it keeps all of `r` in
the field (Go splits into UTF-8 sequences instead; `wp_Split` requires `sep` non-empty). -/
def splitAux (sep : GoString) : GoString → GoString → List GoString
  | [], field => [field]
  | c :: r, field =>
    if sep ≠ [] ∧ sep <+: c :: r then field :: splitAux sep ((c :: r).drop sep.length) []
    else splitAux sep r (field ++ [c])
termination_by r => r.length
decreasing_by
  · obtain ⟨hne, -⟩ := ‹sep ≠ [] ∧ sep <+: c :: r›
    have : 0 < sep.length := List.length_pos_iff.mpr hne
    simp only [List.length_drop, List.length_cons]; omega
  · simp

/-- What `strings.Split(s, sep)` returns, for a non-empty `sep`: the substrings of `s` between
the occurrences of `sep`, found left to right without overlap. `split "" sep = [""]`, and a
trailing `sep` gives a trailing empty field. -/
def split (s sep : GoString) : List GoString := splitAux sep s []

/-! Tests of `split`. -/

example : split go!"a/b" go!"/" = [go!"a", go!"b"] := by simp [split, splitAux]
example : split go!"" go!"/" = [go!""] := by simp [split, splitAux]
example : split go!"a/" go!"/" = [go!"a", go!""] := by simp [split, splitAux]
example : split go!"x//ab///" go!"//" = [go!"x", go!"ab", go!"/"] := by simp [split, splitAux]

theorem splitAux_ne_nil (sep r field : GoString) : splitAux sep r field ≠ [] := by
  fun_induction splitAux sep r field <;> simp_all

/-- `strings.Split` returns at least one field. -/
theorem split_ne_nil (s sep : GoString) : split s sep ≠ [] := splitAux_ne_nil _ _ _

theorem intercalate_splitAux (sep r field : GoString) :
    sep.intercalate (splitAux sep r field) = field ++ r := by
  fun_induction splitAux sep r field with
  | case1 field => simp
  | case2 c r field h ih =>
    obtain ⟨t, ht⟩ := h.2
    rw [List.intercalate_cons_of_ne_nil (splitAux_ne_nil _ _ _), ih, ← ht]
    simp
  | case3 c r field h ih => rw [ih]; simp

/-- The fields of `split s sep` joined by `sep` (as `strings.Join` joins them) give `s` back. -/
theorem intercalate_split (s sep : GoString) : sep.intercalate (split s sep) = s :=
  intercalate_splitAux sep s []

theorem splitAux_no_infix (sep r field : GoString) (hsep : sep ≠ [])
    (H : ∀ k < field.length, ¬ sep <+: field.drop k ++ r) :
    ∀ f ∈ splitAux sep r field, ¬ sep <:+: f := by
  fun_induction splitAux sep r field with
  | case1 field =>
    intro f hf ⟨u, v, huv⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    subst hf
    have hlt : u.length < f.length := by
      rw [← huv]; have := List.length_pos_iff.mpr hsep; simp; omega
    apply H u.length hlt
    rw [← huv]; simp
  | case2 c r field h ih =>
    intro f hf
    simp only [List.mem_cons] at hf
    rcases hf with rfl | hf
    · rintro ⟨u, v, huv⟩
      have hlt : u.length < f.length := by
        rw [← huv]; have := List.length_pos_iff.mpr hsep; simp; omega
      apply H u.length hlt
      rw [← huv]; simp
    · exact ih (by simp) f hf
  | case3 c r field h ih =>
    apply ih
    intro k hk
    simp only [List.length_append, List.length_cons, List.length_nil] at hk
    by_cases hk' : k < field.length
    · rw [List.drop_append_of_le_length (by omega)]
      simpa using H k hk'
    · rw [show k = field.length by omega, List.drop_append_of_le_length (Nat.le_refl _)]
      simp only [List.drop_length, List.nil_append, List.singleton_append]
      exact fun hp => h ⟨hsep, hp⟩

/-- No field of `split s sep` contains `sep`, for a non-empty `sep`. -/
theorem split_no_infix (s sep : GoString) (hsep : sep ≠ []) :
    ∀ f ∈ split s sep, ¬ sep <:+: f :=
  splitAux_no_infix sep s [] hsep (by simp)

/-- A `*Replacer` made by `NewReplacer(oldnew...)` and not used yet: its own copy of the
`oldnew` pairs, its `once` and its built `r` still zero. -/
def ownReplacer (r : Loc) (oldnew : List GoString) : IProp GF :=
  iprop(∃ (sl : GoSlice), r ↦ ({ once' := zero_val _, r' := zero_val _, oldnew' := sl } : Replacer) ∗
    sl ↦* oldnew ∗ ownSliceCap GoString sl (DFrac.own 1))

end wps

end strings

end Perennial
end
