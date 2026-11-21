/-
A format string's directives, as Go's `doPrintf` reads them (`fmtDirectives`), what the specs of
`Sprintf`, `Printf` and `Errorf` state their premise over (`fmt.argsOk`, `Args.lean`), and the
arguments of the `%w` directives (`wrapArgs`), which decide what `Errorf` returns.
-/
module

public import Perennial.Proof.fmt.Base

@[expose] public section

noncomputable section

namespace Perennial

namespace fmt

/-! Bytes are `w8`: `%` is 37, `#` 35, `+` 43, `-` 45, `0` 48, space 32, `.` 46, `*` 42, `[` 91,
digits 48 to 57, `v` 118, `s` 115, `x` 120, `X` 88, `q` 113, `w` 119, `T` 84, `p` 112, `d` 100. -/

/-- One directive of a format string that consumes an argument: its verb, and whether it is
`%#v` or `%#w` (Go's `sharpV`: `doPrintf`'s `case 'w'` falls through to `case 'v'`, which sets
`sharpV` from the `#` flag; under `Errorf`, `%#w` of an error calls its `GoString()` or reflects
into it, as `%#v` does). -/
structure Directive where
  verb : w8
  sharpV : Bool
  deriving DecidableEq, Repr

/-- Where `fmtDirectivesAux` is inside a directive, after its `%`: reading the flags, the width,
or the precision (after the `.`); for the width and the precision, how many digits of the run have
been read. -/
inductive DirPhase where
  | flags | width (n : Nat) | prec (n : Nat)
  deriving DecidableEq, Repr

/-- The longest width or precision digit run the parser accepts: 7. Go's `parsenum` (go1.27.3
`fmt/print.go:350-362`) checks `tooLarge(num)` (`num > 1e6`) before adding each digit and gives up
past it (`doPrintf` then writes `%!(NOVERB)`, stops, and prints every argument left as `EXTRA`
under `%v`). Before the `k`-th digit the value read has `k - 1` digits, at most `10^6 - 1` for
`k ≤ 7`, so a run of at most 7 digits never trips it; a longer one may, and is refused
(conservatively: refusing more formats only excludes more). -/
def maxNumDigits : Nat := 7

/-- `fmtDirectives`' parser, structurally recursive over the bytes: `st = none` in literal text,
`st = some (sharp, ph)` inside a directive, `sharp` saying whether the `#` flag was read and `ph`
what is being read (Go's `doPrintf`). A `.` starts the precision only if a byte follows it, as in
Go (`if i+1 < end && format[i] == '.'`, go1.27.3 `fmt/print.go:1100`); a trailing `.` is the verb.
A verb is one byte: Go decodes a rune, but a multi-byte rune's continuation bytes are never `%`,
so the directives read are the same. -/
def fmtDirectivesAux : Option (Bool × DirPhase) → GoString → Option (List Directive)
  | _, [] => some []
  | none, b :: bs =>
    if b = W8 37 then fmtDirectivesAux (some (false, .flags)) bs
    else fmtDirectivesAux none bs
  | some (sharp, ph), b :: bs =>
    -- `b` as the verb: `*` or `[` (a `*` width or precision, an argument index) is not admitted;
    -- `%%` consumes no argument; any other verb consumes one.
    let verb : Option (List Directive) :=
      if b = W8 42 ∨ b = W8 91 then none
      else if b = W8 37 then fmtDirectivesAux none bs
      else (⟨b, sharp && (decide (b = W8 118) || decide (b = W8 119))⟩ :: ·) <$>
        fmtDirectivesAux none bs
    let digit : Prop := 48 ≤ b.toNat ∧ b.toNat ≤ 57
    match ph with
    | .flags =>
      if b = W8 35 then fmtDirectivesAux (some (true, .flags)) bs
      else if b = W8 43 ∨ b = W8 45 ∨ b = W8 48 ∨ b = W8 32 then
        fmtDirectivesAux (some (sharp, .flags)) bs
      else if digit then fmtDirectivesAux (some (sharp, .width 1)) bs
      else if b = W8 46 ∧ bs ≠ [] then fmtDirectivesAux (some (sharp, .prec 0)) bs
      else verb
    | .width n =>
      if digit then
        (if n < maxNumDigits then fmtDirectivesAux (some (sharp, .width (n + 1))) bs
         else none)
      else if b = W8 46 ∧ bs ≠ [] then fmtDirectivesAux (some (sharp, .prec 0)) bs
      else verb
    | .prec n =>
      if digit then
        (if n < maxNumDigits then fmtDirectivesAux (some (sharp, .prec (n + 1))) bs
         else none)
      else verb

/-- The directives of a format string that consume an argument, in order: each `%`, then flags
among `+ - # 0 space`, then a decimal width, then `.` and a decimal precision, then the verb;
`%%` (after any flags, width, precision) and a trailing `%` consume none. `none` when a directive
has a `*` width or precision or an argument index `[n]`, or a width or precision of more than
`maxNumDigits` digits, which the model does not follow. Decidable: callers' formats are
literals. -/
def fmtDirectives (format : GoString) : Option (List Directive) :=
  fmtDirectivesAux none format

/-! Tests of `fmtDirectives`. -/

example : fmtDirectives go!"%w: Limit(%d) not supported" =
    some [⟨W8 119, false⟩, ⟨W8 100, false⟩] := by decide
example : fmtDirectives go!"%%d %5.2f %#v" = some [⟨W8 102, false⟩, ⟨W8 118, true⟩] := by
  decide
example : fmtDirectives go!"%#x %+v %-08.3s %.q % d" =
    some [⟨W8 120, false⟩, ⟨W8 118, false⟩, ⟨W8 115, false⟩, ⟨W8 113, false⟩,
      ⟨W8 100, false⟩] := by decide
example : fmtDirectives go!"%#w %w %+w" =
    some [⟨W8 119, true⟩, ⟨W8 119, false⟩, ⟨W8 119, false⟩] := by decide
example : fmtDirectives go!"x%." = some [⟨W8 46, false⟩] := by decide
example : fmtDirectives go!"%.5.d" = some [⟨W8 46, false⟩] := by decide
example : fmtDirectives go!"%*d" = none := by decide
example : fmtDirectives go!"%[1]d" = none := by decide
example : fmtDirectives go!"abc%" = some [] := by decide
example : fmtDirectives go!"%5%%s" = some [⟨W8 115, false⟩] := by decide
example : fmtDirectives go!"%1234567d|%.9999999d" =
    some [⟨W8 100, false⟩, ⟨W8 100, false⟩] := by decide
example : fmtDirectives go!"rev %99999999d" = none := by decide
example : fmtDirectives go!"%000000000005d" = some [⟨W8 100, false⟩] := by decide

/-- The verbs under which `fmt` calls an argument's `Error()`/`String()` (`handleMethods`):
`v s x X q`. -/
def methodVerbs : List w8 := [W8 118, W8 115, W8 120, W8 88, W8 113]

/-- `Errorf`'s: the method verbs and `w` (`%w` of an `error` is formatted as `%v`). -/
def errorfVerbs : List w8 := methodVerbs ++ [W8 119]

/-- The argument positions, from `k` on, of the directives `ds` (the `j`-th consuming argument
`k + j`) whose verb is `w`, among the first `n` arguments: the arguments Go's `doPrintf` records in
`wrappedErrs` (a `%w` without an argument records none). -/
def wrapArgsFrom : Nat → List Directive → Nat → List Nat
  | _, [], _ => []
  | k, d :: ds, n => (if d.verb = W8 119 ∧ k < n then [k] else []) ++ wrapArgsFrom (k + 1) ds n

/-- The arguments of the `%w` directives `ds`, among `n` arguments (Go's `wrappedErrs`). -/
def wrapArgs (ds : List Directive) (n : Nat) : List Nat := wrapArgsFrom 0 ds n

theorem wrapArgsFrom_of_le {k n : Nat} (ds : List Directive) (h : n ≤ k) :
    wrapArgsFrom k ds n = [] := by
  induction ds generalizing k with
  | nil => rfl
  | cons d ds ih =>
    have hk : ¬ (d.verb = W8 119 ∧ k < n) := fun h' => by omega
    simp only [wrapArgsFrom, ih (by omega : n ≤ k + 1), List.append_nil, hk, ↓reduceIte]

theorem wrapArgsFrom_cons_ne {k n : Nat} (d : Directive) (ds : List Directive)
    (h : d.verb ≠ W8 119) : wrapArgsFrom k (d :: ds) n = wrapArgsFrom (k + 1) ds n := by
  simp only [wrapArgsFrom, h, false_and, ↓reduceIte, List.nil_append]

/-! Equations of the parser, for the proofs of the model. -/

theorem fmtDirectivesAux_lit {c : w8} (f : GoString) (h : c ≠ W8 37) :
    fmtDirectivesAux none (c :: f) = fmtDirectivesAux none f := by
  simp only [fmtDirectivesAux, h, ↓reduceIte]

theorem fmtDirectivesAux_pct (f : GoString) :
    fmtDirectivesAux none (W8 37 :: f) = fmtDirectivesAux (some (false, .flags)) f := by
  simp [fmtDirectivesAux]

theorem fmtDirectivesAux_pct_pct (f : GoString) :
    fmtDirectivesAux none (W8 37 :: W8 37 :: f) = fmtDirectivesAux none f := by
  simp [fmtDirectivesAux]

/-- A directive `%c` without flags, width or precision, `c` one of `s v x d`: one directive of verb
`c`, then the rest. -/
theorem fmtDirectivesAux_simple {c : w8} (f : GoString)
    (hc : c = W8 115 ∨ c = W8 118 ∨ c = W8 120 ∨ c = W8 100) :
    fmtDirectivesAux none (W8 37 :: c :: f) =
      (⟨c, false⟩ :: ·) <$> fmtDirectivesAux none f := by
  rcases hc with rfl | rfl | rfl | rfl <;> simp [fmtDirectivesAux]

/-- The digits after a `%0`, then `d` or `x` (`parseIntVerb`'s `%0Nd`, `%0Nx`): one directive of
that verb, or `none` (a run of more than `maxNumDigits` digits). In flags phase or in a width
phase. -/
theorem fmtDirectivesAux_digits_d (ds f : GoString) (hds : ∀ c ∈ ds, 48 ≤ c.toNat ∧ c.toNat ≤ 57)
    (sharp : Bool) (ph : DirPhase) (hph : ph = .flags ∨ ∃ n, ph = .width n) (hsharp : sharp = false)
    (v : w8) (hv : v = W8 100 ∨ v = W8 120) :
    fmtDirectivesAux (some (sharp, ph)) (ds ++ v :: f) = none ∨
      fmtDirectivesAux (some (sharp, ph)) (ds ++ v :: f) =
        (⟨v, false⟩ :: ·) <$> fmtDirectivesAux none f := by
  subst hsharp
  induction ds generalizing ph with
  | nil =>
    right
    rcases hv with rfl | rfl <;> rcases hph with rfl | ⟨n, rfl⟩ <;> simp [fmtDirectivesAux]
  | cons c ds ih =>
    have hc := hds c (by simp)
    have hds' : ∀ c ∈ ds, 48 ≤ c.toNat ∧ c.toNat ≤ 57 := fun c' h => hds c' (by simp [h])
    have h1 : c ≠ W8 35 := by rintro rfl; simp at hc
    have h4 : ¬ (c = W8 46) := by rintro rfl; simp at hc
    rcases hph with rfl | ⟨n, rfl⟩
    · by_cases h0 : c = W8 48
      · subst h0
        simp only [List.cons_append, fmtDirectivesAux]
        simp only [show ¬ (W8 48 : w8) = W8 35 by decide, ↓reduceIte, true_or, or_true]
        exact ih hds' _ (.inl rfl)
      · have h2 : ¬ (c = W8 43 ∨ c = W8 45 ∨ c = W8 48 ∨ c = W8 32) := by
          rintro (rfl | rfl | rfl | rfl) <;> simp_all
        simp only [List.cons_append, fmtDirectivesAux, h1, h2, ↓reduceIte, hc, and_self]
        exact ih hds' _ (.inr ⟨1, rfl⟩)
    · simp only [List.cons_append, fmtDirectivesAux, hc, and_self, ↓reduceIte]
      by_cases hn : n < maxNumDigits
      · simp only [hn, ↓reduceIte]; exact ih hds' _ (.inr ⟨n + 1, rfl⟩)
      · simp only [hn, ↓reduceIte]; left; trivial

/-! The directives the model of `Sprintf` formats exactly (its helper `formatArg`): one, consuming
an argument, of verb neither `w` nor `T`. -/

/-- At the `%` at `format[i]`, a directive that consumes an argument, of verb neither `w` nor `T`,
ending at `next` (as far as `fmtDirectivesAux` reads it at all). -/
def AuxStepF (f rest : GoString) : Prop :=
  ∀ L, fmtDirectivesAux none (W8 37 :: f) = some L →
    ∃ d L', L = d :: L' ∧ d.verb ≠ W8 119 ∧ d.verb ≠ W8 84 ∧ fmtDirectivesAux none rest = some L'

/-- `AuxStepF` at the `%` at `format[i]`, the directive ending at `next`. -/
def AuxStep (format : GoString) (i next : Nat) : Prop :=
  AuxStepF (format.drop (i + 1)) (format.drop next)

theorem auxStepF_simple (rest : GoString) (c : w8)
    (hc : c = W8 115 ∨ c = W8 118 ∨ c = W8 120 ∨ c = W8 100) : AuxStepF (c :: rest) rest := by
  intro L hL
  rw [fmtDirectivesAux_simple _ hc] at hL
  cases hL' : fmtDirectivesAux none rest with
  | none => rw [hL'] at hL; cases hL
  | some L' =>
    rw [hL'] at hL
    simp only [Option.map_eq_map, Option.map_some, Option.some.injEq] at hL
    subst hL
    refine ⟨_, L', rfl, ?_, ?_, rfl⟩ <;> (rcases hc with rfl | rfl | rfl | rfl <;> decide)

theorem scanWidth_split (w : Nat) (f : GoString) :
    ∃ ds, f = ds ++ (scanWidth w f).2 ∧ ∀ c ∈ ds, 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
  induction f generalizing w with
  | nil => exact ⟨[], by simp [scanWidth], by simp⟩
  | cons c f ih =>
    by_cases hc : 48 ≤ uint.Z c ∧ uint.Z c ≤ 57 ∧ w ≤ 1000000
    · obtain ⟨ds, hds, hall⟩ := ih (w * 10 + (uint.nat c - 48))
      refine ⟨c :: ds, ?_, ?_⟩
      · simp only [scanWidth, hc, and_self, ↓reduceIte]
        rw [List.cons_append, ← hds]
      · intro c' hc'
        rcases List.mem_cons.mp hc' with rfl | h
        · simp only [uint.Z] at hc; omega
        · exact hall c' h
    · refine ⟨[], ?_, by simp⟩
      simp only [scanWidth, hc, ↓reduceIte, List.nil_append]

theorem auxStep_simple (format : GoString) (i next : Nat) (c : w8)
    (hc : c = W8 115 ∨ c = W8 118 ∨ c = W8 120 ∨ c = W8 100)
    (h : format.drop (i + 1) = c :: format.drop next) : AuxStep format i next := by
  unfold AuxStep; rw [h]; exact auxStepF_simple _ c hc

theorem auxStepF_int (g tail : GoString) (v : w8) (w : Nat)
    (h : parseIntVerb g = some (v, w, tail)) : AuxStepF g tail := by
  cases hf : g with
  | nil => rw [hf] at h; simp [parseIntVerb] at h
  | cons c f =>
    rw [hf] at h
    by_cases hdv : c = W8 100 ∨ c = W8 118
    · simp only [parseIntVerb, hdv, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2.2]
      exact auxStepF_simple f c (by rcases hdv with h | h <;> simp [h])
    · have h0 : c = W8 48 := by
        apply Classical.byContradiction; intro h0
        simp only [parseIntVerb] at h
        rw [if_neg hdv, if_neg h0] at h
        cases h
      subst h0
      intro L hL
      obtain ⟨ds, hds, hall⟩ := scanWidth_split 0 f
      have hd48 : (W8 48 : w8) = W8 48 := rfl
      simp only [parseIntVerb, hdv, ↓reduceIte] at h
      revert h hds
      cases hsw : scanWidth 0 f with
      | mk w' r =>
        cases r with
        | nil => simp
        | cons d rest =>
          intro hds h
          simp only at h hds
          by_cases hcond : (d :: rest).length < f.length ∧ (d = W8 100 ∨ d = W8 120) ∧ w' ≤ 1000000
          · rw [if_pos hcond] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨-, -, hrest⟩ := h
            obtain ⟨-, hdv, -⟩ := hcond
            rw [hds] at hL
            simp only [fmtDirectivesAux_pct] at hL
            have hstep : fmtDirectivesAux (some (false, .flags)) (W8 48 :: (ds ++ d :: rest)) =
                fmtDirectivesAux (some (false, .flags)) (ds ++ d :: rest) := by
              simp [fmtDirectivesAux]
            rw [hstep] at hL
            rcases fmtDirectivesAux_digits_d ds rest hall false .flags (.inl rfl) rfl d hdv with hn | hc
            · rw [hn] at hL; cases hL
            · rw [hc, hrest] at hL
              cases hL' : fmtDirectivesAux none tail with
              | none => rw [hL'] at hL; cases hL
              | some L' =>
                rw [hL'] at hL
                simp only [Option.map_eq_map, Option.map_some, Option.some.injEq] at hL
                subst hL
                exact ⟨_, L', rfl, by rcases hdv with rfl | rfl <;> decide,
                  by rcases hdv with rfl | rfl <;> decide, rfl⟩
          · rw [if_neg hcond] at h; cases h

/-- The directives `formatArg` reads its argument at: `%s`, `%v`, `%x`, an integer directive. -/
theorem auxStepF_of_cond (f : GoString)
    (h : f.head? = some (W8 115) ∨ f.head? = some (W8 118) ∨ f.head? = some (W8 120) ∨
      (parseIntVerb f).isSome) : ∃ rest, AuxStepF f rest := by
  rcases h with h | h | h | h
  · cases f with
    | nil => cases h
    | cons c r => simp only [List.head?_cons, Option.some.injEq] at h; subst h
                  exact ⟨r, auxStepF_simple r _ (.inl rfl)⟩
  · cases f with
    | nil => cases h
    | cons c r => simp only [List.head?_cons, Option.some.injEq] at h; subst h
                  exact ⟨r, auxStepF_simple r _ (.inr (.inl rfl))⟩
  · cases f with
    | nil => cases h
    | cons c r => simp only [List.head?_cons, Option.some.injEq] at h; subst h
                  exact ⟨r, auxStepF_simple r _ (.inr (.inr (.inl rfl)))⟩
  · cases hp : parseIntVerb f with
    | none => rw [hp] at h; cases h
    | some p => exact ⟨p.2.2, auxStepF_int f p.2.2 p.1 p.2.1 hp⟩

theorem auxStep_int (format : GoString) (i next : Nat) (v : w8) (w : Nat)
    (h : parseIntVerb (format.drop (i + 1)) = some (v, w, format.drop next)) :
    AuxStep format i next :=
  auxStepF_int _ _ v w h

end fmt

end Perennial
