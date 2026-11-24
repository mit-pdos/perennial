/-
The proof of `fmt.Errorf` (Go's) and of the Go model of `errorf` (`goose/model/overlay/fmt`): the
model printer's `doPrintf` (`Perennial/Proof/fmt/DoPrintf.lean`) into the buffer of a printer from
`newPrinter`, the message read back from it, then `errorfResult`, from `errors.New`'s code
(`errors.wp_New_errorString_cell`), and `pp.free`.
-/
module

public import Perennial.Spec.fmt.Errorf
public import Perennial.Proof.fmt.DoPrintf
public import Perennial.Proof.errors.NewVar
public import Perennial.Spec.internal.stringslite.IndexByte
public import Perennial.Spec.internal.gomodel.ChooseUint64
public import Perennial.Spec.fmt.newPrinter
public import Perennial.Spec.fmt.pp__free

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : fmt.Assumptions]

theorem fmt.wrapError_ty_eq : fmt.wrapError.ty = go.GoType.Named go!"fmt.wrapError" [] := by
  unfold fmt.wrapError.ty; rfl

theorem fmt.wrapErrors_ty_eq : fmt.wrapErrors.ty = go.GoType.Named go!"fmt.wrapErrors" [] := by
  unfold fmt.wrapErrors.ty; rfl

theorem fmt.errFacts (t : go.GoType) {ms : List (GoString × Option go.signature)} [go.MethodSetIs t ms]
    (hF : go.methodSetLookup ms go!"Format" = none)
    (hE : go.methodSetLookup ms go!"Error" = some (some fmt.noArgStringSig)) :
    methodSet t !! go!"Format" = none ∧ methodSet t !! go!"Error" = some fmt.noArgStringSig := by
  have h1 := go.MethodSetIs.method_set_is (t := t) go!"Format"
  have h2 := go.MethodSetIs.method_set_is (t := t) go!"Error"
  rw [hF] at h1; rw [hE] at h2; exact ⟨h1, h2⟩

theorem fmt.errorString_facts :
    methodSet (go.GoType.PointerType errors.errorString.ty) !! go!"Format" = none ∧
    methodSet (go.GoType.PointerType errors.errorString.ty) !! go!"Error" = some fmt.noArgStringSig :=
  fmt.errFacts _ (by decide) (by simp [go.methodSetLookup, fmt.noArgStringSig])

theorem fmt.wrapError_facts :
    methodSet (go.GoType.PointerType fmt.wrapError.ty) !! go!"Format" = none ∧
    methodSet (go.GoType.PointerType fmt.wrapError.ty) !! go!"Error" = some fmt.noArgStringSig :=
  fmt.errFacts _ (by decide) (by simp [go.methodSetLookup, fmt.noArgStringSig])

theorem fmt.wrapErrors_facts :
    methodSet (go.GoType.PointerType fmt.wrapErrors.ty) !! go!"Format" = none ∧
    methodSet (go.GoType.PointerType fmt.wrapErrors.ty) !! go!"Error" = some fmt.noArgStringSig :=
  fmt.errFacts _ (by decide) (by simp [go.methodSetLookup, fmt.noArgStringSig])

theorem fmt.W64_nat_inj {a b : Nat} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63)
    (h : W64 (a : Int) = W64 (b : Int)) : a = b := by
  have : uint.Z (W64 (a : Int)) = uint.Z (W64 (b : Int)) := by rw [h]
  rw [uint_Z_W64 _ (by omega) (by omega), uint_Z_W64 _ (by omega) (by omega)] at this
  omega

/-- The model's `errorfResult s wrapped unknown a`, of the results of `doPrintf(&p.buf, format, a, true)`
(`s` read back from `p.buf`): the
error `Errorf` returns (`errorfErr`). -/
theorem fmt.wp_errorfResult
    (wp_ChooseUint64 : internal.gomodel.ChooseUint64.spec (GF := GF) (hG := hG))
    (format : GoString) (args_sl : GoSlice) (xs : List GoInterface) (dq : DFrac)
    (s : GoString) (wsl : GoSlice) (unk : Bool) (ws : List w64) :
    {{ (args_sl ↦*{dq} xs : IProp GF) ∗ wsl ↦* ws ∗ ⌜SprintfOut format xs s⌝ ∗
        ⌜(unk = true → ArgsWf xs ∧ fmt.fmtDirectives format = none) ∧
         (unk = false → ∀ ds, fmt.fmtDirectives format = some ds →
            ws = (fmt.wrapArgs ds xs.length).map (fun j : Nat => W64 (j : Int))) ∧
         (unk = false → ∀ w ∈ ws, ∃ j : Nat, w = W64 (j : Int) ∧ j < xs.length)⌝ }}
      (App (App (App (App (Val (@! fmt.errorfResult)) (Val #s)) (Val #wsl)) (Val #unk)) (Val #args_sl))
    {{ (err : GoInterfaceOk), RET #(interface.ok err);
        args_sl ↦*{dq} xs ∗ ∃ s : GoString, ⌜SprintfOut format xs s⌝ ∗ fmt.errorfErr format xs s err }} := by
  wp_start as ⟨Hsl, Hws, %Hs, %Hwr⟩
  wp_auto
  try rw [← fmt.wrapError_ty_eq, ← fmt.wrapErrors_ty_eq]
  cases unk
  · obtain hk := Hwr.2.1 rfl
    obtain hb := Hwr.2.2 rfl
    ihave %Hwlen := ownSlice_len $$ Hws
    ihave %Hxlen := ownSlice_len $$ Hsl
    have hn63 : xs.length < 2 ^ 63 := by word
    wp_auto
    wp_if_destruct
    · -- no `%w`: `errors.New(s)`
      have hws0 : ws = [] := List.eq_nil_of_length_eq_zero (by rw [Hwlen.1, Hif]; rfl)
      wp_apply errors.wp_New_errorString_cell as %x ⟨#Hcell, #HErr⟩
      iapply HΦ
      iframe
      iexists s
      isplitr
      · ipureintro; exact Hs
      unfold fmt.errorfErr
      isplitr
      · ipureintro; exact ⟨⟨_, x, rfl, rfl⟩, fmt.errorString_facts.1, fmt.errorString_facts.2, .inl rfl⟩
      isplitr
      · iexact HErr
      cases hf : fmt.fmtDirectives format with
      | none => itrivial
      | some ds =>
        have hw := hk ds hf
        rw [hws0] at hw
        have hnil : fmt.wrapArgs ds xs.length = [] := List.map_eq_nil_iff.mp hw.symm
        simp only [hnil]
        iexists x
        isplitr
        · ipureintro; rfl
        iexact Hcell
    have hne0 := Hif
    wp_if_destruct
    · -- one `%w`: a `*wrapError`
      obtain ⟨w, hws1⟩ : ∃ w, ws = [w] := by
        cases ws with
        | nil => simp at Hwlen; word
        | cons w ws' =>
          cases ws' with
          | nil => exact ⟨w, rfl⟩
          | cons w' ws'' => simp at Hwlen; word
      subst hws1
      obtain ⟨j, rfl, hj⟩ := hb _ (List.mem_singleton_self _)
      have hjlt : j < xs.length := hj
      obtain ⟨x, Hx⟩ : ∃ x, xs[j]? = some x := ⟨_, List.getElem?_eq_getElem hjlt⟩
      iStructNamed «$r0»
      simp only [show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z wsl.len from ⟨by word, by word⟩,
        _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index wsl (sint.Z (W64 0)) [W64 (j : Int)] (DFrac.own 1) (W64 (j : Int))
        (by word) $$ [Hws] with Hws
      · iframe; ipureintro; rfl
      simp only [show 0 ≤ sint.Z (W64 (j : Int)) ∧ sint.Z (W64 (j : Int)) < sint.Z args_sl.len from
        ⟨by word, by word⟩, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index args_sl (sint.Z (W64 (j : Int))) xs dq x (by word) $$ [Hsl] with Hsl
      · iframe; ipureintro; rw [show (sint.Z (W64 (j : Int))).toNat = j by word]; exact Hx
      have hcases : (x = .nil ∧ fmt.asError x = .nil) ∨
          (∃ ii, x = .ok ii ∧ go.typeSetContains ii.ty go.error = true ∧ fmt.asError x = .ok ii) ∨
          (∃ ii, x = .ok ii ∧ go.typeSetContains ii.ty go.error = false ∧ fmt.asError x = .nil) := by
        cases x with
        | nil => exact .inl ⟨rfl, rfl⟩
        | ok ii =>
          cases h : go.typeSetContains ii.ty go.error
          · exact .inr (.inr ⟨ii, rfl, h, by simp [fmt.asError, h]⟩)
          · exact .inr (.inl ⟨ii, rfl, h, by simp [fmt.asError, h]⟩)
      rcases hcases with ⟨rfl, hae⟩ | ⟨ii, rfl, htc, hae⟩ | ⟨ii, rfl, htc, hae⟩
      all_goals
        ipersist msg
        try simp only [htc, ↓reduceIte, Bool.false_eq_true]
        wp_pures
        wp_store
        ipersist err
        wp_auto
        iapply HΦ
        iframe
        iexists s
        isplitr
        · ipureintro; exact Hs
        unfold fmt.errorfErr
        isplitr
        · ipureintro; exact ⟨⟨_, «$r0_ptr», rfl, rfl⟩, fmt.wrapError_facts.1, fmt.wrapError_facts.2, .inr (.inl rfl)⟩
        isplitr
        · imodintro
          iintro %Φ' HΦ'
          rw [method_unfold]
          wp_auto
          iexact HΦ'
        cases hf : fmt.fmtDirectives format with
        | none => itrivial
        | some ds =>
          have hw := hk ds hf
          obtain ⟨j', hj'⟩ : ∃ j', fmt.wrapArgs ds xs.length = [j'] := by
            cases h : fmt.wrapArgs ds xs.length with
            | nil => rw [h] at hw; simp at hw
            | cons a t =>
              cases t with
              | nil => exact ⟨a, rfl⟩
              | cons b t' => rw [h] at hw; simp at hw
          rw [hj'] at hw
          simp only [List.map_cons, List.map_nil, List.cons.injEq, _root_.and_true] at hw
          have hj'mem : j' ∈ fmt.wrapArgsFrom 0 ds xs.length := by
            have : fmt.wrapArgsFrom 0 ds xs.length = [j'] := hj'
            rw [this]; exact List.mem_singleton_self _
          have hj'lt : j' < xs.length := (fmt.wrapArgsFrom_bound hj'mem).2
          have hjj : j = j' := fmt.W64_nat_inj (by omega) (by omega) hw
          subst hjj
          simp only [hj', Hx, Option.getD_some, hae]
          iexists «$r0_ptr»
          isplitr
          · ipureintro; rfl
          isplitr
          · iexact msg
          · iexact err
    -- several `%w`: a `*wrapErrors`
    have hlen2 : 2 ≤ ws.length := by
      have h1 := Hif
      rw [Hwlen.1]
      word
    ihave Hes0 := ownSlice_nil (V := GoInterface) (GF := GF) (DFrac.own 1)
    ihave Hec0 := ownSliceCap_nil (V := GoInterface) (GF := GF)
    ihave IH : iprop(∃ (m : w64) (av : w64) (esl : GoSlice) (es : List GoInterface),
        "i" ∷ i_ptr ↦ m ∗ "argNum" ∷ argNum_ptr ↦ av ∗ "errs" ∷ errs_ptr ↦ esl ∗
        "Hes" ∷ esl ↦* es ∗ "Hec" ∷ ownSliceCap GoInterface esl (DFrac.own 1) ∗
        "%Hm" ∷ ⌜0 ≤ sint.Z m ∧ sint.Z m ≤ (ws.length : Int)⌝) $$ [i argNum errs Hes0 Hec0]
    · iexists _, _, slice.nil, []
      rw [show zero_val GoSlice = slice.nil from rfl]
      iframe
      isplitr
      · iexact Hes0
      isplitr
      · iexact Hec0
      ipureintro; exact ⟨by word, by word⟩
    wp_for IH
    wp_if_destruct
    · have Hmlt : sint.nat m < ws.length := by word
      obtain ⟨w, Hw⟩ : ∃ w, ws[sint.nat m]? = some w := ⟨_, List.getElem?_eq_getElem Hmlt⟩
      obtain ⟨j, rfl, hj⟩ := hb w (List.mem_of_getElem? Hw)
      obtain ⟨x, Hx⟩ : ∃ x, xs[j]? = some x := ⟨_, List.getElem?_eq_getElem hj⟩
      simp only [show 0 ≤ sint.Z m ∧ sint.Z m < sint.Z wsl.len from ⟨Hm.1, by word⟩,
        _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index wsl (sint.Z m) ws (DFrac.own 1) (W64 (j : Int)) Hm.1 $$ [Hws] with Hws
      · iframe; ipureintro; rw [show (sint.Z m).toNat = sint.nat m from rfl]; exact Hw
      simp only [show 0 ≤ sint.Z (W64 (j : Int)) ∧ sint.Z (W64 (j : Int)) < sint.Z args_sl.len from
        ⟨by word, by word⟩, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index args_sl (sint.Z (W64 (j : Int))) xs dq x (by word) $$ [Hsl] with Hsl
      · iframe; ipureintro; rw [show (sint.Z (W64 (j : Int))).toNat = j by word]; exact Hx
      cases x with
      | nil =>
        wp_auto
        wp_for_post
        iframe
        iexists _, _, _, _
        iframe
        ipureintro; exact ⟨by word, by word⟩
      | ok ii =>
        wp_auto
        cases htc : go.typeSetContains ii.ty go.error
        · simp only [htc, Bool.false_eq_true, ↓reduceIte]
          wp_auto
          wp_for_post
          iframe
          iexists _, _, _, _
          iframe
          ipureintro; exact ⟨by word, by word⟩
        · simp only [htc, ↓reduceIte]
          wp_auto
          wp_apply wp_slice_literal (V := GoInterface) [GoInterface.ok ii]
          isplitr
          · ipureintro; rfl
          iintro %sl2 ⟨Hsl2, -⟩
          wp_apply wp_slice_append $$ [$Hes $Hec $Hsl2] as %esl' ⟨Hes, Hec, -⟩
          wp_for_post
          iframe
          iexists _, _, _, _
          iframe
          ipureintro; exact ⟨by word, by word⟩
    · wp_alloc l as Hl
      iStructNamed Hl
      ipersist msg
      wp_auto
      iapply HΦ
      iframe
      iexists s
      isplitr
      · ipureintro; exact Hs
      unfold fmt.errorfErr
      isplitr
      · ipureintro; exact ⟨⟨_, l, rfl, rfl⟩, fmt.wrapErrors_facts.1, fmt.wrapErrors_facts.2, .inr (.inr rfl)⟩
      isplitr
      · imodintro
        iintro %Φ' HΦ'
        rw [method_unfold]
        wp_auto
        iexact HΦ'
      cases hf : fmt.fmtDirectives format with
      | none => itrivial
      | some ds =>
        have hw := hk ds hf
        have hl : 2 ≤ (fmt.wrapArgs ds xs.length).length := by
          rw [hw, List.length_map] at hlen2; exact hlen2
        obtain ⟨a, b, t, hab⟩ : ∃ a b t, fmt.wrapArgs ds xs.length = a :: b :: t := by
          cases h : fmt.wrapArgs ds xs.length with
          | nil => rw [h] at hl; simp at hl
          | cons a t =>
            cases t with
            | nil => rw [h] at hl; simp at hl
            | cons b t' => exact ⟨a, b, t', rfl⟩
        simp only [hab]
        iexists l
        isplitr
        · ipureintro; rfl
        iexact msg
  · -- a directive the model does not follow: any of the three errors
    obtain ⟨hwf, hnone⟩ := Hwr.1 rfl
    simp only [fmt.errorfErr, hnone]
    wp_auto
    wp_apply wp_ChooseUint64 as %n -
    wp_if_destruct
    · wp_apply errors.wp_New_errorString_cell as %x ⟨#Hcell, #HErr⟩
      iapply HΦ
      iframe
      iexists s
      isplitr
      · ipureintro; exact Hs
      isplitr
      · ipureintro; exact ⟨⟨_, x, rfl, rfl⟩, fmt.errorString_facts.1, fmt.errorString_facts.2, .inl rfl⟩
      isplitr
      · iexact HErr
      itrivial
    wp_if_destruct
    · wp_alloc l as Hl
      iStructNamed Hl
      ipersist msg
      wp_auto
      iapply HΦ
      iframe
      iexists s
      isplitr
      · ipureintro; exact Hs
      isplitr
      · ipureintro; exact ⟨⟨_, l, rfl, rfl⟩, fmt.wrapError_facts.1, fmt.wrapError_facts.2, .inr (.inl rfl)⟩
      imodintro
      iintro %Φ' HΦ'
      rw [method_unfold]
      wp_auto
      iexact HΦ'
    wp_alloc l as Hl
    iStructNamed Hl
    ipersist msg
    wp_auto
    iapply HΦ
    iframe
    iexists s
    isplitr
    · ipureintro; exact Hs
    isplitr
    · ipureintro; exact ⟨⟨_, l, rfl, rfl⟩, fmt.wrapErrors_facts.1, fmt.wrapErrors_facts.2, .inr (.inr rfl)⟩
    imodintro
    iintro %Φ' HΦ'
    rw [method_unfold]
    wp_auto
    iexact HΦ'

/-- A format without `%` gives itself, of no argument. -/
theorem fmt.SprintfOut_noPct (f : GoString) (h : ∀ j : Nat, f[j]? ≠ some (W8 37)) :
    SprintfOut f [] f := by
  induction f with
  | nil => exact .done
  | cons c f ih =>
    have hc : c ≠ W8 37 := fun hc => h 0 (by simp [hc])
    exact .byte c f [] f hc (ih (fun j hj => h (j + 1) (by simpa using hj)))

/-- A format without `%` has no directive. -/
theorem fmt.fmtDirectives_noPct (f : GoString) (h : ∀ j : Nat, f[j]? ≠ some (W8 37)) :
    fmt.fmtDirectives f = some [] := by
  unfold fmt.fmtDirectives
  induction f with
  | nil => rfl
  | cons c f ih =>
    have hc : c ≠ W8 37 := fun hc => h 0 (by simp [hc])
    rw [fmt.fmtDirectivesAux, if_neg hc]
    exact ih (fun j hj => h (j + 1) (by simpa using hj))

theorem fmt.Errorf.wp_proof
    (wp_IndexByte : internal.stringslite.IndexByte.spec (GF := GF) (hG := hG))
    (wp_newPrinter : fmt.newPrinter.spec (GF := GF) (hG := hG))
    (wp_writeString : fmt.buffer.writeString.spec (GF := GF) (hG := hG))
    (wp_free : fmt.pp.free.spec (GF := GF) (hG := hG))
    (wp_Choose : internal.gomodel.Choose.spec (GF := GF) (hG := hG))
    (wp_ChooseUint64 : internal.gomodel.ChooseUint64.spec (GF := GF) (hG := hG)) :
    fmt.Errorf.spec (GF := GF) (hG := hG) := by
  intro format args_sl xs dq
  wp_start as ⟨Hsl, Hok⟩
  wp_auto
  -- `errorf(format, a...)`
  wp_func_call
  wp_call
  wp_auto
  ihave %Hxlen := ownSlice_len $$ Hsl
  wp_if_destruct
  · have Hlen0 := Hif
    wp_apply wp_IndexByte as %Hflen
    wp_if_destruct
    · -- Go's shortcut: no argument and no `%`; `errorf` returns `nil`, `Errorf` `errors.New(format)`
      have hxs : xs = [] := List.eq_nil_of_length_eq_zero (by have := congrArg sint.Z Hlen0; word)
      subst hxs
      have hneg : internal.bytealg.indexByte format (W8 37) = -1 := by
        have := internal.bytealg.indexByte_bounds format (W8 37)
        have h2 := congrArg sint.Z Hif
        word
      have hnp : ∀ j : Nat, format[j]? ≠ some (W8 37) := by
        rcases internal.bytealg.indexByte_slice_cases format (W8 37) 0 format.length with
          ⟨r, hr, hrl, -, -⟩ | ⟨-, hn⟩
        · simp at hr
          have h' := hneg
          simp at h'
          omega
        · intro j hj
          have hjl : j < format.length := (List.getElem?_eq_some_iff.mp hj).1
          exact hn j hjl (by simpa using hj)
      try wp_auto
      wp_apply errors.wp_New_errorString_cell as %x ⟨#Hcell, #HErr⟩
      try wp_auto
      iapply HΦ
      iframe
      iexists format
      isplitr
      · ipureintro; exact fmt.SprintfOut_noPct format hnp
      unfold fmt.errorfErr
      isplitr
      · ipureintro; exact ⟨⟨_, x, rfl, rfl⟩, fmt.errorString_facts.1, fmt.errorString_facts.2, .inl rfl⟩
      isplitr
      · iexact HErr
      rw [fmt.fmtDirectives_noPct format hnp]
      dsimp only [fmt.wrapArgs, fmt.wrapArgsFrom]
      iexists x
      isplitr
      · ipureintro; rfl
      iexact Hcell
    · try wp_auto
      wp_apply wp_newPrinter as %p Hp
      unfold fmt.isPrinterAny fmt.isPrinter fmt.isPrinterA
      icases Hp with ⟨%hnn, %F, %wid, %prec, %x', Hb, Hrest⟩
      have hdo := fmt.wp_doPrintf wp_Choose wp_ChooseUint64 wp_writeString (p.[fmt.pp, go!"buf"]) []
        format args_sl xs dq true
      rw [fmt.modeVerbs_true] at hdo
      wp_apply hdo $$ [$Hb $Hsl $Hok] as %wsl %unk ⟨%s, Hb, Hsl, %Hs, %ws, Hws, %Hwr⟩
      try wp_auto
      unfold fmt.bufferOwn
      icases Hb with ⟨%sl, Hb, Hbs, Hcap⟩
      wp_auto
      wp_apply wp_bytes_to_string sl ([] ++ s) (DFrac.own 1) $$ Hbs as Hbs
      try wp_auto
      wp_apply (fmt.wp_errorfResult wp_ChooseUint64 format args_sl xs dq ([] ++ s) wsl unk ws) $$ [$Hsl $Hws]
        as %err ⟨Hsl, HE⟩
      · ipureintro; exact ⟨Hs, Hwr⟩
      try wp_auto
      wp_apply wp_free p ([] ++ s) $$ [Hb Hbs Hcap Hrest]
      · iframe
        unfold fmt.isPrinterAny fmt.isPrinter fmt.isPrinterA fmt.bufferOwn
        isplitr
        · ipureintro; exact hnn
        iexists F, wid, prec, x'
        iframe
      try wp_auto
      iapply HΦ
      iframe
  · try wp_auto
    wp_apply wp_newPrinter as %p Hp
    unfold fmt.isPrinterAny fmt.isPrinter fmt.isPrinterA
    icases Hp with ⟨%hnn, %F, %wid, %prec, %x', Hb, Hrest⟩
    have hdo := fmt.wp_doPrintf wp_Choose wp_ChooseUint64 wp_writeString (p.[fmt.pp, go!"buf"]) []
      format args_sl xs dq true
    rw [fmt.modeVerbs_true] at hdo
    wp_apply hdo $$ [$Hb $Hsl $Hok] as %wsl %unk ⟨%s, Hb, Hsl, %Hs, %ws, Hws, %Hwr⟩
    try wp_auto
    unfold fmt.bufferOwn
    icases Hb with ⟨%sl, Hb, Hbs, Hcap⟩
    wp_auto
    wp_apply wp_bytes_to_string sl ([] ++ s) (DFrac.own 1) $$ Hbs as Hbs
    try wp_auto
    wp_apply (fmt.wp_errorfResult wp_ChooseUint64 format args_sl xs dq ([] ++ s) wsl unk ws) $$ [$Hsl $Hws]
      as %err ⟨Hsl, HE⟩
    · ipureintro; exact ⟨Hs, Hwr⟩
    try wp_auto
    wp_apply wp_free p ([] ++ s) $$ [Hb Hbs Hcap Hrest]
    · iframe
      unfold fmt.isPrinterAny fmt.isPrinter fmt.isPrinterA fmt.bufferOwn
      isplitr
      · ipureintro; exact hnn
      iexists F, wid, prec, x'
      iframe
    try wp_auto
    iapply HΦ
    iframe

end proof

end Perennial
