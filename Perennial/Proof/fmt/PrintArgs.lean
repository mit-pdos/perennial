/-
What `fmt.Fprint`'s spec needs of its operands (`printArgOk R`): each is printed under `%v` by Go's
`printArg`, calling at most its `Error()` or `String()`, which may need a resource `R` the caller
lends (and gets back); and the spec of the model's `visitArg` under `%v` for such an operand.
-/
module

public import Perennial.Proof.fmt.VisitModel
public import Perennial.Spec.bytes.Buffer__String

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace fmt

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : fmt.Assumptions]

/-- Method `m` of the interface value `ii`, called with no arguments, given `R`, returns some string
and gives `R` back (persistently: the spec may be used for several calls). `stringMethodSpec` is the
case `R = True` (`stringMethodSpecR_of_stringMethodSpec`). -/
def stringMethodSpecR (ii : GoInterfaceOk) (m : GoString) (R : IProp GF) : IProp GF :=
  iprop(□ ∀ Φ : val → IProp GF, R -∗ ▷ (∀ s : GoString, R -∗ Φ #s) -∗
    WP (App (Val #(methods ii.ty m ii.v)) (Val #())) {{ Φ }})

instance stringMethodSpecR_persistent (ii : GoInterfaceOk) (m : GoString) (R : IProp GF) :
    Persistent (stringMethodSpecR (GF := GF) ii m R) := by
  unfold stringMethodSpecR; infer_instance

theorem stringMethodSpecR_of_stringMethodSpec (ii : GoInterfaceOk) (m : GoString) (R : IProp GF) :
    stringMethodSpec (GF := GF) ii m ⊢ stringMethodSpecR ii m R := by
  unfold stringMethodSpec stringMethodSpecR
  iintro #H
  imodintro
  iintro %Φ HR HΦ
  iapply H
  inext
  iintro %s
  iapply HΦ $$ HR

/-- **One operand of `Fprint`**, printed under `%v` (Go's `printArg(arg, 'v')`), calling at most
a method whose spec needs the lent resource `R`: `nil`; an `ArgWf` value (Go calls no method of
it); a value without a `Format` method whose `Error() string` has `stringMethodSpecR` (Go's
`handleMethods` calls `Error()`); or a value with neither a `Format` nor an `Error` method, nor
`CanInterface` (not a `reflect.Value`), whose `String() string` has it (Go calls `String()`). A
panic of the method, which Go's `catchPanic` would recover, is ruled out by the WP (the model is
stuck there). -/
def printArgOk (R : IProp GF) : GoInterface → IProp GF
  | .nil => iprop(True)
  | .ok ii => iprop(⌜ArgWf ii⌝ ∨
      (stringMethodSpecR ii go!"Error" R ∗
        ⌜methodSet ii.ty !! go!"Format" = none ∧ methodSet ii.ty !! go!"Error" = some noArgStringSig⌝) ∨
      (stringMethodSpecR ii go!"String" R ∗
        ⌜methodSet ii.ty !! go!"Format" = none ∧ methodSet ii.ty !! go!"Error" = none ∧
          methodSet ii.ty !! go!"String" = some noArgStringSig ∧
          methodSet ii.ty !! go!"CanInterface" = none⌝))

instance printArgOk_persistent (R : IProp GF) (x : GoInterface) :
    Persistent (printArgOk (GF := GF) R x) := by
  cases x <;> unfold printArgOk <;> infer_instance

/-- An argument `argOk` (the operands of the `printf` family's specs under a method verb) is a
`printArgOk` for any `R`. -/
theorem printArgOk_of_argOk (R : IProp GF) (x : GoInterface) :
    argOk (GF := GF) x ⊢ printArgOk R x := by
  cases x with
  | nil => unfold printArgOk; iintro -; itrivial
  | ok ii =>
    unfold argOk printArgOk
    iintro (%h | ⟨#H, %h⟩ | ⟨#H, %h⟩)
    · ileft; ipureintro; exact h
    · iright; ileft
      isplitl
      · iapply stringMethodSpecR_of_stringMethodSpec $$ H
      · ipureintro; exact h
    · iright; iright
      isplitl
      · iapply stringMethodSpecR_of_stringMethodSpec $$ H
      · ipureintro; exact h

/-- **A `*T` whose `String()` needs `R`** (`R` lent and given back), where `T`'s pointer method set
`ms` (goose's `MethodSetIs`, an instance of the package's `TypeAssumptions`) has `String() string`
and no `Format`, `Error` or `CanInterface`: a `printArgOk R`. The method-set facts are decided by
`decide` (the lookups) and `simp [go.methodSetLookup, fmt.noArgStringSig]` (the signature). -/
theorem printArgOk_stringer {t : go.GoType} {ms : List (GoString × Option go.signature)}
    [go.MethodSetIs t ms] (v : val) (R : IProp GF)
    (hF : go.methodSetLookup ms go!"Format" = none)
    (hE : go.methodSetLookup ms go!"Error" = none)
    (hS : go.methodSetLookup ms go!"String" = some (some noArgStringSig))
    (hR : go.methodSetLookup ms go!"CanInterface" = none) :
    (□ ∀ Φ : val → IProp GF, R -∗ ▷ (∀ s : GoString, R -∗ Φ #s) -∗
        WP (App (Val #(methods t go!"String" v)) (Val #())) {{ Φ }}) ⊢
      printArgOk R (interface.ok (interface.mk t v)) := by
  have h1 := go.MethodSetIs.method_set_is (t := t) go!"Format"
  have h2 := go.MethodSetIs.method_set_is (t := t) go!"Error"
  have h3 := go.MethodSetIs.method_set_is (t := t) go!"String"
  have h4 := go.MethodSetIs.method_set_is (t := t) go!"CanInterface"
  rw [hF] at h1; rw [hE] at h2; rw [hS] at h3; rw [hR] at h4
  iintro #H
  unfold interface.mk printArgOk
  iright; iright
  isplitl
  · unfold stringMethodSpecR
    iexact H
  · ipureintro; exact ⟨h1, h2, h3, h4⟩

/-- **A `*bytes.Buffer`** at `l` holding the unread bytes `bs` is a `printArgOk` operand with
`R := bytes.ownBuffer l bs` (its `String()`, by `bytes.Buffer.String.spec`; Go's `%v` of it calls
`String()`, its pointer method set having no `Format`, `Error` or `CanInterface`). -/
theorem printArgOk_bytesBuffer [bytes.Assumptions]
    (wp_String : bytes.Buffer.String.spec (GF := GF) (hG := hG)) (l : Loc) (bs : List w8) :
    ⊢ printArgOk (GF := GF) (bytes.ownBuffer l bs)
        (interface.ok (interface.mk (go.GoType.PointerType bytes.Buffer.ty) #l)) := by
  iapply printArgOk_stringer (t := go.GoType.PointerType bytes.Buffer.ty) #l _
    (by simp [go.methodSetLookup]) (by simp [go.methodSetLookup])
    (by simp [go.methodSetLookup, noArgStringSig]) (by simp [go.methodSetLookup])
  imodintro
  iintro %Φ HR HΦ
  wp_apply wp_String l bs $$ HR as HR
  iapply HΦ $$ HR

/-- The helper `fmt.callError` with the method's spec needing `R`. -/
theorem wp_callErrorR (ii : GoInterfaceOk) (R : IProp GF) :
    {{ stringMethodSpecR (GF := GF) ii go!"Error" R ∗ R }}
      (App (Val (@! callError)) (Val #(interface.ok ii)))
    {{ RET #(); R }} := by
  wp_start as ⟨#HE, HR⟩
  try wp_auto
  wp_apply wp_with_defer_recover
  iintro %defer %pnc Hdefer Hpnc
  wp_auto
  iunfold stringMethodSpecR at HE
  wp_bind (App (Val #(methods ii.ty go!"Error" ii.v)) (Val #()))
  iapply HE $$ HR
  inext
  iintro %_ HR
  wp_auto
  wp_apply wp_recoverPanic $$ [$Hpnc] as Hpnc
  iapply HΦ
  iexact HR

/-- The helper `fmt.callString` with the method's spec needing `R`. -/
theorem wp_callStringR (ii : GoInterfaceOk) (R : IProp GF) :
    {{ stringMethodSpecR (GF := GF) ii go!"String" R ∗ R }}
      (App (Val (@! callString)) (Val #(interface.ok ii)))
    {{ RET #(); R }} := by
  wp_start as ⟨#HS, HR⟩
  try wp_auto
  wp_apply wp_with_defer_recover
  iintro %defer %pnc Hdefer Hpnc
  wp_auto
  iunfold stringMethodSpecR at HS
  wp_bind (App (Val #(methods ii.ty go!"String" ii.v)) (Val #()))
  iapply HS $$ HR
  inext
  iintro %_ HR
  wp_auto
  wp_apply wp_recoverPanic $$ [$Hpnc] as Hpnc
  iapply HΦ
  iexact HR

set_option maxHeartbeats 4000000 in
/-- The helper `fmt.visitArg` under `%v` (Go's `printArg(arg, 'v')`, as `Fprint` calls it): for a
`printArgOk R` operand, calls what Go calls of it (its `Error()` or `String()`, with `R`, or
nothing), and returns `R`. -/
theorem wp_visitArg_print (x : GoInterface) (R : IProp GF) :
    {{ printArgOk (GF := GF) R x ∗ R }}
      (App (App (App (App (Val (@! visitArg)) (Val #x)) (Val #(W8 118))) (Val #false)) (Val #false))
    {{ RET #(); R }} := by
  cases x with
  | nil =>
    iintro %Φ ⟨-, HR⟩ HΦ
    wp_apply (wp_visitArg_argOk (GF := GF) .nil (W8 118) false false (by simp)) $$ []
    · unfold argOkAt; itrivial
    iapply HΦ $$ HR
  | ok ii =>
    iintro %Φ ⟨Hx, HR⟩ HΦ
    unfold printArgOk
    icases Hx with (%Hwf | ⟨#HE, %hE⟩ | ⟨#HS, %hS⟩)
    · wp_apply (wp_visitArg_argOk (GF := GF) (.ok ii) (W8 118) false false (by simp)) $$ []
      · unfold argOkAt; ileft; ipureintro; exact Hwf
      iapply HΦ $$ HR
    · wp_func_call
      wp_call
      try wp_auto
      wp_apply wp_isBasic as %b %Hb
      obtain ⟨hF, hE⟩ := hE
      have hnB := ne_SliceType_of_method go.byte hE
      have hnS := ne_SliceType_of_method go.string hE
      cases b
      case true =>
        wp_auto
        iapply HΦ
        iexact HR
      wp_auto
      repeat' (first | (wp_apply (wp_callErrorR ii R) $$ [$HE $HR] as HR) | wp_if_destruct | wp_auto |
        simp only [tsc_method1, hF, hE,
        hnB, hnS, ↓reduceIte, noArgStringSig, reduceCtorEq, decide_false, _root_.decide_true])
      all_goals first
        | (iapply HΦ; iexact HR)
        | (exfalso; simp_all; done)
    · wp_func_call
      wp_call
      try wp_auto
      wp_apply wp_isBasic as %b %Hb
      obtain ⟨hF, hE, hS, hR⟩ := hS
      have hnB := ne_SliceType_of_method go.byte hS
      have hnS := ne_SliceType_of_method go.string hS
      cases b
      case true =>
        wp_auto
        iapply HΦ
        iexact HR
      wp_auto
      repeat' (first | (wp_apply (wp_callStringR ii R) $$ [$HS $HR] as HR) | wp_if_destruct | wp_auto |
        simp only [tsc_method1, hF, hE, hS,
        hR, hnB, hnS, ↓reduceIte, noArgStringSig, reduceCtorEq, decide_false, _root_.decide_true])
      all_goals first
        | (iapply HΦ; iexact HR)
        | (exfalso; simp_all; done)

end wps

end fmt

end Perennial
