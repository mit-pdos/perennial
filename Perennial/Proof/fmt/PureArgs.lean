/-
`fmt.Sprintf` of arguments that call no method (`nil`, a `bool`, a value of a predeclared integer
type, a `string`): the spec of the real `Sprintf` (`fmt.Sprintf.spec`) with the arguments given as
a pure list (`fmt.PureArgs`), and the output computed (`fmt.render`) when the format has no `%q`
(`fmt.NoQuote`); and the tactics that discharge the side conditions on a literal format and
literal arguments (`fmt_encode`, `fmt_fits`, `fmt_pure`, `fmt_noquote`).
-/
module

public import Perennial.Spec.fmt.Sprintf
public import Perennial.Proof.fmt.OutLemmas

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace fmt

section defs
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- The Go values `xs` are the arguments `args`, none of which calls a method: `nil`, a `bool`, a
value of a predeclared integer type (`IntArg`) or a `string`. -/
inductive PureArgs : List GoInterface → List Arg → Prop
  | nil : PureArgs [] []
  | nil_ (xs : List GoInterface) (args : List Arg) :
      PureArgs xs args → PureArgs (interface.nil :: xs) (.nil :: args)
  | bool (b : Bool) (xs : List GoInterface) (args : List Arg) :
      PureArgs xs args → PureArgs (interface.mkOk go.bool #b :: xs) (.bool b :: args)
  | int (x : GoInterface) (z : Int) (xs : List GoInterface) (args : List Arg) :
      IntArg x z → PureArgs xs args → PureArgs (x :: xs) (.int z :: args)
  | str (s : GoString) (xs : List GoInterface) (args : List Arg) :
      PureArgs xs args → PureArgs (interface.mkOk go.string #s :: xs) (.str s :: args)

theorem PureArgs.noMethod {xs : List GoInterface} {args : List Arg} (h : PureArgs xs args) :
    ∀ a ∈ args, a.NoMethod := by
  induction h with
  | nil => simp
  | nil_ _ _ _ ih | bool _ _ _ _ ih | int _ _ _ _ _ _ ih | str _ _ _ _ ih =>
    simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨trivial, ih⟩

theorem PureArgs.length_eq {xs : List GoInterface} {args : List Arg} (h : PureArgs xs args) :
    xs.length = args.length := by
  induction h <;> simp_all

end defs

/-- `%.2X` of an integer `z`: `precPad 16 true 2 z` (`render`). -/
@[simp] theorem precOutFn_int (p : Nat) (v : w8) (z : Int) :
    precOutFn p v (.int z) = precPad (verbBase v) (decide (v = verb_X)) p z := rfl

end fmt

/-- `ps` encodes a literal format: `format = fmt.encode ps`. -/
macro "fmt_encode" : tactic => `(tactic| (simp [_root_.Perennial.fmt.encode,
  _root_.Perennial.fmt.Piece.encode, _root_.Perennial.fmt.decimalNat_eq,
  _root_.Perennial.fmt.digitByte, _root_.Perennial.fmt.verb_d, _root_.Perennial.fmt.verb_s,
  _root_.Perennial.fmt.verb_v, _root_.Perennial.fmt.verb_x, _root_.Perennial.fmt.verb_q,
  _root_.Perennial.fmt.verb_t, _root_.Perennial.fmt.verb_X]))

/-- `fmt.Fits ps args` for literal pieces and arguments (`%q` of a string `s` needs
`s.length ≤ maxAddr` in the context). -/
macro "fmt_fits" : tactic => `(tactic| (repeat' (first
  | exact _root_.Perennial.fmt.Fits.nil
  | refine _root_.Perennial.fmt.Fits.lit _ _ _ (by decide) ?_
  | refine _root_.Perennial.fmt.Fits.percent _ _ ?_
  | refine _root_.Perennial.fmt.Fits.dir _ _ _ _ _ (by simp [_root_.Perennial.fmt.DirOk,
      _root_.Perennial.fmt.ZeroWidthOk, _root_.Perennial.fmt.verb_d, _root_.Perennial.fmt.verb_s,
      _root_.Perennial.fmt.verb_v, _root_.Perennial.fmt.verb_x, _root_.Perennial.fmt.verb_q,
      _root_.Perennial.fmt.verb_t] <;> assumption) ?_
  | refine _root_.Perennial.fmt.Fits.prec _ _ _ _ _ (by simp [_root_.Perennial.fmt.PrecOk,
      _root_.Perennial.fmt.verb_d, _root_.Perennial.fmt.verb_v, _root_.Perennial.fmt.verb_x,
      _root_.Perennial.fmt.verb_X]) ?_)))

/-- `fmt.PureArgs xs ?args` for a literal list `xs` of `nil`s, `bool`s, `string`s and values of
predeclared integer types: the arguments read off the values. -/
macro "fmt_pure" : tactic => `(tactic| (repeat' (first
  | exact _root_.Perennial.fmt.PureArgs.nil
  | refine _root_.Perennial.fmt.PureArgs.str _ _ _ ?_
  | refine _root_.Perennial.fmt.PureArgs.bool _ _ _ ?_
  | refine _root_.Perennial.fmt.PureArgs.nil_ _ _ ?_
  | refine _root_.Perennial.fmt.PureArgs.int _ _ _ _ (by constructor) ?_)))

/-- `fmt.NoQuote ps` for literal pieces. -/
macro "fmt_noquote" : tactic => `(tactic| (intro _ h; simp [_root_.Perennial.fmt.verb_d,
  _root_.Perennial.fmt.verb_s, _root_.Perennial.fmt.verb_v, _root_.Perennial.fmt.verb_x,
  _root_.Perennial.fmt.verb_q, _root_.Perennial.fmt.verb_t, _root_.Perennial.fmt.verb_X] at h))

namespace fmt

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

theorem PureArgs.isArgs {xs : List GoInterface} {args : List Arg} (h : PureArgs xs args) :
    ⊢ ([∗list] x;a ∈ xs;args, isArg (GF := GF) x a) := by
  induction h with
  | nil => exact BigSepL2.bigSepL2_nil.2
  | nil_ _ _ _ ih =>
    iapply BigSepL2.bigSepL2_cons.2
    isplitr
    · simp only [isArg]; ipureintro; trivial
    · iapply ih
  | bool _ _ _ _ ih =>
    iapply BigSepL2.bigSepL2_cons.2
    isplitr
    · simp only [isArg]; ipureintro; trivial
    · iapply ih
  | int _ _ _ _ hx _ ih =>
    iapply BigSepL2.bigSepL2_cons.2
    isplitr
    · simp only [isArg]; ipureintro; exact hx
    · iapply ih
  | str _ _ _ _ ih =>
    iapply BigSepL2.bigSepL2_cons.2
    isplitr
    · simp only [isArg]; ipureintro; trivial
    · iapply ih

/-- **`fmt.Sprintf(format, args...)` of arguments that call no method** (`PureArgs`), the format
`encode ps` in the verified subset (`Fits`): returns some string `s` with `Out ps args s`, which is
`render ps args` when the format has no `%q` (`NoQuote`, `Out.eq_render`), and gives the arguments'
slice back. -/
theorem Sprintf_pure_of (wp_Sprintf : fmt.Sprintf.spec (GF := GF) (hG := hG)) :
    ∀ (format : GoString) (ps : List Piece) (args_sl : GoSlice) (xs : List GoInterface)
      (args : List Arg) (dq : DFrac),
    format = encode ps → Fits ps args → PureArgs xs args →
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args_sl ↦*{dq} xs }}
      (App (App (Val (@! fmt.Sprintf)) (Val #format)) (Val #args_sl))
    {{ (s : GoString), RET #s; args_sl ↦*{dq} xs ∗
        ⌜Out ps args s ∧ (NoQuote ps → s = render ps args)⌝ }} := by
  intro format ps args_sl xs args dq he hf hp
  iintro %Φ ⟨#Hpkg, Hsl⟩ HΦ
  iapply (wp_Sprintf format ps args_sl xs args dq he hf) $$ [Hsl]
  · iframe
    isplitr
    · iexact Hpkg
    iapply hp.isArgs
  inext
  iintro %s ⟨Hsl, -, %Hout⟩
  iapply HΦ
  iframe
  ipureintro
  exact ⟨Hout, Hout.eq_render hp.noMethod⟩

end wps

end fmt

end Perennial
