/-
What the specs of `Sprintf`, `Printf` and `Errorf` need of their arguments (`argsOk`): under each
directive (`fmtDirectives`), an argument Go formats calling only methods whose specs are given
(an `Error()` or `String()` returning some string, needing nothing) and reading no memory; and
what `Errorf` returns (`errorfErr`).
-/
module

public import Perennial.Proof.fmt.Directives
public import Perennial.Golang.Theory
public import Perennial.Proof.errors.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace fmt

section defs
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- The signature `() string` of `Error` and `String`, as goose writes it in method sets. -/
def noArgStringSig : go.signature := go.signature.Signature [] false [go.string]

/-- A type of one of the kinds whose values Go's `%p` prints by their address (`fmtPointer`:
`Chan`, `Func`, `Map`, `Pointer`, `Slice`; `UnsafePointer`, a named type in the semantics, is left
out), without reading the memory they point to. -/
def IsRefKind : go.GoType → Prop
  | .PointerType _ => True
  | .FunctionType _ => True
  | .SliceType _ => True
  | .MapType _ _ => True
  | .ChannelType _ _ => True
  | _ => False

/-- `Errorf`'s `w.err, _ = a[k].(error)`: the argument as an `error`, `nil` if it is not one. -/
def asError (x : GoInterface) : GoInterface :=
  match x with
  | .nil => .nil
  | .ok ii => if go.typeSetContains ii.ty go.error then .ok ii else .nil

end defs

section iprops
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- Method `m` of the interface value `ii`, called with no arguments, returns some string,
needing nothing (persistently: `fmt` may call it any number of times). For `Error()` this is
what `errors.wp_New` and `fmt.wp_Errorf` give of the errors they return. -/
def stringMethodSpec (ii : GoInterfaceOk) (m : GoString) : IProp GF :=
  iprop(□ ∀ Φ : val → IProp GF, ▷ (∀ s : GoString, Φ #s) -∗
    WP (App (Val #(methods ii.ty m ii.v)) (Val #())) {{ Φ }})

theorem stringMethodSpec_unfold (ii : GoInterfaceOk) (m : GoString) :
    stringMethodSpec (GF := GF) ii m = iprop(□ ∀ Φ : val → IProp GF, ▷ (∀ s : GoString, Φ #s) -∗
      WP (App (Val #(methods ii.ty m ii.v)) (Val #())) {{ Φ }}) := rfl

instance stringMethodSpec_persistent (ii : GoInterfaceOk) (m : GoString) :
    Persistent (stringMethodSpec (GF := GF) ii m) := by
  unfold stringMethodSpec; infer_instance

/-- One argument that Go formats under a method verb (`v s x X q`, and `w` in `Errorf`), without
`#`, by calling its `Error()` or `String()`, which return some string needing nothing: a value
without a `Format` method whose `Error() string` has `stringMethodSpec`; or a value with neither a
`Format` nor an `Error` method whose `String() string` has it. Go's `handleMethods` calls `Format`
in place of either when the type has one (with Go's signature: none at all is asked here), and
`Error()` in place of `String()` for an `error`; it switches on `case error`/`case Stringer`, by
signature (`noArgStringSig`). In the `String()` case, no method `CanInterface`: not a
`reflect.Value`, which Go's `printArg` unwraps (`case reflect.Value:`, calling the methods of the
value it holds or printing that by reflection), and which the model tells by that method and is
stuck on. A panic of the method would be recovered by Go's `catchPanic`; the model does not recover
it, and the WP rules it out. `nil` and the predeclared basic types (`ArgWf`)
are admitted too. -/
def argOk : GoInterface → IProp GF
  | .nil => iprop(True)
  | .ok ii => iprop(⌜ArgWf ii⌝ ∨
      (stringMethodSpec ii go!"Error" ∗
        ⌜methodSet ii.ty !! go!"Format" = none ∧ methodSet ii.ty !! go!"Error" = some noArgStringSig⌝) ∨
      (stringMethodSpec ii go!"String" ∗
        ⌜methodSet ii.ty !! go!"Format" = none ∧ methodSet ii.ty !! go!"Error" = none ∧
          methodSet ii.ty !! go!"String" = some noArgStringSig ∧
          methodSet ii.ty !! go!"CanInterface" = none⌝))

/-- **One argument under the directive `d`**, the method verbs being `mv`, that Go formats calling
only methods `stringMethodSpec` covers and reading no memory the caller owns:
* `nil`, or `ArgWf` (a predeclared basic type, or a type of integer or string kind with none of the
  formatting methods: Go calls no method of it, under any directive);
* under a verb that is not a method verb, a value of integer kind with an `Error() string` or a
  `String() string` and no `Format` method (Go prints it as an integer by reflection, calling no
  method: `%d` of raft's `ConfChangeType`, which has `String()`);
* under `%T`, any value (Go prints its type's name);
* under `%p`, a value of a pointer, func, slice, map or chan type (`IsRefKind`; Go prints its
  address, `fmtPointer`, reading nothing);
* under a method verb other than `%#v`/`%#w`, and under `w` only for a type with `Error() string`
  (`Errorf`'s `%w` of a value that is no `error` is a bad verb, and `fmt` reflects into it),
  `argOk`. -/
def argOkAt (mv : List w8) (d : Directive) : GoInterface → IProp GF
  | .nil => iprop(True)
  | .ok ii => iprop(⌜ArgWf ii⌝ ∨
      ⌜d.verb ∉ mv ∧ IsIntType (underlying ii.ty) ∧ methodSet ii.ty !! go!"Format" = none ∧
        (methodSet ii.ty !! go!"Error" = some noArgStringSig ∨
          methodSet ii.ty !! go!"String" = some noArgStringSig)⌝ ∨
      (⌜d.verb ∈ mv ∧ d.sharpV = false ∧
        (d.verb = W8 119 → methodSet ii.ty !! go!"Error" = some noArgStringSig)⌝ ∗
        argOk (.ok ii)) ∨
      ⌜d.verb = W8 84⌝ ∨
      ⌜d.verb = W8 112 ∧ IsRefKind (underlying ii.ty)⌝)

instance argOk_persistent (x : GoInterface) : Persistent (argOk (GF := GF) x) := by
  cases x <;> unfold argOk <;> infer_instance

instance argOkAt_persistent (mv : List w8) (d : Directive) (x : GoInterface) :
    Persistent (argOkAt (GF := GF) mv d x) := by
  cases x <;> unfold argOkAt <;> infer_instance

/-- The arguments under the directives: one each, in order; those left over are printed under
`%v` (`EXTRA`). -/
def argsOkAt (mv : List w8) : List Directive → List GoInterface → IProp GF
  | _, [] => iprop(True)
  | d :: ds, a :: xs => iprop(argOkAt mv d a ∗ argsOkAt mv ds xs)
  | [], a :: xs => iprop(argOkAt mv ⟨W8 118, false⟩ a ∗ argsOkAt mv [] xs)

instance argsOkAt_persistent (mv : List w8) (ds : List Directive) (xs : List GoInterface) :
    Persistent (argsOkAt (GF := GF) mv ds xs) := by
  induction xs generalizing ds with
  | nil => cases ds <;> unfold argsOkAt <;> infer_instance
  | cons x xs ih => cases ds <;> unfold argsOkAt <;> infer_instance

/-- **The arguments `xs` of the format `format`**, the method verbs being `mv`: every argument is
`nil` or `ArgWf` (Go calls no method of them, whatever the format: then the format may have
directives `fmtDirectives` refuses), or the format's directives parse (`fmtDirectives`) and each
argument is `argOkAt` its directive. -/
def argsOk (mv : List w8) (format : GoString) (xs : List GoInterface) : IProp GF :=
  iprop(⌜ArgsWf xs⌝ ∨
    ∃ ds : List Directive, ⌜fmtDirectives format = some ds⌝ ∗ argsOkAt mv ds xs)

/-- `argsOk` from the format's directives. -/
theorem argsOk_intro {mv : List w8} {format : GoString} {ds : List Directive}
    {xs : List GoInterface} (h : fmtDirectives format = some ds) :
    argsOkAt (GF := GF) mv ds xs ⊢ argsOk mv format xs := by
  unfold argsOk
  iintro H
  iright
  iexists ds
  isplitr
  · ipureintro; exact h
  · iexact H

/-- `argsOk` of arguments that are all `nil` or `ArgWf`. -/
theorem argsOk_of_argsWf {mv : List w8} {format : GoString} {xs : List GoInterface}
    (h : ArgsWf xs) : ⊢ argsOk (GF := GF) mv format xs := by
  unfold argsOk
  ileft
  ipureintro
  exact h

/-- **What `Errorf(format, xs...)` returns, of message `s`** (the formatted string): a pointer error
of a type with `Error() string` and no `Format` method, one of `*errors.errorString`,
`*fmt.wrapError`, `*fmt.wrapErrors`, whose `Error()` returns `s`; and, when the
format's directives parse (`fmtDirectives`), by its `%w` directives' arguments (`wrapArgs`, Go's
`wrappedErrs`): with none, an `*errors.errorString` holding `s` (`errors.New(s)`); with one, a
`*fmt.wrapError` holding `s` and the argument as an `error` (`asError`: `nil` if it is not one),
which its `Unwrap` returns; with several, a `*fmt.wrapErrors` holding `s`. -/
def errorfErr (format : GoString) (xs : List GoInterface) (s : GoString) (err : GoInterfaceOk) :
    IProp GF :=
  iprop(⌜errors.IsPointerError err ∧ methodSet err.ty !! go!"Format" = none ∧
      methodSet err.ty !! go!"Error" = some noArgStringSig ∧
      (err.ty = go.GoType.PointerType errors.errorString.ty ∨
        err.ty = go.GoType.PointerType wrapError.ty ∨ err.ty = go.GoType.PointerType wrapErrors.ty)⌝ ∗
    (□ ∀ Φ : val → IProp GF, ▷ Φ #s -∗
      WP (App (Val #(methods err.ty go!"Error" err.v)) (Val #())) {{ Φ }}) ∗
    match fmtDirectives format with
    | none => iprop(True)
    | some ds =>
      match wrapArgs ds xs.length with
      | [] => iprop(∃ l : Loc,
          ⌜err = interface.mk (go.GoType.PointerType errors.errorString.ty) #l⌝ ∗
          l.[errors.errorString, go!"s"] ↦□ s)
      | [j] => iprop(∃ l : Loc,
          ⌜err = interface.mk (go.GoType.PointerType wrapError.ty) #l⌝ ∗
          l.[wrapError, go!"msg"] ↦□ s ∗ l.[wrapError, go!"err"] ↦□ asError (xs[j]?.getD .nil))
      | _ :: _ :: _ => iprop(∃ l : Loc,
          ⌜err = interface.mk (go.GoType.PointerType wrapErrors.ty) #l⌝ ∗
          l.[wrapErrors, go!"msg"] ↦□ s))

end iprops

end fmt

end Perennial
