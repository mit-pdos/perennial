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

/-- The method `Write` of the interface value `ii` (an `io.Writer`), called once, with `P` and a
slice of the bytes `bs` that it owns entirely: it returns `(n, err)` with `Q bs n err` and gives
the slice back, as `io.Writer`'s contract asks ("Write must not modify the slice data, even
temporarily. Implementations must not retain p."). What `fmt.Fprintf` needs of its writer. -/
def writeSpec (ii : GoInterfaceOk) (P : IProp GF) (Q : GoString → w64 → GoInterface → IProp GF) :
    IProp GF :=
  iprop(∀ (sl : GoSlice) (bs : GoString) (Φ : val → IProp GF),
    P -∗ sl ↦* bs -∗
    ▷ (∀ (n : w64) (err : GoInterface), sl ↦* bs -∗ Q bs n err -∗ Φ (PairV #n #err)) -∗
    WP (App (Val #(methods ii.ty go!"Write" ii.v)) (Val #sl)) {{ Φ }})

/-- One argument that Go formats under a method verb (`v s x X q`, and `w` in `Errorf`), without
`#`, by calling its `Error()` or `String()`, which return some string needing nothing: a value
without a `Format` method whose `Error() string` has `stringMethodSpec`; or a value with neither a
`Format` nor an `Error` method whose `String() string` has it. Go's `handleMethods` calls `Format`
in place of either when the type has one (with Go's signature: none at all is asked here), and
`Error()` in place of `String()` for an `error`; it switches on `case error`/`case Stringer`, by
signature (`noArgStringSig`). In the `String()` case, no method `CanInterface`: not a
`reflect.Value`, which Go's `printArg` unwraps (`case reflect.Value:`, calling the methods of the
value it holds or printing that by reflection), and which the model tells by that method and is
stuck on. A panic of the method would be recovered by Go's `catchPanic`; the model is stuck there
(`callError`, `callString`), and the WP rules it out. `nil` and the predeclared basic types (`ArgWf`)
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

/-! ### `[]byte` arguments

The bytes of `[]byte` arguments are memory Go reads while formatting, so they are not part of the
persistent `argOkAt`: a caller lends them separately, as a list of resources over the arguments
(`bytesOwn`), naming their contents with `B` (`B x = some bs`), and gets them back. `argsOkB B`
admits a lent `[]byte` argument under any directive; with `B` always `none` it is `argsOk`. -/

/-- The bytes `bs` of the argument `x` lent for formatting, when `B x = some bs`: `x` holds a
`[]byte` whose elements are `bs`, at fraction `dq`; nothing when `B x = none`. -/
def bytesArgOwn (dq : DFrac) (B : GoInterface → Option GoString) (x : GoInterface) : IProp GF :=
  match B x with
  | none => iprop(emp)
  | some bs => iprop(∃ (ii : GoInterfaceOk) (sl : GoSlice),
      ⌜x = interface.ok ii ∧ ii.ty = go.SliceType go.byte ∧ ii.v = #sl⌝ ∗ sl ↦*{dq} bs)

/-- `bytesArgOwn` of a lent argument: a `[]byte` holding the lent bytes. -/
theorem bytesArgOwn_some {dq : DFrac} {B : GoInterface → Option GoString} {x : GoInterface}
    {bs : GoString} (h : B x = some bs) :
    bytesArgOwn (GF := GF) dq B x ⊣⊢ ∃ (ii : GoInterfaceOk) (sl : GoSlice),
      ⌜x = interface.ok ii ∧ ii.ty = go.SliceType go.byte ∧ ii.v = #sl⌝ ∗ sl ↦*{dq} bs := by
  unfold bytesArgOwn; rw [h]; exact .rfl

/-- The bytes of every argument `x` with `B x = some _`, lent for formatting (`bytesArgOwn`). -/
def bytesOwn (dq : DFrac) (B : GoInterface → Option GoString) (xs : List GoInterface) : IProp GF :=
  iprop([∗list] x ∈ xs, bytesArgOwn dq B x)

/-- `argOkAt`, or a `[]byte` whose bytes are lent (`B x ≠ none`, under any directive: Go calls no
method of a `[]byte`). -/
def argOkAtB (B : GoInterface → Option GoString) (mv : List w8) (d : Directive) (x : GoInterface) :
    IProp GF :=
  iprop(argOkAt mv d x ∨ ⌜(B x).isSome⌝)

/-- `argsOkAt` with `argOkAtB`. -/
def argsOkAtB (B : GoInterface → Option GoString) (mv : List w8) :
    List Directive → List GoInterface → IProp GF
  | _, [] => iprop(True)
  | d :: ds, a :: xs => iprop(argOkAtB B mv d a ∗ argsOkAtB B mv ds xs)
  | [], a :: xs => iprop(argOkAtB B mv ⟨W8 118, false⟩ a ∗ argsOkAtB B mv [] xs)

/-- `argsOk` with `argOkAtB`: the arguments of `format` when the bytes named by `B` are lent. -/
def argsOkB (B : GoInterface → Option GoString) (mv : List w8) (format : GoString)
    (xs : List GoInterface) : IProp GF :=
  iprop(⌜ArgsWf xs⌝ ∨ ∃ ds : List Directive, ⌜fmtDirectives format = some ds⌝ ∗ argsOkAtB B mv ds xs)

instance argOkAtB_persistent (B : GoInterface → Option GoString) (mv : List w8) (d : Directive)
    (x : GoInterface) : Persistent (argOkAtB (GF := GF) B mv d x) := by
  unfold argOkAtB; infer_instance

instance argsOkAtB_persistent (B : GoInterface → Option GoString) (mv : List w8)
    (ds : List Directive) (xs : List GoInterface) : Persistent (argsOkAtB (GF := GF) B mv ds xs) := by
  induction xs generalizing ds with
  | nil => cases ds <;> unfold argsOkAtB <;> infer_instance
  | cons x xs ih => cases ds <;> unfold argsOkAtB <;> infer_instance

instance argsOkB_persistent (B : GoInterface → Option GoString) (mv : List w8) (format : GoString)
    (xs : List GoInterface) : Persistent (argsOkB (GF := GF) B mv format xs) := by
  unfold argsOkB; infer_instance

theorem argsOkAtB_of_argsOkAt (B : GoInterface → Option GoString) (mv : List w8)
    (ds : List Directive) (xs : List GoInterface) :
    argsOkAt (GF := GF) mv ds xs ⊢ argsOkAtB B mv ds xs := by
  induction xs generalizing ds with
  | nil => cases ds <;> (unfold argsOkAtB; iintro -; itrivial)
  | cons x xs ih =>
    cases ds with
    | nil =>
      unfold argsOkAt argsOkAtB argOkAtB
      iintro ⟨H, Hs⟩
      isplitl [H]
      · ileft; iexact H
      · iapply ih; iexact Hs
    | cons d ds =>
      unfold argsOkAt argsOkAtB argOkAtB
      iintro ⟨H, Hs⟩
      isplitl [H]
      · ileft; iexact H
      · iapply ih; iexact Hs

/-- `argsOk` admits what `argsOkB` does, whatever bytes are lent. -/
theorem argsOkB_of_argsOk (B : GoInterface → Option GoString) (mv : List w8) (format : GoString)
    (xs : List GoInterface) : argsOk (GF := GF) mv format xs ⊢ argsOkB B mv format xs := by
  unfold argsOk argsOkB
  iintro (%Hwf | ⟨%ds, %Hds, Hds⟩)
  · ileft; ipureintro; exact Hwf
  · iright; iexists ds
    isplitr
    · ipureintro; exact Hds
    · iapply argsOkAtB_of_argsOkAt; iexact Hds

/-- With no bytes lent, `bytesOwn` holds trivially. -/
theorem bytesOwn_none (dq : DFrac) (xs : List GoInterface) :
    ⊢ bytesOwn (GF := GF) dq (fun _ => none) xs := by
  unfold bytesOwn
  induction xs with
  | nil => iapply BigSepL.bigSepL_nil.2; iempintro
  | cons x xs ih =>
    iapply BigSepL.bigSepL_cons.2
    isplitl []
    · unfold bytesArgOwn; iempintro
    · iapply ih

/-- The bytes of the argument at index `k`, out of `bytesOwn`, to be put back. -/
theorem bytesOwn_lookup_acc {dq : DFrac} {B : GoInterface → Option GoString}
    {xs : List GoInterface} {k : Nat} {x : GoInterface} (h : xs[k]? = some x) :
    bytesOwn (GF := GF) dq B xs ⊢ bytesArgOwn dq B x ∗ (bytesArgOwn dq B x -∗ bytesOwn dq B xs) := by
  unfold bytesOwn
  iintro H
  icases (BigSepL.bigSepL_lookup_acc (Φ := fun _ y => bytesArgOwn (GF := GF) dq B y) h).1 $$ H
    with ⟨Hx, Hclose⟩
  iframe Hx
  iintro Hx
  have hset : xs.set k x = xs := by
    apply List.ext_getElem?
    intro j
    rw [List.getElem?_set]
    by_cases hj : k = j
    · subst hj
      obtain ⟨hk, hx⟩ := List.getElem?_eq_some_iff.mp h
      simp [hk, hx]
    · simp [hj]
  ihave H2 := Hclose $$ %x Hx
  rw [hset]
  iexact H2

/-- A lent argument is a `[]byte` (`bytesArgOwn`), as a pure fact, keeping the bytes. -/
theorem bytesOwn_ty (dq : DFrac) (B : GoInterface → Option GoString) (xs : List GoInterface) :
    bytesOwn (GF := GF) dq B xs ⊢ bytesOwn dq B xs ∗
      ⌜∀ x ∈ xs, (B x).isSome → ∃ ii, x = interface.ok ii ∧ ii.ty = go.SliceType go.byte⌝ := by
  unfold bytesOwn
  induction xs with
  | nil => iintro H; iframe; ipureintro; intro x hx; cases hx
  | cons x xs ih =>
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨Hx, Hxs⟩
    icases ih $$ Hxs with ⟨Hxs, %hxs⟩
    cases hB : B x with
    | none =>
      isplitl [Hx Hxs]
      · iapply BigSepL.bigSepL_cons.2; iframe
      ipureintro
      intro y hy hs
      rcases List.mem_cons.mp hy with rfl | hy
      · rw [hB] at hs; cases hs
      · exact hxs y hy hs
    | some bs =>
      icases (bytesArgOwn_some (dq := dq) hB).1 $$ Hx with ⟨%ii, %sl, %Hp, Hsl⟩
      obtain ⟨hx, hty, hv⟩ := Hp
      isplitl [Hsl Hxs]
      · iapply BigSepL.bigSepL_cons.2
        iframe
        iapply (bytesArgOwn_some (dq := dq) hB).2
        iexists ii, sl
        iframe
        ipureintro; exact ⟨hx, hty, hv⟩
      ipureintro
      intro y hy hs
      rcases List.mem_cons.mp hy with rfl | hy
      · exact ⟨ii, hx, hty⟩
      · exact hxs y hy hs

/-- With no bytes lent, `argsOkB` is `argsOk`. -/
theorem argsOk_of_argsOkB_none (mv : List w8) (format : GoString) (xs : List GoInterface) :
    argsOkB (GF := GF) (fun _ => none) mv format xs ⊢ argsOk mv format xs := by
  have hat : ∀ ds xs, argsOkAtB (GF := GF) (fun _ => none) mv ds xs ⊢ argsOkAt mv ds xs := by
    intro ds xs
    induction xs generalizing ds with
    | nil => cases ds <;> (unfold argsOkAt; iintro -; itrivial)
    | cons x xs ih =>
      cases ds <;>
        (unfold argsOkAtB argsOkAt argOkAtB
         iintro ⟨(H | %H), Hs⟩
         · isplitl [H]
           · iexact H
           · iapply ih; iexact Hs
         · simp at H)
  unfold argsOkB argsOk
  iintro (%Hwf | ⟨%ds, %Hds, Hds⟩)
  · ileft; ipureintro; exact Hwf
  · iright; iexists ds
    isplitr
    · ipureintro; exact Hds
    · iapply hat; iexact Hds

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
