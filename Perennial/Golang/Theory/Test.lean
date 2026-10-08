/-
Small worked examples of the GooseLang proof tactics (`wp_start`, `wp_auto`,
`wp_apply`, `wp_pures`, `wp_bind`, `wp_load`/`wp_store`/`wp_alloc`, `wp_for`,
`iNamed`) on hand-written GooseLang functions in the style of goose's output.
These double as regression tests and as examples for proof writers.
-/
module

public import Perennial.Golang.Theory

@[expose] public section

namespace Perennial
open Iris Iris.BI

section code
variable [FfiSyntax] [GoGlobalContext]

/-- `func addOne(x uint64) uint64 { return x + 1 }` -/
def addOne : val :=
  LamV "x" (App (Val exceptionDo)
    (Let "x" (App (Val (GoInstruction (GoAlloc go.uint64))) (Var "x"))
    (App (Val doReturn)
      (App (Val (GoInstruction (GoOp GoPlus go.uint64)))
        (Pair (App (Val (GoInstruction (GoLoad go.uint64))) (Var "x")) (Val #(W64 1)))))))

/-- `func callAddOne(y uint64) uint64 { return addOne(y) }` -/
def callAddOne : val :=
  LamV "y" (App (Val exceptionDo)
    (Let "y" (App (Val (GoInstruction (GoAlloc go.uint64))) (Var "y"))
    (App (Val doReturn)
      (Let "$a0" (App (Val (GoInstruction (GoLoad go.uint64))) (Var "y"))
      (App (Val addOne) (Var "$a0"))))))

/-- `func countTo(n uint64) uint64 { var i uint64; for i < n { i = i + 1 }; return i }` -/
def countTo : val :=
  LamV "n" (App (Val exceptionDo)
    (Let "n" (App (Val (GoInstruction (GoAlloc go.uint64))) (Var "n"))
    (Let "i" (App (Val (GoInstruction (GoAlloc go.uint64)))
      (App (Val (GoInstruction (GoZeroVal go.uint64))) (Val #())))
    (App (App (Val exceptionSeq) (Lam BAnon
      (App (Val doReturn) (App (Val (GoInstruction (GoLoad go.uint64))) (Var "i")))))
    (App (App (App (Val doFor)
      (Lam BAnon (App (Val (GoInstruction (GoOp GoLt go.uint64)))
        (Pair (App (Val (GoInstruction (GoLoad go.uint64))) (Var "i"))
              (App (Val (GoInstruction (GoLoad go.uint64))) (Var "n"))))))
      (Lam BAnon (App (Val doExecute)
        (App (Val (GoInstruction (GoStore go.uint64))) (Pair (Var "i")
          (App (Val (GoInstruction (GoOp GoPlus go.uint64)))
            (Pair (App (Val (GoInstruction (GoLoad go.uint64))) (Var "i")) (Val #(W64 1)))))))))
      (Lam BAnon (Val #())))))))

end code

section proofs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [go.PreSemantics]

/-- A pure computation: `wp_pures` steps through `let:` and `if:`. -/
example (Φ : val → IProp GF) (v w : val) :
    Φ v ⊢ WP gl(let: "x" := v in let: "y" := w in if: #true then "x" else "y") {{ Φ }} := by
  iintro H
  wp_pures
  iexact H

/-- Typed memory: allocation, load and store. -/
example : ⊢ WP gl(let: "x" := GoAlloc go.uint64 #(W64 3) in
     "x" <-[go.uint64] (![go.uint64] "x" +⟨go.uint64⟩ #(W64 1)) ;;
     ![go.uint64] "x") {{ v, (⌜v = #(W64 3 + W64 1)⌝ : IProp GF) }} := by
  wp_auto
  ipureintro; rfl

/-- The same with the individual tactics. -/
example : ⊢ WP gl(let: "x" := GoAlloc go.uint64 #(W64 3) in
     "x" <-[go.uint64] (![go.uint64] "x" +⟨go.uint64⟩ #(W64 1)) ;;
     ![go.uint64] "x") {{ v, (⌜v = #(W64 3 + W64 1)⌝ : IProp GF) }} := by
  wp_pures
  wp_alloc l as Hl
  wp_pures
  wp_load
  wp_pures
  wp_store
  wp_pures
  wp_load
  ipureintro; rfl

theorem wp_addOne (x : w64) :
    {{ (True : IProp GF) }} (App (Val addOne) (Val #x)) {{ RET #(x + W64 1); True }} := by
  wp_start
  wp_auto
  iapply HΦ
  itrivial

theorem wp_callAddOne (y : w64) :
    {{ (True : IProp GF) }} (App (Val callAddOne) (Val #y)) {{ RET #(y + W64 1); True }} := by
  wp_start
  wp_auto
  wp_apply wp_addOne
  iapply HΦ
  itrivial

/-- `wp_apply ... as pats` introduces the return binders and postcondition. -/
example (Φ : val → IProp GF) :
    (∀ x : w64, Φ #x) ⊢ WP gl(let: "x" := ArbitraryInt in let: "y" := "x" in "y") {{ Φ }} := by
  iintro H
  wp_apply wp_ArbitraryInt as %x _
  iapply H

/-- `wp_bind` with a pattern, and `wp_apply_core` (no automation). -/
example (Φ : val → IProp GF) :
    (∀ x : w64, Φ #x) ⊢ WP gl(let: "x" := ArbitraryInt in "x") {{ Φ }} := by
  iintro H
  wp_bind ArbitraryInt
  wp_apply_core wp_ArbitraryInt
  iintro %x _
  wp_pures
  iapply H

theorem wp_countTo (n : w64) :
    {{ (True : IProp GF) }} (App (Val countTo) (Val #n)) {{ RET #n; True }} := by
  wp_start
  wp_auto
  -- the loop invariant
  ihave HI : (∃ i : w64, "i" ∷ i_ptr ↦ i ∗ "%Hi" ∷ ⌜uint.Z i ≤ uint.Z n⌝ : IProp GF) $$ [i]
  · iexists _; iframe i; ipureintro; simp [zero_val, ZeroVal.zeroValDef, uint.Z]
  wp_for HI
  wp_if_destruct
  · -- loop body: prove the invariant again
    wp_for_post
    iframe
    iexists _
    iframe
    ipureintro; word
  · -- loop exit
    have heq : i = n := by word
    subst heq
    iapply HΦ
    itrivial

/-! ### Regression tests for the tactic fixes -/

/-- `wp_apply ... $$ [..] as pats`: the `as` is not swallowed by the spec pattern. -/
example (l : Loc) (v : w64) (Φ : val → IProp GF) :
    (l ↦ v) ∗ (l ↦ v -∗ Φ #v) ⊢ WP gl(![go.uint64] #l) {{ Φ }} := by
  iintro ⟨Hl, H⟩
  wp_apply IntoValTyped.wp_load (t := go.uint64) l (DFrac.own 1) v $$ [$Hl] as Hl
  iapply H $$ Hl

/-- An ill-typed lemma given to `wp_apply` is an error (not a silent `sorry`). -/
example (Φ : val → IProp GF) :
    (∀ x : w64, Φ #x) ⊢ WP gl(let: "x" := ArbitraryInt in "x") {{ Φ }} := by
  iintro H
  fail_if_success wp_apply wp_ArbitraryInt 1 2 3 as %x _
  wp_apply wp_ArbitraryInt as %x _
  iapply H

/-- `wp_if_destruct` splits on the condition of the head `if:`, not on a
`decide` in the postcondition. -/
example (b : Bool) (P : Prop) [Decidable P] (Φ : val → IProp GF) :
    Φ #() ⊢ WP gl(if: #(decide P) then #() else #())
      {{ v, ⌜decide (b = true) = decide (b = true)⌝ -∗ Φ v }} := by
  iintro H
  wp_if_destruct
  · iintro _; iexact H
  · iintro _; iexact H

/-- `len` leaves the Iris goal alone. -/
example (l : List Nat) (_h : (l ++ [1]).length = 3) (Φ : val → IProp GF) : Φ #() ⊢ Φ #() := by
  len
  iintro H; iexact H

set_option goose.wp.extras true in
/-- With `goose.wp.extras`, `wp_auto` stores function literals (`RecV`) as `#(func.mk ..)`. -/
example (l : Loc) (f : GoFunc) (Φ : val → IProp GF) :
    (l ↦ f) ∗ (l ↦ func.mk BAnon BAnon (Val #()) -∗ Φ #()) ⊢
      WP (App (Val (GoInstruction (GoStore (go.FunctionType (go.Signature [] false [])))))
        (Pair (Val #l) (Rec BAnon BAnon (Val #())))) {{ Φ }} := by
  iintro ⟨Hl, H⟩
  wp_auto
  iapply H $$ Hl

/-! ### Regression tests (tactic backlog, round 2) -/

/-- `wp_apply +noauto ... as pats` introduces `pats` and stops right after the call. -/
example (Φ : val → IProp GF) :
    (∀ x : w64, Φ #x) ⊢ WP gl(let: "x" := ArbitraryInt in let: "y" := "x" in "y") {{ Φ }} := by
  iintro H
  wp_apply +noauto wp_ArbitraryInt as %x _
  -- the `let:`s have not been stepped
  wp_pure; wp_pure
  wp_pures
  iapply H

/-- `wp_apply (lc := n)` produces credits, and fails when there are too few steps. -/
example (Φ : val → IProp GF) :
    (∀ x : w64, £ 1 -∗ Φ #x) ⊢ WP gl(let: "x" := ArbitraryInt in let: "y" := "x" in "y") {{ Φ }} := by
  iintro H
  fail_if_success wp_apply (lc := 5) wp_ArbitraryInt as %x _
  wp_apply (lc := 1) wp_ArbitraryInt as %x _
  iapply H $$ Hlc1

/-- `+noauto` with a spec pattern and `as`. -/
example (l : Loc) (v : w64) (Φ : val → IProp GF) :
    (l ↦ v) ∗ (l ↦ v -∗ Φ #v) ⊢ WP gl(let: "x" := ![go.uint64] #l in "x") {{ Φ }} := by
  iintro ⟨Hl, H⟩
  wp_apply +noauto (IntoValTyped.wp_load (t := go.uint64) l (DFrac.own 1) v) $$ [$Hl] as Hl
  wp_pures
  iapply H $$ Hl

/-- `iNamed` on `∃ s, ... ∗ match s with ...` (used to fail with "unknown free
variable"); the unnamed rest does not shadow a conjunct with the same name. -/
example (P Q : IProp GF) :
    (∃ s : Option Nat, "H" ∷ P ∗ match s with | some _ => Q | none => P) ⊢ P := by
  iintro H
  iNamed H
  iexact H

/-- `iNamed` destructs a hypothesis under a later (e.g. an invariant just opened
with `iinv`); it used to do nothing. -/
example (P : Nat → IProp GF) : (▷ ∃ n m : Nat, "Ha" ∷ P n ∗ "Hb" ∷ P m) ⊢ ▷ ∃ n, P n := by
  iintro H
  iNamed H
  inext
  iexists n
  iexact Ha

/-- `solve_ndisj` proves namespace mask conditions. -/
example (N : Namespace) : (↑(N.@"inv") : CoPset) ⊆ ⊤ \ ↑(N.@"sema") := by solve_ndisj
example (N : Namespace) : (⊤ \ ↑N : CoPset) ⊆ ⊤ \ ↑(N.@"x") := by solve_ndisj
example (N : Namespace) : (↑(N.@"a") : CoPset) ## ↑(N.@"b") := by solve_ndisj
example (N : Namespace) (E : CoPset) (h : ↑N ⊆ E) :
    (↑(N.@"inv") : CoPset) ⊆ E \ ↑(N.@"sema") := by solve_ndisj
example (N : Namespace) : ¬ ((↑(N.@"inv") : CoPset) ⊆ ⊤ \ ↑(N.@"inv")) ∨ True := by
  fail_if_success (left; solve_ndisj)
  right; trivial

/-- `iinv` discharges the namespace side condition (used to be left as a goal),
also with word facts in the context. -/
example (N : Namespace) (P : IProp GF) (x y : w64) (_h1 : sint.Z x < sint.Z y)
    (_h2 : uint.Z x + 1 = uint.Z y) :
    inv (N.@"inv") P ⊢ |={⊤ \ ↑(N.@"sema")}=> True := by
  iintro #Hinv
  iinv Hinv with Hi Hclose
  imod Hclose $$ Hi with _
  imodintro; itrivial

/-- `iinv` on a non-atomic WP is an error (not a leftover `Atomic` goal). -/
example (N : Namespace) (P : IProp GF) :
    inv N P ⊢ WP gl(let: "x" := #(W64 1) in "x") {{ _v, (True : IProp GF) }} := by
  iintro #Hinv
  fail_if_success iinv Hinv with Hi Hclose
  wp_pures; itrivial

/-- `wp_if_destruct` after introducing a Lean variable inside the proof (used to
fail with "unknown free variable"). -/
example (Φ : val → IProp GF) :
    (∀ b : Bool, Φ #b) ⊢ ∀ b : Bool, WP gl(if: #b then #true else #false) {{ Φ }} := by
  iintro H %b
  wp_if_destruct
  · iapply H
  · iapply H

set_option goose.wp.extras true in
/-- `decide` with classical instances and `#a = #b` are simplified (extras). -/
example (x : w64) (v : val) (Φ : val → IProp GF) :
    Φ #true ∗ Φ #false ∗ Φ #false ∗ Φ #true ⊢
      WP (Val #(decide (x = x))) {{ Φ }} ∗ WP (Val #(!decide (v = v))) {{ Φ }} ∗
      WP (Val #(decide ((#false : val) = #true))) {{ Φ }} ∗ WP (Val #(decide True)) {{ Φ }} := by
  iintro ⟨H1, H2, H3, H4⟩
  isplitl [H1]; · wp_pures; iexact H1
  isplitl [H2]; · wp_pures; iexact H2
  isplitl [H3]; · wp_pures; iexact H3
  wp_pures; iexact H4


/-- `iNamed` does not unfold an `if` into a raw `Decidable.rec` (which could
send the kernel into a deep recursion for classical instances). -/
noncomputable def testIfProp (v : val) (P Q : IProp GF) : IProp GF :=
  if v = #(W64 3) then iprop("H" ∷ P) else iprop("H" ∷ Q)

example (v : val) (P Q : IProp GF) : testIfProp v P Q ⊢ ⌜True⌝ := by
  iintro H
  iNamed H
  -- `H : if v = #(W64 3) then .. else ..`
  by_cases h : v = #(W64 3)
  · simp only [h, ↓reduceIte]; ipureintro; trivial
  · simp only [h, ↓reduceIte]; ipureintro; trivial

/-- `iframe` frames up to computation (`[] ++ [v]`, unreduced `match`). -/
example (v : w64) (P : List w64 → IProp GF) : P [v] ⊢ P ([] ++ [v]) := by
  iintro H
  iframe

/-- `iframe` matches `W64 7` and `7#64` (e.g. after a bare `simp`). -/
example (l : Loc) (x : w64) : (l ↦ (x + 1#64) : IProp GF) ⊢ l ↦ (x + W64 1) := by
  iintro H
  iframe

/-- `iframe` uses a spatial persistent hypothesis for several conjuncts. -/
example (P : IProp GF) [Persistent P] : P ⊢ P ∗ P := by
  iintro HP
  iframe

/-- `iframe` picks the existential witness from the hypothesis that matches the
conjunct mentioning it (not `2` from `H2`). -/
example (P : Nat → IProp GF) (n : Nat) : P n ∗ P 2 ⊢ ∃ m, P m ∗ P 2 := by
  iintro ⟨H1, H2⟩
  iframe

/-- `word_lit_simp` evaluates word literals, keeping `W64 n` elsewhere. -/
example (h : uint.Z (W64 300) = 3) : sint.Z (W64 7) = 7 ∧ False := by
  word_lit_simp
  omega

/-- `wp_auto` keeps points-to facts of locations that are not Go local variables
(e.g. obtained from a spec), even if the location occurs nowhere else. -/
example (l : Loc) (v : w64) (Φ : val → IProp GF) :
    (l ↦ v) ∗ (∀ w : w64, (∃ l' : Loc, l' ↦ v) -∗ Φ #w) ⊢ WP gl(let: "x" := #(W64 1) in "x") {{ Φ }} := by
  iintro ⟨Hl, H⟩
  wp_auto
  iapply H
  iexists l
  iexact Hl

/-- `wp_apply` discharges closed pure side conditions of the spec (here the
bounds check `0 ≤ 0` of `wp_load_slice_index`). -/
example (sl : GoSlice) (x : w64) (Φ : val → IProp GF) :
    sl ↦* [x] ∗ (sl ↦* [x] -∗ Φ #x) ⊢
      WP (App (Val (GoInstruction (GoLoad go.uint64))) (Val #(sliceIndexRef w64 0 sl))) {{ Φ }} := by
  iintro ⟨Hs, H⟩
  wp_apply wp_load_slice_index sl 0 [x] _ x $$ [$Hs] as Hs
  · ipureintro; rfl
  iapply H $$ Hs

set_option goose.wp.extras true in
/-- Projections of interface values are reduced (extras). -/
example (Φ : val → IProp GF) (t : go.GoType) (v : val) :
    Φ v ⊢ WP (Val (interface.mk t v).v) {{ Φ }} := by
  iintro H; wp_pures; iexact H

end proofs

section consts
variable [FfiSyntax] [GoGlobalContext]
/-- A package constant, as goose generates it. -/
def testConst : val := #(W64 3)
/-- An implementation constant, as `wp_func_call`/`wp_method_call` produce. -/
def testFn.impl : val := LamV "x" (Var "x")
end consts

section proofs2
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [go.PreSemantics]

set_option goose.wp.extras true in
/-- With `goose.wp.extras`, `wp_auto` unfolds a package constant that blocks a step. -/
example (Φ : val → IProp GF) :
    Φ #(W64 3 + W64 1) ⊢ WP (App (Val (GoInstruction (GoOp GoPlus go.uint64)))
      (Pair (Val testConst) (Val #(W64 1)))) {{ Φ }} := by
  iintro H
  wp_auto
  iexact H

/-- `wp_auto` steps into a call of an implementation constant `Foo.impl`. -/
example (Φ : val → IProp GF) :
    Φ #(W64 3) ⊢ WP (App (Val testFn.impl) (Val #(W64 3))) {{ Φ }} := by
  iintro H
  wp_auto
  iexact H

end proofs2

/-! ### A struct, in the shape goose generates (`[ext] [ffi]` instance binders,
`heapGS hlc GF`, named field conjuncts, and `@[reducible]`
`fieldsUnsealed`/`underlying` definitions). -/

noncomputable section
namespace testpkg

def pt.ty [FfiSyntax] [GoGlobalContext] : go.GoType := (go.GoType.Named go!"testpkg.pt" [])
attribute [irreducible] pt.ty

structure pt [FfiSyntax] where
  mk ::
  x' : w64
  y' : w64
instance pt.zero_val [FfiSyntax] : ZeroVal pt := ⟨pt.mk zeroValDef zeroValDef⟩

@[reducible] def pt.fieldsUnsealed [FfiSyntax] [GoGlobalContext] : List go.field_decl :=
  [(go.field_decl.FieldDecl go!"x" go.uint64), (go.field_decl.FieldDecl go!"y" go.uint64)]
@[irreducible] def pt.fields [FfiSyntax] [GoGlobalContext] : List go.field_decl := pt.fieldsUnsealed
instance equals_unfold_pt [FfiSyntax] [GoGlobalContext] : EqualsUnfold pt.fields pt.fieldsUnsealed :=
  ⟨by unfold pt.fields; rfl⟩
@[reducible] def pt.underlying [FfiSyntax] [GoGlobalContext] : go.GoType := (go.GoType.StructType pt.fields)

class pt.TypeAssumptions [FfiSyntax] [GoGlobalContext] [GoLocalContext] [GoSemanticsFunctions] : Prop where
  type_repr : go.TypeReprUnderlying pt.underlying pt
  underlying : go.UnderlyingDirectedEq pt.ty pt.underlying
  get_x : ∀ (x : pt), go.IsGoStepPureDetTagged under (StructFieldGet pt.underlying go!"x") #x (Val #(x.x'))
  set_x : ∀ (x : pt) (y : w64), go.IsGoStepPureDetTagged under (StructFieldSet pt.underlying go!"x") (PairV #x #y) (Val #(({ x with x' := y } : pt)))
  get_y : ∀ (x : pt), go.IsGoStepPureDetTagged under (StructFieldGet pt.underlying go!"y") #x (Val #(x.y'))
  set_y : ∀ (x : pt) (y : w64), go.IsGoStepPureDetTagged under (StructFieldSet pt.underlying go!"y") (PairV #x #y) (Val #(({ x with y' := y } : pt)))
attribute [instance] pt.TypeAssumptions.type_repr pt.TypeAssumptions.underlying pt.TypeAssumptions.get_x
  pt.TypeAssumptions.set_x pt.TypeAssumptions.get_y pt.TypeAssumptions.set_y

section def_
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : pt.TypeAssumptions]

instance pt_typed_pointsto : TypedPointsto (GF := GF) pt where
  typedPointstoDef l v dq := iprop(
    "x" ∷ typedPointsto (structFieldRef pt go!"x" l) v.x' dq ∗
    "y" ∷ typedPointsto (structFieldRef pt go!"y" l) v.y' dq ∗
    "_" ∷ True)
  typedPointstoDef_dfractional := by solve_typed_pointsto_dfractional
  typedPointstoDef_timeless := by solve_typed_pointsto_timeless
  typedPointsto_agree := by solve_typed_pointsto_agree

instance pt_access_load_x (l : Loc) (v : pt) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef pt go!"x" l) v.x' dq)
      (typedPointsto (structFieldRef pt go!"x" l) v.x' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) := by
  solve_pointsto_access_struct

instance pt_access_store_x (l : Loc) (v : pt) (x' : w64) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef pt go!"x" l) v.x' (DFrac.own 1))
      (typedPointsto (structFieldRef pt go!"x" l) x' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1)) (typedPointsto l ({ v with x' := x' } : pt) (DFrac.own 1)) := by
  solve_pointsto_access_struct

instance pt_access_load_y (l : Loc) (v : pt) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef pt go!"y" l) v.y' dq)
      (typedPointsto (structFieldRef pt go!"y" l) v.y' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) := by
  solve_pointsto_access_struct

instance pt_access_store_y (l : Loc) (v : pt) (y' : w64) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef pt go!"y" l) v.y' (DFrac.own 1))
      (typedPointsto (structFieldRef pt go!"y" l) y' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1)) (typedPointsto l ({ v with y' := y' } : pt) (DFrac.own 1)) := by
  solve_pointsto_access_struct

instance pt_into_val_typed : IntoValTypedUnderlying (GF := GF) pt pt.underlying := by
  solve_into_val_typed_struct

example (l : Loc) (v : pt) :
    {{ (l ↦ v : IProp GF) }}
      gl(let: "a" := ![go.uint64] (StructFieldRef pt.ty "x" #l) in
         StructFieldRef pt.ty "y" #l <-[go.uint64] "a" ;; ![go.uint64] (StructFieldRef pt.ty "y" #l))
    {{ RET #v.x'; l ↦ ({ v with y' := v.x' } : pt) }} := by
  iintro %Φ Hl HΦ
  wp_auto
  iapply HΦ $$ Hl

/-- Projections of the zero value of a struct are reduced (extras). -/
example (Φ : val → IProp GF) : Φ #(0 : w64) ⊢ WP (Val #((zero_val pt).x')) {{ Φ }} := by
  iintro H
  wp_pures
  iexact H

end def_
end testpkg
end



/-! A struct with a by-value `uintptr` field, in the shape goose generates:
`type ub struct { p uintptr }`. -/
noncomputable section
namespace testpkg

def ub.ty [FfiSyntax] [GoGlobalContext] : go.GoType := (go.GoType.Named go!"testpkg.ub" [])
attribute [irreducible] ub.ty

structure ub [FfiSyntax] where
  mk ::
  p' : w64
instance ub.zero_val [FfiSyntax] : ZeroVal ub := ⟨ub.mk zeroValDef⟩

@[reducible] def ub.fieldsUnsealed [FfiSyntax] [GoGlobalContext] : List go.field_decl :=
  [(go.field_decl.FieldDecl go!"p" go.uintptr)]
@[irreducible] def ub.fields [FfiSyntax] [GoGlobalContext] : List go.field_decl := ub.fieldsUnsealed
instance equals_unfold_ub [FfiSyntax] [GoGlobalContext] : EqualsUnfold ub.fields ub.fieldsUnsealed :=
  ⟨by unfold ub.fields; rfl⟩
@[reducible] def ub.underlying [FfiSyntax] [GoGlobalContext] : go.GoType := (go.GoType.StructType ub.fields)

class ub.TypeAssumptions [FfiSyntax] [GoGlobalContext] [GoLocalContext] [GoSemanticsFunctions] : Prop where
  type_repr : go.TypeReprUnderlying ub.underlying ub
  underlying : go.UnderlyingDirectedEq ub.ty ub.underlying
  get_p : ∀ (x : ub), go.IsGoStepPureDetTagged under (StructFieldGet ub.underlying go!"p") #x (Val #(x.p'))
  set_p : ∀ (x : ub) (y : w64), go.IsGoStepPureDetTagged under (StructFieldSet ub.underlying go!"p") (PairV #x #y) (Val #(({ x with p' := y } : ub)))
attribute [instance] ub.TypeAssumptions.type_repr ub.TypeAssumptions.underlying
  ub.TypeAssumptions.get_p ub.TypeAssumptions.set_p

section def_
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : ub.TypeAssumptions]

instance ub_typed_pointsto : TypedPointsto (GF := GF) ub where
  typedPointstoDef l v dq := iprop(
    "p" ∷ typedPointsto (structFieldRef ub go!"p" l) v.p' dq ∗
    "_" ∷ True)
  typedPointstoDef_dfractional := by solve_typed_pointsto_dfractional
  typedPointstoDef_timeless := by solve_typed_pointsto_timeless
  typedPointsto_agree := by solve_typed_pointsto_agree

instance ub_access_load_p (l : Loc) (v : ub) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef ub go!"p" l) v.p' dq)
      (typedPointsto (structFieldRef ub go!"p" l) v.p' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) := by
  solve_pointsto_access_struct

instance ub_access_store_p (l : Loc) (v : ub) (p' : w64) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef ub go!"p" l) v.p' (DFrac.own 1))
      (typedPointsto (structFieldRef ub go!"p" l) p' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1)) (typedPointsto l ({ v with p' := p' } : ub) (DFrac.own 1)) := by
  solve_pointsto_access_struct

instance ub_into_val_typed : IntoValTypedUnderlying (GF := GF) ub ub.underlying := by
  solve_into_val_typed_struct

/-- Load, increment and store the `uintptr` field. -/
example (l : Loc) (v : ub) :
    {{ (l ↦ v : IProp GF) }}
      gl(StructFieldRef ub.ty "p" #l <-[go.uintptr]
           (![go.uintptr] (StructFieldRef ub.ty "p" #l) +⟨go.uintptr⟩ #(W64 1)) ;;
         ![go.uintptr] (StructFieldRef ub.ty "p" #l))
    {{ RET #(v.p' + W64 1); l ↦ ({ v with p' := v.p' + W64 1 } : ub) }} := by
  iintro %Φ Hl HΦ
  wp_auto
  iapply HΦ $$ Hl

end def_
end testpkg
end

/-! ### `uintptr` (see `go.UintptrSemantics`): a 64-bit unsigned integer -/
section uintptr_tests
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [go.PreSemantics]

/-- Allocation, load, store and wrapping addition at `uintptr`. -/
example : ⊢ WP gl(let: "x" := GoAlloc go.uintptr #(W64 (2^64 - 1)) in
     "x" <-[go.uintptr] (![go.uintptr] "x" +⟨go.uintptr⟩ #(W64 1)) ;;
     ![go.uintptr] "x") {{ v, (⌜v = #(W64 0)⌝ : IProp GF) }} := by
  wp_auto
  ipureintro; rfl

/-- The zero value of `uintptr` is `W64 0`. -/
example : ⊢ WP (App (Val (GoInstruction (GoZeroVal go.uintptr))) (Val #()))
    {{ v, (⌜v = #(W64 0)⌝ : IProp GF) }} := by
  wp_auto
  ipureintro; rfl

/-- Typed points-to and `wp_load` at `uintptr`. -/
example (l : Loc) (v : w64) (Φ : val → IProp GF) :
    (l ↦ v) ∗ (l ↦ v -∗ Φ #v) ⊢ WP gl(![go.uintptr] #l) {{ Φ }} := by
  iintro ⟨Hl, H⟩
  wp_apply IntoValTyped.wp_load (t := go.uintptr) l (DFrac.own 1) v $$ [$Hl] as Hl
  iapply H $$ Hl

/-- Comparisons at `uintptr` are unsigned. -/
example (Φ : val → IProp GF) :
    Φ #true ⊢ WP gl(#(W64 1) <⟨go.uintptr⟩ #(W64 (2^64 - 1))) {{ Φ }} := by
  iintro H
  wp_auto
  iexact H

example (Φ : val → IProp GF) (x : w64) :
    Φ #true ⊢ WP gl(#x =⟨go.uintptr⟩ #x) {{ Φ }} := by
  iintro H
  wp_auto
  iexact H

/-- Conversions to and from `uintptr` (identity on 64-bit types, truncation to narrower ones). -/
example (Φ : val → IProp GF) (x : w64) :
    Φ #x ⊢ WP (App (Val (GoInstruction (Convert go.uintptr go.uint64)))
      (App (Val (GoInstruction (Convert go.uint64 go.uintptr))) (Val #x))) {{ Φ }} := by
  iintro H
  wp_auto
  iexact H

example (Φ : val → IProp GF) :
    Φ #(W8 1) ⊢ WP (App (Val (GoInstruction (Convert go.uintptr go.uint8)))
      (App (Val (GoInstruction (Convert go.int go.uintptr))) (Val #(W64 257)))) {{ Φ }} := by
  iintro H
  wp_auto
  rw [show W8 (uint.Z (W64 257)) = W8 1 from rfl]
  iexact H

end uintptr_tests

end Perennial
