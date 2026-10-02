/-
Small worked examples of the GooseLang proof tactics (`wp_start`, `wp_auto`,
`wp_apply`, `wp_pures`, `wp_bind`, `wp_load`/`wp_store`/`wp_alloc`, `wp_for`,
`iNamed`) on hand-written GooseLang functions in the style of goose's output.
These double as regression tests and as examples for proof porters.
-/
import Perennial.Golang.Theory

namespace Perennial
open Iris Iris.BI

section code
variable [ffi_syntax] [GoGlobalContext]

/-- `func addOne(x uint64) uint64 { return x + 1 }` -/
def addOne : val :=
  LamV "x" (App (Val exception_do)
    (Let "x" (App (Val (GoInstruction (GoAlloc go.uint64))) (Var "x"))
    (App (Val do_return)
      (App (Val (GoInstruction (GoOp GoPlus go.uint64)))
        (Pair (App (Val (GoInstruction (GoLoad go.uint64))) (Var "x")) (Val #(W64 1)))))))

/-- `func callAddOne(y uint64) uint64 { return addOne(y) }` -/
def callAddOne : val :=
  LamV "y" (App (Val exception_do)
    (Let "y" (App (Val (GoInstruction (GoAlloc go.uint64))) (Var "y"))
    (App (Val do_return)
      (Let "$a0" (App (Val (GoInstruction (GoLoad go.uint64))) (Var "y"))
      (App (Val addOne) (Var "$a0"))))))

/-- `func countTo(n uint64) uint64 { var i uint64; for i < n { i = i + 1 }; return i }` -/
def countTo : val :=
  LamV "n" (App (Val exception_do)
    (Let "n" (App (Val (GoInstruction (GoAlloc go.uint64))) (Var "n"))
    (Let "i" (App (Val (GoInstruction (GoAlloc go.uint64)))
      (App (Val (GoInstruction (GoZeroVal go.uint64))) (Val #())))
    (App (App (Val exception_seq) (Lam BAnon
      (App (Val do_return) (App (Val (GoInstruction (GoLoad go.uint64))) (Var "i")))))
    (App (App (App (Val do_for)
      (Lam BAnon (App (Val (GoInstruction (GoOp GoLt go.uint64)))
        (Pair (App (Val (GoInstruction (GoLoad go.uint64))) (Var "i"))
              (App (Val (GoInstruction (GoLoad go.uint64))) (Var "n"))))))
      (Lam BAnon (App (Val do_execute)
        (App (Val (GoInstruction (GoStore go.uint64))) (Pair (Var "i")
          (App (Val (GoInstruction (GoOp GoPlus go.uint64)))
            (Pair (App (Val (GoInstruction (GoLoad go.uint64))) (Var "i")) (Val #(W64 1)))))))))
      (Lam BAnon (Val #())))))))

end code

section proofs
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
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
  · iexists _; iframe i; ipureintro; simp [zero_val, ZeroVal.zero_val_def, uint.Z]
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
example (l : loc) (v : w64) (Φ : val → IProp GF) :
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
example (l : loc) (f : func.t) (Φ : val → IProp GF) :
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
example (l : loc) (v : w64) (Φ : val → IProp GF) :
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

set_option goose.wp.extras true in
/-- Projections of interface values are reduced (extras). -/
example (Φ : val → IProp GF) (t : go.type) (v : val) :
    Φ v ⊢ WP (Val (interface.mk t v).v) {{ Φ }} := by
  iintro H; wp_pures; iexact H

end proofs

section consts
variable [ffi_syntax] [GoGlobalContext]
/-- A package constant, as goose generates it. -/
def testConst : val := #(W64 3)
end consts

section proofs2
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [GoSemanticsFunctions] [go.PreSemantics]

set_option goose.wp.extras true in
/-- With `goose.wp.extras`, `wp_auto` unfolds a package constant that blocks a step. -/
example (Φ : val → IProp GF) :
    Φ #(W64 3 + W64 1) ⊢ WP (App (Val (GoInstruction (GoOp GoPlus go.uint64)))
      (Pair (Val testConst) (Val #(W64 1)))) {{ Φ }} := by
  iintro H
  wp_auto
  iexact H

end proofs2

/-! ### A struct, in the shape goose generates (with the template changes
described in the porting notes: `[ext] [ffi]` instance binders, `heapGS hlc GF`,
named field conjuncts, and `@[reducible]` `'fds_unsealed`/`ⁱᵐᵖˡ` definitions). -/

noncomputable section
namespace testpkg

def pt [ffi_syntax] [GoGlobalContext] : go.type := (go.type.Named go!"testpkg.pt" [])
attribute [irreducible] pt

namespace pt
structure t [ffi_syntax] where
  mk ::
  x' : w64
  y' : w64
instance zero_val [ffi_syntax] : ZeroVal t := ⟨t.mk zero_val_def zero_val_def⟩
end pt

@[reducible] def pt'fds_unsealed [ffi_syntax] [GoGlobalContext] : List go.field_decl :=
  [(go.field_decl.FieldDecl go!"x" go.uint64), (go.field_decl.FieldDecl go!"y" go.uint64)]
@[irreducible] def pt'fds [ffi_syntax] [GoGlobalContext] : List go.field_decl := pt'fds_unsealed
instance equals_unfold_pt [ffi_syntax] [GoGlobalContext] : EqualsUnfold pt'fds pt'fds_unsealed :=
  ⟨by unfold pt'fds; rfl⟩
@[reducible] def «ptⁱᵐᵖˡ» [ffi_syntax] [GoGlobalContext] : go.type := (go.type.StructType pt'fds)

class pt_Assumptions [ffi_syntax] [GoGlobalContext] [GoLocalContext] [GoSemanticsFunctions] : Prop where
  pt_type_repr : go.TypeReprUnderlying «ptⁱᵐᵖˡ» pt.t
  pt_underlying : go.UnderlyingDirectedEq pt «ptⁱᵐᵖˡ»
  pt_get_x : ∀ (x : pt.t), go.IsGoStepPureDetTagged under (StructFieldGet «ptⁱᵐᵖˡ» go!"x") #x (Val #(x.x'))
  pt_set_x : ∀ (x : pt.t) (y : w64), go.IsGoStepPureDetTagged under (StructFieldSet «ptⁱᵐᵖˡ» go!"x") (PairV #x #y) (Val #(({ x with x' := y } : pt.t)))
  pt_get_y : ∀ (x : pt.t), go.IsGoStepPureDetTagged under (StructFieldGet «ptⁱᵐᵖˡ» go!"y") #x (Val #(x.y'))
  pt_set_y : ∀ (x : pt.t) (y : w64), go.IsGoStepPureDetTagged under (StructFieldSet «ptⁱᵐᵖˡ» go!"y") (PairV #x #y) (Val #(({ x with y' := y } : pt.t)))
attribute [instance] pt_Assumptions.pt_type_repr pt_Assumptions.pt_underlying pt_Assumptions.pt_get_x
  pt_Assumptions.pt_set_x pt_Assumptions.pt_get_y pt_Assumptions.pt_set_y

section def_
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : pt_Assumptions]

instance pt_typed_pointsto : TypedPointsto (GF := GF) pt.t where
  typed_pointsto_def l v dq := iprop(
    "x" ∷ typed_pointsto (struct_field_ref pt.t go!"x" l) v.x' dq ∗
    "y" ∷ typed_pointsto (struct_field_ref pt.t go!"y" l) v.y' dq ∗
    "_" ∷ True)
  typed_pointsto_def_dfractional := by solve_typed_pointsto_dfractional
  typed_pointsto_def_timeless := by solve_typed_pointsto_timeless
  typed_pointsto_agree := by solve_typed_pointsto_agree

instance pt_access_load_x (l : loc) (v : pt.t) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typed_pointsto (struct_field_ref pt.t go!"x" l) v.x' dq)
      (typed_pointsto (struct_field_ref pt.t go!"x" l) v.x' dq)
      (typed_pointsto l v dq) (typed_pointsto l v dq) := by
  solve_pointsto_access_struct

instance pt_access_store_x (l : loc) (v : pt.t) (x' : w64) :
    AccessStrict (PROP := IProp GF)
      (typed_pointsto (struct_field_ref pt.t go!"x" l) v.x' (DFrac.own 1))
      (typed_pointsto (struct_field_ref pt.t go!"x" l) x' (DFrac.own 1))
      (typed_pointsto l v (DFrac.own 1)) (typed_pointsto l ({ v with x' := x' } : pt.t) (DFrac.own 1)) := by
  solve_pointsto_access_struct

instance pt_access_load_y (l : loc) (v : pt.t) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typed_pointsto (struct_field_ref pt.t go!"y" l) v.y' dq)
      (typed_pointsto (struct_field_ref pt.t go!"y" l) v.y' dq)
      (typed_pointsto l v dq) (typed_pointsto l v dq) := by
  solve_pointsto_access_struct

instance pt_access_store_y (l : loc) (v : pt.t) (y' : w64) :
    AccessStrict (PROP := IProp GF)
      (typed_pointsto (struct_field_ref pt.t go!"y" l) v.y' (DFrac.own 1))
      (typed_pointsto (struct_field_ref pt.t go!"y" l) y' (DFrac.own 1))
      (typed_pointsto l v (DFrac.own 1)) (typed_pointsto l ({ v with y' := y' } : pt.t) (DFrac.own 1)) := by
  solve_pointsto_access_struct

instance pt_into_val_typed : IntoValTypedUnderlying (GF := GF) pt.t «ptⁱᵐᵖˡ» := by
  solve_into_val_typed_struct

example (l : loc) (v : pt.t) :
    {{ (l ↦ v : IProp GF) }}
      gl(let: "a" := ![go.uint64] (StructFieldRef pt "x" #l) in
         StructFieldRef pt "y" #l <-[go.uint64] "a" ;; ![go.uint64] (StructFieldRef pt "y" #l))
    {{ RET #v.x'; l ↦ ({ v with y' := v.x' } : pt.t) }} := by
  iintro %Φ Hl HΦ
  wp_auto
  iapply HΦ $$ Hl

end def_
end testpkg
end

end Perennial
