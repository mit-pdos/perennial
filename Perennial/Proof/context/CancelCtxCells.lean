/-
The `atomic.Value` cells `done` and `err` of a `*cancelCtx`: the triples of `c.done.Load()` and
`c.err.Load()` (calls of `(*atomic.Value).Load` on the fields), from its spec (a hypothesis;
`Results.lean` has them under their old names, without it).
-/
module

public import Perennial.Proof.context.Base
public import Perennial.Spec.sync.atomic.Value__Load

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace context

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

open ContextDesc

/-! ### The `atomic.Value` cells of a `*cancelCtx` -/

/-- `c.done.Load()` without the lock: `nil`, or a determined Done channel. -/
theorem wp_done_Load_of
    (wp_VLoad : sync.atomic.Value.Load.spec (GF := GF) (hG := hG))
    (c : Loc) (γ : ContextNames) (P : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isCancelCtxOf c γ P }}
      (App (Val (structFieldRef context.cancelCtx go!"done" c @!!
        go.GoType.PointerType sync.atomic.Value.ty @!! go!"Load")) (Val #()))
    {{ (od : Option GoChan), RET #(doneAny od);
        match od with
        | none => iprop(True)
        | some ch => ∃ γch, isContextDone (cdesc γ P) ch γch ∗ doneFresh γ P ch }} := by
  iintro %Φ ⟨#Hpkg, #Hc⟩ HΦ
  unfold isCancelCtxOf
  iNamed Hc
  iapply wp_VLoad _ (DFrac.own 1) $$ [] [-]
  all_goals try inonnull
  all_goals try (ipureintro; first | exact Hcal.1 | exact Hcal.2)
  · iPkgInit
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  unfold cancelCtxInv
  icases Hi with ⟨%od, %e, Hdone, Hdg, Herr, Hcg⟩
  iexists doneAny od
  iframe Hdone
  iintro Hdone
  imod Hmask with -
  cases od with
  | none =>
    imod Hclose $$ [Hdone Hdg Herr Hcg] with -
    · inext; iexists none, e; iframe
    imodintro
    iapply HΦ $$ %none
    itrivial
  | some ch =>
    icases Hdg with ⟨%γch, #Hd, #Hfr⟩
    imod Hclose $$ [Hdone Herr Hcg] with -
    · inext; iexists (some ch), e; iframe; iexists γch; iframe #
    imodintro
    iapply HΦ $$ %(some ch)
    iexists γch; iframe #

/-- `c.done.Load()` given the lock invariant's half of the done cell, which determines the
result. -/
theorem wp_done_Load_frag_of
    (wp_VLoad : sync.atomic.Value.Load.spec (GF := GF) (hG := hG))
    (c : Loc) (γ : ContextNames) (P : IProp GF) (od : Option GoChan) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isCancelCtxOf c γ P ∗ doneFrag γ od }}
      (App (Val (structFieldRef context.cancelCtx go!"done" c @!!
        go.GoType.PointerType sync.atomic.Value.ty @!! go!"Load")) (Val #()))
    {{ RET #(doneAny od); doneFrag γ od ∗
        match od with
        | none => iprop(True)
        | some ch => ∃ γch, isContextDone (cdesc γ P) ch γch ∗ doneFresh γ P ch }} := by
  iintro %Φ ⟨#Hpkg, #Hc, Hf⟩ HΦ
  unfold isCancelCtxOf
  iNamed Hc
  iapply wp_VLoad _ (DFrac.own 1) $$ [] [-]
  all_goals try inonnull
  all_goals try (ipureintro; first | exact Hcal.1 | exact Hcal.2)
  · iPkgInit
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  unfold cancelCtxInv
  icases Hi with ⟨%od', %e, Hdone, Hdg, Herr, Hcg⟩
  ihave %Heq : ⌜od' = od⌝ $$ [Hdg Hf]
  · cases od' <;> cases od <;> unfold doneFrag <;> dsimp only
    · ipureintro; rfl
    · ihave %h := dghostVar_agree _ _ _ _ _ $$ Hdg Hf
      ipureintro; cases h
    · icases Hdg with ⟨%γch, Hd, -⟩
      rw [isContextDone_unseal]; unfold isContextDoneDef cdesc
      icases Hd with ⟨Hd, -⟩
      ihave %h := dghostVar_agree _ _ _ _ _ $$ Hd Hf
      ipureintro; cases h
    · icases Hdg with ⟨%γch, Hd, -⟩
      rw [isContextDone_unseal]; unfold isContextDoneDef cdesc
      icases Hd with ⟨Hd, -⟩
      ihave %h := dghostVar_agree _ _ _ _ _ $$ Hd Hf
      ipureintro; rw [h]
  subst Heq
  iexists doneAny od'
  iframe Hdone
  iintro Hdone
  imod Hmask with -
  cases od' with
  | none =>
    imod Hclose $$ [Hdone Hdg Herr Hcg] with -
    · inext; iexists none, e; iframe
    imodintro
    iapply HΦ
    iframe Hf
  | some ch =>
    icases Hdg with ⟨%γch, #Hd, #Hfr⟩
    imod Hclose $$ [Hdone Herr Hcg] with -
    · inext; iexists (some ch), e; iframe; iexists γch; iframe #
    imodintro
    iapply HΦ
    iframe Hf
    iexists γch; iframe #

/-- `c.err.Load()` without the lock; given `ContextClosed γ` (`cl`), the error is not `nil`. -/
theorem wp_err_Load_of
    (wp_VLoad : sync.atomic.Value.Load.spec (GF := GF) (hG := hG))
    (c : Loc) (γ : ContextNames) (P : IProp GF) (cl : Bool) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isCancelCtxOf c γ P ∗
        (if cl then ContextClosed γ else iprop(True)) }}
      (App (Val (structFieldRef context.cancelCtx go!"err" c @!!
        go.GoType.PointerType sync.atomic.Value.ty @!! go!"Load")) (Val #()))
    {{ (e : GoInterface), RET #e; ⌜cl = true → e ≠ interface.nil⌝ ∗
        (if e = interface.nil then iprop(True)
         else iprop(⌜isTypedErr e⌝ ∗ □ P ∗ ContextClosed γ)) }} := by
  iintro %Φ ⟨#Hpkg, #Hc, Hcl⟩ HΦ
  unfold isCancelCtxOf
  iNamed Hc
  iapply wp_VLoad _ (DFrac.own 1) $$ [] [-]
  all_goals try inonnull
  all_goals try (ipureintro; first | exact Hcal.1 | exact Hcal.2)
  · iPkgInit
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  unfold cancelCtxInv
  icases Hi with ⟨%od, %e, Hdone, Hdg, Herr, Hcg⟩
  iexists e
  iframe Herr
  iintro Herr
  imod Hmask with -
  by_cases he : e = interface.nil
  · subst he
    cases cl
    · imod Hclose $$ [Hdone Hdg Herr Hcg] with -
      · inext; iexists od, GoInterface.nil; iframe
      imodintro
      iapply HΦ
      rw [ite_eq_left rfl]
      isplitl []
      · ipureintro; intro h; cases h
      · itrivial
    · rw [ite_eq_left rfl] at *
      simp only [↓reduceIte, ContextClosed]
      ihave %h := dghostVar_agree _ _ _ _ _ $$ Hcl Hcg
      cases h
  · simp only [he, ↓reduceIte]
    icases Hcg with ⟨%ht, #Hp, #Hc⟩
    imod Hclose $$ [Hdone Hdg Herr] with -
    · inext; iexists od, e; iframe Hdone Hdg Herr
      simp only [he, ↓reduceIte, named]
      iframe #; ipureintro; exact ht
    imodintro
    iapply HΦ
    isplitl []
    · ipureintro; intro _; exact he
    · simp only [he, ↓reduceIte]
      iframe #; ipureintro; exact ht

/-- `c.err.Load()` given the lock invariant's half of the closed flag, which determines whether
the result is `nil`. -/
theorem wp_err_Load_frag_of
    (wp_VLoad : sync.atomic.Value.Load.spec (GF := GF) (hG := hG))
    (c : Loc) (γ : ContextNames) (P : IProp GF) (closed : Bool) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isCancelCtxOf c γ P ∗ closedFrag γ closed }}
      (App (Val (structFieldRef context.cancelCtx go!"err" c @!!
        go.GoType.PointerType sync.atomic.Value.ty @!! go!"Load")) (Val #()))
    {{ (e : GoInterface), RET #e; closedFrag γ closed ∗
        ⌜closed = false → e = interface.nil⌝ ∗ ⌜closed = true → isTypedErr e⌝ ∗
        □ (⌜closed = true⌝ -∗ P) }} := by
  iintro %Φ ⟨#Hpkg, #Hc, Hf⟩ HΦ
  unfold isCancelCtxOf
  iNamed Hc
  iapply wp_VLoad _ (DFrac.own 1) $$ [] [-]
  all_goals try inonnull
  all_goals try (ipureintro; first | exact Hcal.1 | exact Hcal.2)
  · iPkgInit
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  unfold cancelCtxInv
  icases Hi with ⟨%od, %e, Hdone, Hdg, Herr, Hcg⟩
  iexists e
  iframe Herr
  iintro Herr
  imod Hmask with -
  by_cases he : e = interface.nil
  · subst he
    cases closed <;> simp only [closedFrag, ContextClosed, Bool.false_eq_true, ↓reduceIte]
    · imod Hclose $$ [Hdone Hdg Herr Hcg] with -
      · inext; iexists od, GoInterface.nil; iframe Hdone Hdg Herr; rw [ite_eq_left rfl]; iexact Hcg
      imodintro
      iapply HΦ
      iframe Hf
      isplitl []; · ipureintro; intro _; rfl
      isplitl []; · ipureintro; intro h; cases h
      imodintro; iintro %h; cases h
    · ihave %h := dghostVar_agree _ _ _ _ _ $$ Hf Hcg
      cases h
  · simp only [he, ↓reduceIte]
    icases Hcg with ⟨%ht, #Hp, #Hc⟩
    cases closed <;> simp only [closedFrag, Bool.false_eq_true, ↓reduceIte]
    · unfold ContextClosed
      ihave %h := dghostVar_agree _ _ _ _ _ $$ Hf Hc
      cases h
    · imod Hclose $$ [Hdone Hdg Herr] with -
      · inext; iexists od, e; iframe Hdone Hdg Herr
        simp only [he, ↓reduceIte, named]
        iframe #; ipureintro; exact ht
      imodintro
      iapply HΦ
      iframe Hf
      isplitl []; · ipureintro; intro h; cases h
      isplitl []; · ipureintro; intro _; exact ht
      imodintro; iintro -; iexact Hp

/-- `c.done.Load()` once the Done channel `ch` is known: it returns `ch`. -/
theorem wp_done_Load_known_of
    (wp_VLoad : sync.atomic.Value.Load.spec (GF := GF) (hG := hG))
    (c : Loc) (γ : ContextNames) (P : IProp GF) (ch : GoChan) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isCancelCtxOf c γ P ∗
        dghostVar γ.doneGn .discard (some ch) }}
      (App (Val (structFieldRef context.cancelCtx go!"done" c @!!
        go.GoType.PointerType sync.atomic.Value.ty @!! go!"Load")) (Val #()))
    {{ RET #(doneAny (some ch)); True }} := by
  iintro %Φ ⟨#Hpkg, #Hc, #Hdd⟩ HΦ
  unfold isCancelCtxOf
  iNamed Hc
  iapply wp_VLoad _ (DFrac.own 1) $$ [] [-]
  all_goals try inonnull
  all_goals try (ipureintro; first | exact Hcal.1 | exact Hcal.2)
  · iPkgInit
  iinv Hinv with Hi Hclose
  all_goals try solve_ndisj
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  unfold cancelCtxInv
  icases Hi with ⟨%od, %e, Hdone, Hdg, Herr, Hcg⟩
  cases od
  case none =>
    dsimp only
    ihave %h := dghostVar_agree _ _ _ _ _ $$ Hdd Hdg
    cases h
  case some ch' =>
    icases Hdg with ⟨%γ', #Hd2, #Hfr⟩
    ihave #Hdd2 := isContextDone_doneGn _ _ _ $$ Hd2
    ihave %h := dghostVar_agree _ _ _ _ _ $$ Hdd Hdd2
    cases h
    iexists doneAny (some ch)
    iframe Hdone
    iintro Hdone
    imod Hmask with -
    imod Hclose $$ [Hdone Herr Hcg] with -
    · inext; iexists (some ch), e; iframe
      iexists γ'
      iframe #
    imodintro
    iapply HΦ $$ []
    itrivial

end wps

end context

end Perennial
