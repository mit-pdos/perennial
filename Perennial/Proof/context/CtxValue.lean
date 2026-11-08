/-
`Context.Value` at keys other than `&cancelCtxKey` (`docs/design/context-value.md`; the file is not
named after `value`, the Go function, which a proof file of its own would be).

`ctxValue x k R` (persistent): both `x.Value(k)` and `context.value(x, k)` return a result
satisfying `R`. It is a chain description (`ctxChain`) of the contexts `value` walks through
from `x`: a `*cancelCtx` or a `*timerCtx` (at a key other than `&cancelCtxKey`), whose parent is
read from its `Context` field; a `*valueCtx`, whose fields are given; and a root, `Background()`,
`TODO()`, or a context of another type with its own `Value` spec. The laws (`ctxValue_background`,
`ctxValue_todo`, `ctxValue_cancel`, `ctxValue_timer`, `ctxValue_valueCtx`, `ctxValue_other`)
build it; `wp_value` and `ctxValue_Value` use it.
-/
module

public import Perennial.Proof.context.Base

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace context

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

/-- The context `TODO()` returns: a `todoCtx{}` as a `Context`. -/
abbrev todoCtxVal : GoInterfaceOk :=
  interface.mk todoCtx.ty #(zero_val todoCtx)

/-- The `Context` field of the `*valueCtx` `p`. -/
abbrev vctxField [GoSemanticsFunctions] (p : Loc) : Loc :=
  structFieldRef context.valueCtx go!"Context" p

/-- The types whose fields `context.value` reads directly (or returns `nil` for), instead of
calling their `Value` method. -/
def valueSpecialTypes : List go.GoType :=
  [go.GoType.PointerType valueCtx.ty, go.GoType.PointerType cancelCtx.ty, withoutCancelCtx.ty,
   go.GoType.PointerType timerCtx.ty, backgroundCtx.ty, todoCtx.ty]

/-- Comparing `k` with `key` (as `any`, either way round) does not panic: when both hold values of
the same dynamic type, that type's comparison of them is equality of values. -/
def keyEqOk (k key : GoInterface) : IProp GF :=
  iprop(□ ∀ (ki kk : GoInterfaceOk) (Φ : val → IProp GF),
    ⌜(k = GoInterface.ok ki ∧ key = GoInterface.ok kk ∨ k = GoInterface.ok kk ∧
      key = GoInterface.ok ki) ∧ ki.ty = kk.ty⌝ -∗
    Φ #(decide (ki.v = kk.v)) -∗
    WP gl(CheckComparable ki.ty ;; GoOp GoEquals ki.ty glv((ki.v, kk.v))) {{ Φ }})

instance keyEqOk_persistent (k key : GoInterface) : Persistent (keyEqOk (GF := GF) k key) := by
  unfold keyEqOk; infer_instance

/-- `k` is not a `*int` key, so comparing it with `&cancelCtxKey` (as `any`) is `false` without
comparing pointers. -/
def notIntPtrKey (k : GoInterface) : Prop :=
  ∀ ki : GoInterfaceOk, k = GoInterface.ok ki → ki.ty ≠ go.GoType.PointerType go.int

/-- One link of the chain `context.value` walks. -/
inductive CtxLink where
  | cancel (c : Loc)
  | timer (c : Loc)
  | valCtx (p : Loc) (key val : GoInterface)

/-- `x` is the head of the chain `l` of contexts `value(x, k)` walks, ending at a root whose
answer satisfies `R` (persistent). -/
def ctxChain (k : GoInterface) (R : GoInterface → Prop) : GoInterfaceOk → List CtxLink → IProp GF
  | x, [] =>
      iprop(⌜(x = backgroundCtxVal ∨ x = todoCtxVal) ∧ R interface.nil⌝ ∨
        (⌜x.ty ∉ valueSpecialTypes⌝ ∗
          □ ∀ Φ : val → IProp GF, ▷ (∀ v : GoInterface, ⌜R v⌝ -∗ Φ #v) -∗
            WP (App (Val #(methods x.ty go!"Value" x.v)) (Val #k)) {{ Φ }}))
  | x, .cancel c :: l =>
      iprop(⌜x = interface.mk (go.GoType.PointerType cancelCtx.ty) #c ∧ notIntPtrKey k⌝ ∗
        ∃ p : GoInterfaceOk, ctxField c ↦□ (interface.ok p : GoInterface) ∗ ctxChain k R p l)
  | x, .timer c :: l =>
      iprop(⌜x = interface.mk (go.GoType.PointerType timerCtx.ty) #c ∧ notIntPtrKey k⌝ ∗
        ∃ p : GoInterfaceOk, ctxField (tcc c) ↦□ (interface.ok p : GoInterface) ∗
          ctxChain k R p l)
  | x, .valCtx q key val :: l =>
      iprop(⌜x = interface.mk (go.GoType.PointerType valueCtx.ty) #q⌝ ∗
        ∃ p : GoInterfaceOk, vctxField q ↦□ (interface.ok p : GoInterface) ∗
          structFieldRef context.valueCtx go!"key" q ↦□ key ∗
          structFieldRef context.valueCtx go!"val" q ↦□ val ∗ keyEqOk k key ∗
          (if k = key then iprop(⌜R val⌝) else ctxChain k R p l))

instance ctxChain_persistent (k : GoInterface) (R : GoInterface → Prop) (x : GoInterfaceOk)
    (l : List CtxLink) : Persistent (ctxChain (GF := GF) k R x l) := by
  induction l generalizing x with
  | nil => unfold ctxChain; infer_instance
  | cons a l ih =>
    cases a with
    | cancel c => unfold ctxChain; infer_instance
    | timer c => unfold ctxChain; infer_instance
    | valCtx q key val =>
      unfold ctxChain
      by_cases h : k = key
      · simp only [h, ite_true]; infer_instance
      · simp only [h, ite_false]; infer_instance

/-- **`x.Value(k)` and `context.value(x, k)` return a result satisfying `R`** (persistent). -/
def ctxValue (x : GoInterfaceOk) (k : GoInterface) (R : GoInterface → Prop) : IProp GF :=
  iprop(∃ l : List CtxLink, ctxChain k R x l)

/-- **`child` answers every key that is not a `*int` as `parent` does** (persistent): what
`WithCancel(parent)` and the deadline constructors give of the new context. -/
def ctxValueFrom (parent child : GoInterfaceOk) : IProp GF :=
  iprop(□ ∀ (k : GoInterface) (R : GoInterface → Prop), ⌜notIntPtrKey k⌝ -∗
    ctxValue parent k R -∗ ctxValue child k R)

instance ctxValueFrom_persistent (parent child : GoInterfaceOk) :
    Persistent (ctxValueFrom (GF := GF) parent child) := by
  unfold ctxValueFrom; infer_instance

instance ctxValue_persistent (x : GoInterfaceOk) (k : GoInterface) (R : GoInterface → Prop) :
    Persistent (ctxValue (GF := GF) x k R) := by
  unfold ctxValue; infer_instance

end defs

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

theorem ty_ne_vc_cc : go.GoType.PointerType valueCtx.ty ≠ go.GoType.PointerType cancelCtx.ty := by
  unfold valueCtx.ty cancelCtx.ty; simp
theorem ty_ne_cc_vc : go.GoType.PointerType cancelCtx.ty ≠ go.GoType.PointerType valueCtx.ty :=
  fun h => ty_ne_vc_cc h.symm
theorem ty_ne_tc_vc : go.GoType.PointerType timerCtx.ty ≠ go.GoType.PointerType valueCtx.ty := by
  unfold valueCtx.ty timerCtx.ty; simp
theorem ty_ne_tc_cc : go.GoType.PointerType timerCtx.ty ≠ go.GoType.PointerType cancelCtx.ty := by
  unfold cancelCtx.ty timerCtx.ty; simp
theorem ty_ne_tc_wc : go.GoType.PointerType timerCtx.ty ≠ withoutCancelCtx.ty := by
  unfold withoutCancelCtx.ty; simp
theorem ty_ne_bg_vc : backgroundCtx.ty ≠ go.GoType.PointerType valueCtx.ty := by
  unfold backgroundCtx.ty; simp
theorem ty_ne_bg_cc : backgroundCtx.ty ≠ go.GoType.PointerType cancelCtx.ty := by
  unfold backgroundCtx.ty; simp
theorem ty_ne_bg_wc : backgroundCtx.ty ≠ withoutCancelCtx.ty := by
  unfold backgroundCtx.ty withoutCancelCtx.ty; simp
theorem ty_ne_bg_tc : backgroundCtx.ty ≠ go.GoType.PointerType timerCtx.ty := by
  unfold backgroundCtx.ty; simp
theorem ty_ne_bg_td : backgroundCtx.ty ≠ todoCtx.ty := by
  unfold backgroundCtx.ty todoCtx.ty; simp
theorem ty_ne_td_vc : todoCtx.ty ≠ go.GoType.PointerType valueCtx.ty := by
  unfold todoCtx.ty; simp
theorem ty_ne_td_cc : todoCtx.ty ≠ go.GoType.PointerType cancelCtx.ty := by
  unfold todoCtx.ty; simp
theorem ty_ne_td_wc : todoCtx.ty ≠ withoutCancelCtx.ty := by
  unfold todoCtx.ty withoutCancelCtx.ty; simp
theorem ty_ne_td_tc : todoCtx.ty ≠ go.GoType.PointerType timerCtx.ty := by
  unfold todoCtx.ty; simp

theorem wp_background_Value (k : GoInterface) :
    {{ (True : IProp GF) }}
      (App (Val #(methods backgroundCtx.ty go!"Value" #(zero_val backgroundCtx))) (Val #k))
    {{ RET #(interface.nil : GoInterface); True }} := by
  wp_start
  wp_method_call
  wp_auto
  iapply HΦ
  itrivial

theorem wp_value_chain (k : GoInterface) (R : GoInterface → Prop) (l : List CtxLink)
    (x : GoInterfaceOk) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ ctxChain k R x l }}
      (App (App (Val (@! context.value)) (Val #(interface.ok x))) (Val #k))
    {{ (w : GoInterface), RET #w; ⌜R w⌝ }} := by
  wp_start as #Hch
  wp_auto
  ihave HI : iprop(∃ (y : GoInterfaceOk) (l' : List CtxLink),
      "c" ∷ c_ptr ↦ (interface.ok y : GoInterface) ∗ "#Hch" ∷ ctxChain k R y l') $$ [c]
  · iexists x, l; iframe; iexact Hch
  wp_for HI
  cases l' with
  | nil =>
    iunfold ctxChain at Hch
    icases Hch with (%hroot | ⟨%hty, #Hspec⟩)
    · obtain ⟨hy | hy, hR⟩ := hroot <;> subst hy
      · wp_auto
        wp_for_post
        iapply HΦ; ipureintro; exact hR
      · wp_auto
        wp_for_post
        iapply HΦ; ipureintro; exact hR
    · simp only [valueSpecialTypes, List.mem_cons, List.not_mem_nil, not_or] at hty
      obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := hty
      repeat (first | wp_auto | simp only [h1, h2, h3, h4, h5, h6, decide_false, ↓reduceIte])
      wp_bind (App (Val #(methods y.ty go!"Value" y.v)) (Val #k))
      iapply Hspec
      inext
      iintro %v %hv
      wp_auto
      wp_for_post
      iapply HΦ; ipureintro; exact hv
  | cons a l' =>
    cases a with
    | cancel cc =>
      iunfold ctxChain at Hch
      icases Hch with ⟨%hyk, %p, #Hf, #Hp⟩
      obtain ⟨hy, hk⟩ := hyk
      subst hy
      wp_auto
      cases k with
      | nil =>
        wp_auto
        wp_for_post
        iframe; iexists p, l'; iframe; iexact Hp
      | ok ki =>
        have hne := hk ki rfl
        simp only [hne, ↓reduceIte]
        wp_auto
        wp_for_post
        iframe; iexists p, l'; iframe; iexact Hp
    | timer cc =>
      iunfold ctxChain at Hch
      icases Hch with ⟨%hyk, %p, #Hf, #Hp⟩
      obtain ⟨hy, hk⟩ := hyk
      subst hy
      wp_auto
      cases k with
      | nil =>
        wp_auto
        wp_for_post
        iframe; iexists p, l'; iframe; iexact Hp
      | ok ki =>
        have hne := hk ki rfl
        simp only [hne, ↓reduceIte]
        wp_auto
        wp_for_post
        iframe; iexists p, l'; iframe; iexact Hp
    | valCtx q key val =>
      iunfold ctxChain at Hch
      icases Hch with ⟨%hy, %p, #Hf, #Hk, #Hv, #Heq, #Hrest⟩
      subst hy
      iunfold keyEqOk at Heq
      wp_auto
      by_cases hkk : k = key
      · subst hkk
        simp only [↓reduceIte]
        cases k with
        | nil =>
          wp_auto
          wp_for_post
          iapply HΦ; iexact Hrest
        | ok ki =>
          simp only [↓reduceIte]
          wp_bind gl(CheckComparable ki.ty ;; GoOp GoEquals ki.ty glv((ki.v, ki.v)))
          iapply Heq $$ %ki %ki
          · ipureintro; exact ⟨Or.inl ⟨rfl, rfl⟩, rfl⟩
          wp_auto
          wp_for_post
          iapply HΦ; iexact Hrest
      · simp only [hkk, ↓reduceIte]
        have hfalse : ∀ ki kk : GoInterfaceOk, k = GoInterface.ok ki → key = GoInterface.ok kk →
            ki.ty = kk.ty → ki.v ≠ kk.v := by
          intro ki kk h1 h2 h3 h4
          apply hkk; subst h1 h2; cases ki; cases kk; simp_all
        cases k with
        | nil =>
          cases key with
          | nil => exact absurd rfl hkk
          | ok kk =>
            wp_auto
            wp_for_post
            iframe; iexists p, l'; iframe; iexact Hrest
        | ok ki =>
          cases key with
          | nil =>
            wp_auto
            wp_for_post
            iframe; iexists p, l'; iframe; iexact Hrest
          | ok kk =>
            by_cases hty : ki.ty = kk.ty
            · simp only []; rw [if_pos hty]
              wp_bind gl(CheckComparable ki.ty ;; GoOp GoEquals ki.ty glv((ki.v, kk.v)))
              iapply Heq $$ %ki %kk
              · ipureintro; exact ⟨Or.inl ⟨rfl, rfl⟩, hty⟩
              rw [decide_eq_false (hfalse ki kk rfl rfl hty)]
              wp_auto
              wp_for_post
              iframe; iexists p, l'; iframe; iexact Hrest
            · simp only [hty, ↓reduceIte]
              wp_auto
              wp_for_post
              iframe; iexists p, l'; iframe; iexact Hrest

theorem ctxChain_Value (k : GoInterface) (R : GoInterface → Prop) (l : List CtxLink)
    (x : GoInterfaceOk) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ ctxChain k R x l }}
      (App (Val #(methods x.ty go!"Value" x.v)) (Val #k))
    {{ (w : GoInterface), RET #w; ⌜R w⌝ }} := by
  iintro %Φ ⟨#Hpkg, #Hch⟩ HΦ
  cases l with
  | nil =>
    iunfold ctxChain at Hch
    icases Hch with (%hroot | ⟨%hty, #Hspec⟩)
    · obtain ⟨hy | hy, hR⟩ := hroot <;> subst hy
      · wp_method_call
        wp_auto
        wp_method_call
        wp_auto
        iapply HΦ; ipureintro; exact hR
      · wp_method_call
        wp_auto
        wp_method_call
        wp_auto
        iapply HΦ; ipureintro; exact hR
    · iapply Hspec
      inext
      iexact HΦ
  | cons a l =>
    cases a with
    | cancel cc =>
      iunfold ctxChain at Hch
      icases Hch with ⟨%hyk, %p, #Hf, #Hp⟩
      obtain ⟨hy, hk⟩ := hyk
      subst hy
      wp_method_call
      wp_auto
      cases k with
      | nil =>
        wp_auto
        wp_apply wp_value_chain _ R l p $$ [Hp] as %w %hw
        · iframe #
        iapply HΦ; ipureintro; exact hw
      | ok ki =>
        have hne := hk ki rfl
        simp only [hne, ↓reduceIte]
        wp_auto
        wp_apply wp_value_chain _ R l p $$ [Hp] as %w %hw
        · iframe #
        iapply HΦ; ipureintro; exact hw
    | timer cc =>
      iunfold ctxChain at Hch
      icases Hch with ⟨%hyk, %p, #Hf, #Hp⟩
      obtain ⟨hy, hk⟩ := hyk
      subst hy
      wp_method_call
      wp_auto
      wp_method_call
      wp_auto
      cases k with
      | nil =>
        wp_auto
        wp_apply wp_value_chain _ R l p $$ [Hp] as %w %hw
        · iframe #
        iapply HΦ; ipureintro; exact hw
      | ok ki =>
        have hne := hk ki rfl
        simp only [hne, ↓reduceIte]
        wp_auto
        wp_apply wp_value_chain _ R l p $$ [Hp] as %w %hw
        · iframe #
        iapply HΦ; ipureintro; exact hw
    | valCtx q key val =>
      iunfold ctxChain at Hch
      icases Hch with ⟨%hy, %p, #Hf, #Hk, #Hv, #Heq, #Hrest⟩
      subst hy
      iunfold keyEqOk at Heq
      wp_method_call
      wp_auto
      by_cases hkk : k = key
      · subst hkk
        simp only [↓reduceIte]
        cases k with
        | nil =>
          wp_auto
          iapply HΦ; iexact Hrest
        | ok ki =>
          simp only [↓reduceIte]
          wp_bind gl(CheckComparable ki.ty ;; GoOp GoEquals ki.ty glv((ki.v, ki.v)))
          iapply Heq $$ %ki %ki
          · ipureintro; exact ⟨Or.inl ⟨rfl, rfl⟩, rfl⟩
          wp_auto
          iapply HΦ; iexact Hrest
      · simp only [hkk, ↓reduceIte]
        have hfalse : ∀ ki kk : GoInterfaceOk, k = GoInterface.ok ki → key = GoInterface.ok kk →
            ki.ty = kk.ty → kk.v ≠ ki.v := by
          intro ki kk h1 h2 h3 h4
          apply hkk; subst h1 h2; cases ki; cases kk; simp_all
        cases k with
        | nil =>
          cases key with
          | nil => exact absurd rfl hkk
          | ok kk =>
            wp_auto
            wp_apply wp_value_chain _ R l p $$ [Hrest] as %w %hw
            · iframe #
            iapply HΦ; ipureintro; exact hw
        | ok ki =>
          cases key with
          | nil =>
            wp_auto
            wp_apply wp_value_chain _ R l p $$ [Hrest] as %w %hw
            · iframe #
            iapply HΦ; ipureintro; exact hw
          | ok kk =>
            by_cases hty : kk.ty = ki.ty
            · simp only []; rw [if_pos hty]
              wp_bind gl(CheckComparable kk.ty ;; GoOp GoEquals kk.ty glv((kk.v, ki.v)))
              iapply Heq $$ %kk %ki
              · ipureintro; exact ⟨Or.inr ⟨rfl, rfl⟩, hty⟩
              rw [decide_eq_false (hfalse ki kk rfl rfl hty.symm)]
              wp_auto
              wp_apply wp_value_chain _ R l p $$ [Hrest] as %w %hw
              · iframe #
              iapply HΦ; ipureintro; exact hw
            · simp only [hty, ↓reduceIte]
              wp_auto
              wp_apply wp_value_chain _ R l p $$ [Hrest] as %w %hw
              · iframe #
              iapply HΦ; ipureintro; exact hw

/-- **`value(x, k)` of a context with `ctxValue x k R`.** -/
theorem wp_value (x : GoInterfaceOk) (k : GoInterface) (R : GoInterface → Prop) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ ctxValue x k R }}
      (App (App (Val (@! context.value)) (Val #(interface.ok x))) (Val #k))
    {{ (w : GoInterface), RET #w; ⌜R w⌝ }} := by
  iintro %Φ ⟨#Hpkg, #Hv⟩ HΦ
  iunfold ctxValue at Hv
  icases Hv with ⟨%l, #Hch⟩
  iapply wp_value_chain k R l x $$ [] HΦ
  iframe #

/-- **`x.Value(k)` of a context with `ctxValue x k R`.** -/
theorem ctxValue_Value (x : GoInterfaceOk) (k : GoInterface) (R : GoInterface → Prop) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ ctxValue x k R }}
      (App (Val #(methods x.ty go!"Value" x.v)) (Val #k))
    {{ (w : GoInterface), RET #w; ⌜R w⌝ }} := by
  iintro %Φ ⟨#Hpkg, #Hv⟩ HΦ
  iunfold ctxValue at Hv
  icases Hv with ⟨%l, #Hch⟩
  iapply ctxChain_Value k R l x $$ [] HΦ
  iframe #

theorem ctxChain_mono (k : GoInterface) (R R' : GoInterface → Prop) (h : ∀ v, R v → R' v)
    (l : List CtxLink) (x : GoInterfaceOk) :
    ctxChain (GF := GF) k R x l ⊢ ctxChain k R' x l := by
  induction l generalizing x with
  | nil =>
    simp only [ctxChain]
    iintro (%hr | ⟨%hty, #Hs⟩)
    · ileft; ipureintro; exact ⟨hr.1, h _ hr.2⟩
    · iright; iframe %hty
      imodintro
      iintro %Φ HΦ
      iapply Hs
      inext
      iintro %v %hv
      iapply HΦ; ipureintro; exact h v hv
  | cons a l ih =>
    cases a with
    | cancel c =>
      simp only [ctxChain]
      iintro ⟨%hx, %p, #Hf, Hp⟩
      iframe %hx
      iexists p; iframe #; iapply ih; iexact Hp
    | timer c =>
      simp only [ctxChain]
      iintro ⟨%hx, %p, #Hf, Hp⟩
      iframe %hx
      iexists p; iframe #; iapply ih; iexact Hp
    | valCtx q key val =>
      simp only [ctxChain]
      iintro ⟨%hx, %p, #Hf, #Hk, #Hv, #He, Hr⟩
      iframe %hx
      iexists p; iframe #
      by_cases hkk : k = key
      · simp only [hkk, ↓reduceIte]
        icases Hr with %hr
        ipureintro; exact h _ hr
      · simp only [hkk, ↓reduceIte]
        iapply ih; iexact Hr

theorem ctxValue_mono (x : GoInterfaceOk) (k : GoInterface) (R R' : GoInterface → Prop)
    (h : ∀ v, R v → R' v) : ctxValue (GF := GF) x k R ⊢ ctxValue x k R' := by
  unfold ctxValue
  iintro ⟨%l, Hch⟩
  iexists l
  iapply ctxChain_mono k R R' h l x
  iexact Hch

/-- **L1: `Background()` answers `nil` at every key.** -/
theorem ctxValue_background (k : GoInterface) :
    ⊢ ctxValue (GF := GF) backgroundCtxVal k (· = interface.nil) := by
  unfold ctxValue
  iexists []
  simp only [ctxChain]
  ileft; ipureintro; simp

/-- **L1: `TODO()` answers `nil` at every key.** -/
theorem ctxValue_todo (k : GoInterface) :
    ⊢ ctxValue (GF := GF) todoCtxVal k (· = interface.nil) := by
  unfold ctxValue
  iexists []
  simp only [ctxChain]
  ileft; ipureintro; simp

/-- **L2: a `*cancelCtx` answers a key that is not a `*int` as its parent does.** -/
theorem ctxValue_cancel (c : Loc) (p : GoInterfaceOk) (k : GoInterface) (R : GoInterface → Prop)
    (hk : notIntPtrKey k) :
    ctxField c ↦□ (interface.ok p : GoInterface) ∗ ctxValue (GF := GF) p k R ⊢
      ctxValue (interface.mk (go.GoType.PointerType cancelCtx.ty) #c) k R := by
  unfold ctxValue
  iintro ⟨#Hf, %l, #Hch⟩
  iexists (CtxLink.cancel c :: l)
  simp only [ctxChain]
  isplitr
  · ipureintro; simp [hk]
  iexists p; iframe #

/-- **L3: a `*timerCtx` answers a key that is not a `*int` as its parent does.** -/
theorem ctxValue_timer (c : Loc) (p : GoInterfaceOk) (k : GoInterface) (R : GoInterface → Prop)
    (hk : notIntPtrKey k) :
    ctxField (tcc c) ↦□ (interface.ok p : GoInterface) ∗ ctxValue (GF := GF) p k R ⊢
      ctxValue (interface.mk (go.GoType.PointerType timerCtx.ty) #c) k R := by
  unfold ctxValue
  iintro ⟨#Hf, %l, #Hch⟩
  iexists (CtxLink.timer c :: l)
  simp only [ctxChain]
  isplitr
  · ipureintro; simp [hk]
  iexists p; iframe #

/-- **L4: a `*valueCtx` answers its key with its value, and another key as its parent does.** -/
theorem ctxValue_valueCtx (q : Loc) (p : GoInterfaceOk) (key val k : GoInterface)
    (R : GoInterface → Prop) :
    vctxField q ↦□ (interface.ok p : GoInterface) ∗
      structFieldRef context.valueCtx go!"key" q ↦□ key ∗
      structFieldRef context.valueCtx go!"val" q ↦□ val ∗ keyEqOk (GF := GF) k key ∗
      (if k = key then iprop(⌜R val⌝) else ctxValue p k R) ⊢
      ctxValue (interface.mk (go.GoType.PointerType valueCtx.ty) #q) k R := by
  iintro ⟨#Hf, #Hk, #Hv, #Heq, Hr⟩
  by_cases h : k = key
  · simp only [h, ↓reduceIte]
    icases Hr with %hR
    unfold ctxValue
    iexists [CtxLink.valCtx q key val]
    simp only [ctxChain]
    simp only [↓reduceIte]
    isplitr
    · ipureintro; trivial
    iexists p; iframe #; ipureintro; exact hR
  · simp only [h, ↓reduceIte]
    unfold ctxValue
    icases Hr with ⟨%l, #Hch⟩
    iexists (CtxLink.valCtx q key val :: l)
    simp only [ctxChain]
    simp only [h, ↓reduceIte]
    isplitr
    · ipureintro; trivial
    iexists p; iframe #

/-- **L5: a context of another type answers as its own `Value` spec says.** -/
theorem ctxValue_other (x : GoInterfaceOk) (k : GoInterface) (R : GoInterface → Prop)
    (hty : x.ty ∉ valueSpecialTypes) :
    (□ ∀ Φ : val → IProp GF, ▷ (∀ v : GoInterface, ⌜R v⌝ -∗ Φ #v) -∗
        WP (App (Val #(methods x.ty go!"Value" x.v)) (Val #k)) {{ Φ }}) ⊢
      ctxValue x k R := by
  iintro #Hs
  unfold ctxValue
  iexists []
  simp only [ctxChain]
  iright
  iframe #
  ipureintro; exact hty

/-- A `*cancelCtx` with parent `p` answers as `p` does. -/
theorem ctxValueFrom_cancel (c : Loc) (p : GoInterfaceOk) :
    ctxField c ↦□ (interface.ok p : GoInterface) ⊢
      ctxValueFrom (GF := GF) p (interface.mk (go.GoType.PointerType cancelCtx.ty) #c) := by
  iintro #Hf
  unfold ctxValueFrom
  imodintro
  iintro %k %R %hk Hv
  iapply ctxValue_cancel c p k R hk
  iframe #; iexact Hv

/-- A `*timerCtx` with parent `p` answers as `p` does. -/
theorem ctxValueFrom_timer (c : Loc) (p : GoInterfaceOk) :
    ctxField (tcc c) ↦□ (interface.ok p : GoInterface) ⊢
      ctxValueFrom (GF := GF) p (interface.mk (go.GoType.PointerType timerCtx.ty) #c) := by
  iintro #Hf
  unfold ctxValueFrom
  imodintro
  iintro %k %R %hk Hv
  iapply ctxValue_timer c p k R hk
  iframe #; iexact Hv

end proofs

end context

end Perennial
