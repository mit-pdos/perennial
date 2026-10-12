/-
Package initialization of `context` (`wp_initialize'`).

The initializer allocates the package's variables, initializes `errors`, `sync`,
`sync/atomic` and `time`, sets `Canceled = errors.New("context canceled")`,
`DeadlineExceeded = deadlineExceededError{}` and `closedchan = make(chan struct{})`, and runs
`init()`, which closes `closedchan`. It establishes `isInit` (the `goroutines` counter in an
invariant, the fixed `closedchan` and `Canceled`).

Two premises are not facts of the model: `Canceled`'s dynamic type (`*errors.errorString`)
and `DeadlineExceeded`'s (`deadlineExceededError`) are in the type set of `error`
(`isTypedErr`). These are method-set facts (both types have `Error() string`), and method sets
are uninterpreted in the semantics (`methodSet` is a parameter of `GoSemanticsFunctions` that no
assumption constrains), so they are the classes `ErrorStringIsError` and
`DeadlineExceededIsError`, assumptions about the semantics like the packages' `Assumptions`.
-/
module

public import Perennial.Proof.context

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace context

/-- `*errors.errorString` is in the type set of `error` (it has the method `Error() string`):
a fact about the method sets, which the semantics leaves uninterpreted. -/
class ErrorStringIsError [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions] : Prop where
  is_error : go.typeSetContains (go.GoType.PointerType errors.errorString.ty) go.error = true

/-- `context.deadlineExceededError` is in the type set of `error` (it has the method
`Error() string`): a fact about the method sets, which the semantics leaves uninterpreted. -/
class DeadlineExceededIsError [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions] : Prop where
  is_error : go.typeSetContains context.deadlineExceededError.ty go.error = true

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]
variable [hErr : ErrorStringIsError]
variable [hDE : DeadlineExceededIsError]

/-- `errors.New(msg)`, with the exact type of what it returns (`errors.wp_New_ptr` keeps the
pointer type abstract; `isTypedErr` needs `*errorString`): a pointer to an `errorString`
converted to `error` (a caller that compares a non-`nil` error against it needs its
dynamic type to be comparable, which a pointer type is). -/
theorem wp_New_errorString (msg : GoString) :
    {{ (True : IProp GF) }}
      (App (Val (@! errors.New)) (Val #msg))
    {{ (x : Loc), RET #(interface.mkOk (go.GoType.PointerType errors.errorString.ty) #x);
        □ ∀ Φ : val → IProp GF, ▷ Φ #msg -∗
          WP (App (Val #(methods (go.GoType.PointerType errors.errorString.ty) go!"Error" #x))
            (Val #())) {{ Φ }} }} := by
  wp_start
  wp_auto
  wp_alloc x as Hx
  iStructNamed Hx
  ipersist s
  wp_auto
  iapply HΦ
  imodintro
  iintro %Φ HΦ
  rw [method_unfold]
  wp_auto
  iexact HΦ

theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.context get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.context }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := GoChan) closedchan _ as Hcl
  wp_apply wp_GlobalAlloc (V := w64) cancelCtxKey go.int as _
  wp_apply wp_GlobalAlloc (V := sync.atomic.Int32) goroutines sync.atomic.Int32.ty as Hgo
  wp_apply wp_GlobalAlloc (V := GoInterface) DeadlineExceeded go.error as HDE
  wp_apply wp_GlobalAlloc (V := GoInterface) Canceled go.error as HC
  wp_apply time.wp_initialize' _ Hinit.2.2.2.2.1 $$ Hown as ⟨Hown, #H1⟩
  wp_apply sync.atomic.wp_initialize' _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #H2⟩
  wp_apply sync.wp_initialize' _ Hinit.2.2.1 $$ Hown as ⟨Hown, #H3⟩
  wp_apply errors.wp_initialize' _ Hinit.2.1 $$ Hown as ⟨Hown, #H4⟩
  wp_apply wp_New_errorString as %x _
  wp_apply chan.wp_make1 (V := Unit) as %ch %γ ⟨#His_ch, %Hcap, Hch⟩
  ipersist HC
  ipersist HDE
  ipersist Hcl
  ihave Hgo : sync.atomic.ownInt32 (globalAddr goroutines) (DFrac.own 1) (W32 0) $$ [Hgo]
  · rw [sync.atomic.ownInt32_unseal]
    unfold sync.atomic.ownInt32Def
    rw [show ({ _0' := zero_val _, v' := W32 0 } : sync.atomic.Int32) =
      zero_val sync.atomic.Int32 from rfl]
    iexact Hgo
  imod inv_alloc nroot ⊤ iprop(∃ g, sync.atomic.ownInt32 (globalAddr context.goroutines)
    (DFrac.own 1) g) $$ [Hgo] with #Hginv
  · inext
    iexists _
    iexact Hgo
  wp_apply_core chan.wp_close (V := Unit) ch γ $$ His_ch
  iintro -
  unfold closeAu
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists .Idle
  iframe Hch
  dsimp only
  iintro Hch
  imod Hmask with -
  imodintro
  wp_auto
  iframe Hown
  is_pkg_init_finish
  imodintro
  isplitr
  · iexact Hginv
  isplitr
  · iexists ch
    iexact Hcl
  isplitr
  · iexists _
    iframe HC
    ipureintro
    exact hErr.is_error
  isplitr
  · iexists _
    iframe HDE
    ipureintro
    exact hDE.is_error
  itrivial

end wps

end context

end Perennial
