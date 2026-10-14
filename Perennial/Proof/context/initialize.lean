/-
The proof of `context.initialize'`.
-/
module

public import Perennial.Spec.context.initialize
public import Perennial.Spec.time.initialize
public import Perennial.Spec.sync.atomic.initialize
public import Perennial.Spec.sync.initialize
public import Perennial.Spec.errors.initialize
public import Perennial.Proof.context.NewErrorString

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

theorem context.initialize'.wp_proof
    (wp_time_init : time.initialize'.spec (GF := GF) (hG := hG))
    (wp_atomic_init : sync.atomic.initialize'.spec (GF := GF) (hG := hG))
    (wp_sync_init : sync.initialize'.spec (GF := GF) (hG := hG))
    (wp_errors_init : errors.initialize'.spec (GF := GF) (hG := hG)) :
    context.initialize'.spec (GF := GF) (hG := hG) :=
  fun [hErr : ErrorStringIsError] [hDE : DeadlineExceededIsError] get_is_pkg_init Hinit => by
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
  wp_apply wp_time_init _ Hinit.2.2.2.2.1 $$ Hown as ⟨Hown, #H1⟩
  wp_apply wp_atomic_init _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #H2⟩
  wp_apply wp_sync_init _ Hinit.2.2.1 $$ Hown as ⟨Hown, #H3⟩
  wp_apply wp_errors_init _ Hinit.2.1 $$ Hown as ⟨Hown, #H4⟩
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
  wp_func_call
  wp_call
  wp_auto
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

end proof

end Perennial
