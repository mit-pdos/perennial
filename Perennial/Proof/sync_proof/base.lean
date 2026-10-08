/-
Common imports and package
initialization of `sync`.
-/
import Perennial.Code.sync
import Perennial.Proof.ProofPrelude
import Perennial.GeneratedProof.sync
import Perennial.Proof.sync.atomic
import Perennial.Proof.internal.race
import Perennial.Proof.internal.synctest
import Perennial.Proof.TokSet
import Perennial.Algebra.AuthProp

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

inductive rwmutex where
  | RLocked (num_readers : Nat)
  | Locked

inductive WlockState where
  | NotLocked (unnotified_readers : w32)
  | SignalingReaders (remaining_readers : w32)
  | WaitingForReaders
  | IsLocked

namespace sync

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.sync :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.sync :=
  build_get_is_pkg_init_wf

theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.sync get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.sync }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply internal.synctest.wp_initialize' _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #Hsynctest⟩
  wp_apply internal.race.wp_initialize' _ Hinit.2.2.1 $$ Hown as ⟨Hown, #Hrace⟩
  wp_apply sync.atomic.wp_initialize' _ Hinit.2.1 $$ Hown as ⟨Hown, #Hatomic⟩
  iframe Hown
  is_pkg_init_finish

end wps

end sync

end Perennial
end
