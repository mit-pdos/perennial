/-
Port of `new/proof/go_etcd_io/etcd/pkg/v3/wait.v`.

Lean notes:
* Rocq's nested Texan triples inside `ownWait` (iProps) are written out as
  `□ ∀ Φ, P -∗ ▷ (∀ x, Q -∗ Φ v) -∗ WP e {{ Φ }}`.
* Rocq's `recvAu γch any.t Φ` is `recvAu γch interface.t Φ` (`any.t` is an
  abbreviation of `interface.t`).
-/
import Perennial.Proof.ProofPrelude
import Perennial.Code.go_etcd_io.etcd.pkg.v3.wait
import Perennial.GeneratedProof.go_etcd_io.etcd.pkg.v3.wait
import Perennial.Proof.log
import Perennial.Proof.sync
import Perennial.Golang.Theory.Chan
import Perennial.Golang.Theory.Chan.Idioms.Bag

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace go_etcd_io.etcd.pkg.v3.wait

/-- Rocq `interfaceCall i m`. -/
abbrev interfaceCall [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions] (i : interface.t_ok)
    (m : GoString) : val :=
  #(methods i.ty m i.v)

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : wait.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.wait :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.wait :=
  build_get_is_pkg_init_wf

end init

structure WaitParams (GF : BundledGFunctors) where
  I : IProp GF
  ownUnregisteredId : w64 → IProp GF

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : wait.Assumptions]

local notation "pkg" => pkg_id.go_etcd_io.etcd.pkg.v3.wait


/-- This is non-duplicable so that ownership of the internal `I` can rule out
overflow. This also permits non-concurrent implementations. -/
def ownWaitDef (γ : WaitParams GF) (w : interface.t_ok) (R : w64 → interface.t → IProp GF) :
    IProp GF :=
  iprop(
    "HI" ∷ γ.I ∗
    "#Register" ∷
      (∀ (id' : w64), □ (∀ Φ : val → IProp GF,
        (γ.I ∗ γ.ownUnregisteredId id') -∗
        ▷ (∀ (ch : Loc) (γch : ChanNames),
            (γ.I ∗ isChan ch γch interface.t ∗
              (∀ Φ' : interface.t → Bool → IProp GF,
                (∀ v, R id' v -∗ Φ' v true) -∗ recvAu γch interface.t Φ')) -∗ Φ #ch) -∗
        WP (App (Val (interfaceCall w go!"Register")) (Val #id')) {{ Φ }})) ∗
    "#Trigger" ∷
      (∀ (id' : w64) (x : interface.t), □ (∀ Φ : val → IProp GF,
        (γ.I ∗ R id' x) -∗
        ▷ (γ.I -∗ Φ #()) -∗
        WP (App (App (Val (interfaceCall w go!"Trigger")) (Val #id')) (Val #x)) {{ Φ }})) ∗
    "#IsRegistered" ∷
      (∀ (id' : w64), □ (∀ Φ : val → IProp GF,
        γ.I -∗
        ▷ (∀ reg : Bool, γ.I -∗ Φ #reg) -∗
        WP (App (Val (interfaceCall w go!"IsRegistered")) (Val #id')) {{ Φ }})))
/-- (Rocq: `Opaque ownWait`) -/
@[irreducible] def ownWait (γ : WaitParams GF) (w : interface.t_ok)
    (R : w64 → interface.t → IProp GF) : IProp GF := ownWaitDef γ w R
theorem ownWait_unseal : @ownWait = @ownWaitDef := by funext; with_unfolding_all rfl

theorem Wait.wp_Register (γ : WaitParams GF) (w : interface.t_ok) (id' : w64)
    (R : w64 → interface.t → IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ ownWait γ w R ∗ γ.ownUnregisteredId id' }}
      (App (Val (interfaceCall w go!"Register")) (Val #id'))
    {{ (ch : Loc) (γch : ChanNames), RET #ch;
        isChan ch γch interface.t ∗
        ownWait γ w R ∗
        (∀ Φ' : interface.t → Bool → IProp GF,
          (∀ v, R id' v -∗ Φ' v true) -∗ recvAu γch interface.t Φ') }} := by
  iintro %Φ ⟨-, Hw, Hid⟩ HΦ
  rw [ownWait_unseal]
  iNamed Hw
  iapply Register $$ %id' %Φ [HI Hid]
  · iframe
  inext
  iintro %ch %γch ⟨HI, #Hch, Hpost⟩
  iapply HΦ
  unfold ownWaitDef
  iframe # ∗

theorem Wait.wp_Trigger (γ : WaitParams GF) (w : interface.t_ok) (id' : w64) (x : interface.t)
    (R : w64 → interface.t → IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ ownWait γ w R ∗ R id' x }}
      (App (App (Val (interfaceCall w go!"Trigger")) (Val #id')) (Val #x))
    {{ RET #(); ownWait γ w R }} := by
  iintro %Φ ⟨-, Hw, HR⟩ HΦ
  rw [ownWait_unseal]
  iNamed Hw
  iapply Trigger $$ %id' %x %Φ [HI HR]
  · iframe
  inext
  iintro HI
  iapply HΦ
  unfold ownWaitDef
  iframe # ∗

theorem Wait.wp_IsRegistered (γ : WaitParams GF) (w : interface.t_ok) (id' : w64)
    (R : w64 → interface.t → IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ ownWait γ w R }}
      (App (Val (interfaceCall w go!"IsRegistered")) (Val #id'))
    {{ (reg : Bool), RET #reg; ownWait γ w R }} := by
  iintro %Φ ⟨-, Hw⟩ HΦ
  rw [ownWait_unseal]
  iNamed Hw
  iapply IsRegistered $$ %id' %Φ HI
  inext
  iintro %reg HI
  iapply HΦ
  unfold ownWaitDef
  iframe # ∗

end wps

end go_etcd_io.etcd.pkg.v3.wait

end Perennial
end
