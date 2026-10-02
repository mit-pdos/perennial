/-
Port of `new/proof/go_etcd_io/etcd/pkg/v3/wait.v`.

Lean notes:
* Rocq's nested Texan triples inside `own_Wait` (iProps) are written out as
  `□ ∀ Φ, P -∗ ▷ (∀ x, Q -∗ Φ v) -∗ WP e {{ Φ }}`.
* The channel ghost state needs `Pos.Countable interface.t`; as in
  `channel_dsp.lean`, it is derived from an explicit `[Pos.Countable val]`
  assumption (Rocq gets `Countable val` from `ffi_syntax`).
* Rocq's `recv_au γch any.t Φ` is `recv_au γch interface.t Φ` (`any.t` is an
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

section countable
variable [ext : ffi_syntax]

instance interface_countable [val_countable : Pos.Countable val] : Pos.Countable interface.t :=
  .ofInjective (fun
      | .ok i => Pos.Countable.encode (val.InterfaceV (some (i.ty, i.v)))
      | .nil => Pos.Countable.encode (val.InterfaceV none))
    (by
      rintro (⟨⟨a, b⟩⟩ | _) (⟨⟨c, d⟩⟩ | _) h <;> have h := Pos.encode_inj h <;> simp_all)

/-- Rocq `interface_call i m`. -/
abbrev interface_call [GoGlobalContext] [GoSemanticsFunctions] (i : interface.t_ok) (m : go_string) : val :=
  #(methods i.ty m i.v)

end countable

section init
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : wait.Assumptions]

instance is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.wait :=
  define_is_pkg_init iprop(True)
instance get_is_pkg_init_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.wait :=
  build_get_is_pkg_init_wf

end init

structure wait_params (GF : BundledGFunctors) where
  I : IProp GF
  own_unregistered_id : w64 → IProp GF

section wps
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : heapGS HasLC.hasLC GF] [allG GF]
variable [sem : go.Semantics]
variable [package_sem : wait.Assumptions]
variable [val_countable : Pos.Countable val]

local notation "pkg" => pkg_id.go_etcd_io.etcd.pkg.v3.wait


/-- This is non-duplicable so that ownership of the internal `I` can rule out
overflow. This also permits non-concurrent implementations. -/
def own_Wait_def (γ : wait_params GF) (w : interface.t_ok) (R : w64 → interface.t → IProp GF) :
    IProp GF :=
  iprop(
    "HI" ∷ γ.I ∗
    "#Register" ∷
      (∀ (id' : w64), □ (∀ Φ : val → IProp GF,
        (γ.I ∗ γ.own_unregistered_id id') -∗
        ▷ (∀ (ch : loc) (γch : chan_names),
            (γ.I ∗ is_chan ch γch interface.t ∗
              (∀ Φ' : interface.t → Bool → IProp GF,
                (∀ v, R id' v -∗ Φ' v true) -∗ recv_au γch interface.t Φ')) -∗ Φ #ch) -∗
        WP (App (Val (interface_call w go!"Register")) (Val #id')) {{ Φ }})) ∗
    "#Trigger" ∷
      (∀ (id' : w64) (x : interface.t), □ (∀ Φ : val → IProp GF,
        (γ.I ∗ R id' x) -∗
        ▷ (γ.I -∗ Φ #()) -∗
        WP (App (App (Val (interface_call w go!"Trigger")) (Val #id')) (Val #x)) {{ Φ }})) ∗
    "#IsRegistered" ∷
      (∀ (id' : w64), □ (∀ Φ : val → IProp GF,
        γ.I -∗
        ▷ (∀ reg : Bool, γ.I -∗ Φ #reg) -∗
        WP (App (Val (interface_call w go!"IsRegistered")) (Val #id')) {{ Φ }})))
/-- (Rocq: `Opaque own_Wait`) -/
@[irreducible] def own_Wait (γ : wait_params GF) (w : interface.t_ok)
    (R : w64 → interface.t → IProp GF) : IProp GF := own_Wait_def γ w R
theorem own_Wait_unseal : @own_Wait = @own_Wait_def := by funext; with_unfolding_all rfl

theorem wp_Wait__Register (γ : wait_params GF) (w : interface.t_ok) (id' : w64)
    (R : w64 → interface.t → IProp GF) :
    {{ is_pkg_init (PROP := IProp GF) pkg ∗ own_Wait γ w R ∗ γ.own_unregistered_id id' }}
      (App (Val (interface_call w go!"Register")) (Val #id'))
    {{ (ch : loc) (γch : chan_names), RET #ch;
        is_chan ch γch interface.t ∗
        own_Wait γ w R ∗
        (∀ Φ' : interface.t → Bool → IProp GF,
          (∀ v, R id' v -∗ Φ' v true) -∗ recv_au γch interface.t Φ') }} := by
  iintro %Φ ⟨-, Hw, Hid⟩ HΦ
  rw [own_Wait_unseal]
  iNamed Hw
  iapply Register $$ %id' %Φ [HI Hid]
  · iframe
  inext
  iintro %ch %γch ⟨HI, #Hch, Hpost⟩
  iapply HΦ
  unfold own_Wait_def
  iframe # ∗

theorem wp_Wait__Trigger (γ : wait_params GF) (w : interface.t_ok) (id' : w64) (x : interface.t)
    (R : w64 → interface.t → IProp GF) :
    {{ is_pkg_init (PROP := IProp GF) pkg ∗ own_Wait γ w R ∗ R id' x }}
      (App (App (Val (interface_call w go!"Trigger")) (Val #id')) (Val #x))
    {{ RET #(); own_Wait γ w R }} := by
  iintro %Φ ⟨-, Hw, HR⟩ HΦ
  rw [own_Wait_unseal]
  iNamed Hw
  iapply Trigger $$ %id' %x %Φ [HI HR]
  · iframe
  inext
  iintro HI
  iapply HΦ
  unfold own_Wait_def
  iframe # ∗

theorem wp_Wait__IsRegistered (γ : wait_params GF) (w : interface.t_ok) (id' : w64)
    (R : w64 → interface.t → IProp GF) :
    {{ is_pkg_init (PROP := IProp GF) pkg ∗ own_Wait γ w R }}
      (App (Val (interface_call w go!"IsRegistered")) (Val #id'))
    {{ (reg : Bool), RET #reg; own_Wait γ w R }} := by
  iintro %Φ ⟨-, Hw⟩ HΦ
  rw [own_Wait_unseal]
  iNamed Hw
  iapply IsRegistered $$ %id' %Φ HI
  inext
  iintro %reg HI
  iapply HΦ
  unfold own_Wait_def
  iframe # ∗

end wps

end go_etcd_io.etcd.pkg.v3.wait

end Perennial
end
