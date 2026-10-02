/-
Port of `new/proof/github_com/mit_pdos/perennial/goose/testdata/examples/channel_dsp.v`:
examples of dependent separation protocols (DSP) over Go channels, and an MPMC muxer.

Lean notes / deviations:
* Countability. The channel ghost state needs `Pos.Countable V` for the element type.
  Rocq gets `Countable val`/`Countable func.t` from `ffi_syntax`, which requires
  `Countable ffi_val`; the Lean `ffi_syntax` has no such field and the port has no
  `Countable val` instance. The lemmas whose channels carry `interface.t` or `streamold.t`
  (which contains a `func.t`) therefore take `[Pos.Countable val]` as an explicit
  assumption, from which the instances for `func.t`, `interface.t` and `streamold.t` are
  derived.
* The Rocq `wp_send`/`wp_recv` tactics are not ported (`DspProofmode.lean` has the Texan
  triples `tac_wp_send`/`tac_wp_recv`). Below, `wp_dsp_send0/1/2`, `wp_dsp_recv0/1/2` are
  wrappers for messages with 0, 1 or 2 binders, whose messages are found by protocol
  normalization (`ProtoNormalize`).
* `solve_proto_contractive` is not ported; contractiveness is proved by hand, and
  `ProtoUnfold` instances are replaced by explicit unfolding equations (`*_unfold`).
-/
import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.channel_examples_init
import Perennial.Golang.Theory.Chan.Idioms.Mpmc
import Perennial.Golang.Theory.Chan.Idioms.Dsp.Dsp
import Perennial.Golang.Theory.Chan.Idioms.Dsp.DspProofmode

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

namespace github_com.mit_pdos.perennial.goose.testdata.examples.channel

/-! ## Countability -/

section countable
variable [ext : ffi_syntax] [val_countable : Pos.Countable val]

instance func_countable : Pos.Countable func.t :=
  .ofInjective (fun f => Pos.Countable.encode (val.RecV f.f f.x f.e))
    (by rintro ⟨a, b, c⟩ ⟨d, e, f⟩ h; have h := Pos.encode_inj h; simp_all)

instance interface_countable : Pos.Countable interface.t :=
  .ofInjective (fun
      | .ok i => Pos.Countable.encode (val.InterfaceV (some (i.ty, i.v)))
      | .nil => Pos.Countable.encode (val.InterfaceV none))
    (by
      rintro (⟨⟨a, b⟩⟩ | _) (⟨⟨c, d⟩⟩ | _) h <;> have h := Pos.encode_inj h <;> simp_all)

instance streamold_countable : Pos.Countable streamold.t :=
  .ofInjective (fun x => Pos.Countable.encode (x.req', x.res', x.f'))
    (by rintro ⟨a, b, c⟩ ⟨d, e, f⟩ h; have h := Pos.encode_inj h; simp_all)

end countable

/-! ## DSP send/receive wrappers -/

section dsp_wrappers
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : heapGS HasLC.hasLC GF] [allG GF]
variable [sem : go.Semantics]
variable {V : Type} [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V] {t : go.type}
  [IntoValTyped (GF := GF) V t]

theorem wp_dsp_recv0 (γ : dsp_names) (lr_chan rl_chan : loc) (p0 : iProto GF V) (v : V)
    (P : IProp GF) (p : iProto GF V) [ProtoNormalize false p0 [] (<?> iMsg_base v P p)] :
    {{ (lr_chan, rl_chan) ↣{γ} p0 }}
      (App (Val (chan.receive t)) (Val #rl_chan))
    {{ RET (PairV #v #true); ((lr_chan, rl_chan) ↣{γ} p) ∗ P }} := by
  iintro %Φ Hc HΦ
  wp_apply tac_wp_recv (TT := Tele.nil.{0}) γ lr_chan rl_chan p0 _ (ULift.up v) (ULift.up P)
    (ULift.up p) $$ Hc as %x H
  iapply HΦ $$ H

theorem wp_dsp_recv1 {A : Type} (γ : dsp_names) (lr_chan rl_chan : loc) (p0 : iProto GF V)
    (v : A → V) (P : A → IProp GF) (p : A → iProto GF V)
    [ProtoNormalize false p0 [] (<?> iMsg_exist fun a => iMsg_base (v a) (P a) (p a))] :
    {{ (lr_chan, rl_chan) ↣{γ} p0 }}
      (App (Val (chan.receive t)) (Val #rl_chan))
    {{ (a : A), RET (PairV #(v a) #true); ((lr_chan, rl_chan) ↣{γ} p a) ∗ P a }} := by
  iintro %Φ Hc HΦ
  wp_apply tac_wp_recv (TT := Tele.cons fun (_ : A) => Tele.nil) γ lr_chan rl_chan p0 _
    (fun a => ULift.up (v a)) (fun a => ULift.up (P a)) (fun a => ULift.up (p a)) $$ Hc
    as %x H
  obtain ⟨a, ⟨⟩⟩ := x
  iapply HΦ $$ H

theorem wp_dsp_recv2 {A B : Type} (γ : dsp_names) (lr_chan rl_chan : loc) (p0 : iProto GF V)
    (v : A → B → V) (P : A → B → IProp GF) (p : A → B → iProto GF V)
    [ProtoNormalize false p0 []
      (<?> iMsg_exist fun a => iMsg_exist fun b => iMsg_base (v a b) (P a b) (p a b))] :
    {{ (lr_chan, rl_chan) ↣{γ} p0 }}
      (App (Val (chan.receive t)) (Val #rl_chan))
    {{ (a : A) (b : B), RET (PairV #(v a b) #true); ((lr_chan, rl_chan) ↣{γ} p a b) ∗ P a b }} := by
  iintro %Φ Hc HΦ
  wp_apply tac_wp_recv (TT := Tele.cons fun (_ : A) => Tele.cons fun (_ : B) => Tele.nil)
    γ lr_chan rl_chan p0 _
    (fun a b => ULift.up (v a b)) (fun a b => ULift.up (P a b)) (fun a b => ULift.up (p a b))
    $$ Hc as %x H
  obtain ⟨a, b, ⟨⟩⟩ := x
  iapply HΦ $$ H

theorem wp_dsp_send0 (γ : dsp_names) (lr_chan rl_chan : loc) (p0 : iProto GF V) (v : V)
    (P : IProp GF) (p : iProto GF V) [ProtoNormalize false p0 [] (<!> iMsg_base v P p)] :
    {{ ((lr_chan, rl_chan) ↣{γ} p0) ∗ P }}
      (App (App (Val (chan.send t)) (Val #lr_chan)) (Val #v))
    {{ RET #(); (lr_chan, rl_chan) ↣{γ} p }} := by
  iintro %Φ H HΦ
  wp_apply tac_wp_send (TT := Tele.nil.{0}) Tele.Arg.nil γ lr_chan rl_chan p0 _ (ULift.up v)
    (ULift.up P) (ULift.up p) $$ H as H
  iapply HΦ $$ H

theorem wp_dsp_send1 {A : Type} (a : A) (γ : dsp_names) (lr_chan rl_chan : loc)
    (p0 : iProto GF V) (v : A → V) (P : A → IProp GF) (p : A → iProto GF V)
    [ProtoNormalize false p0 [] (<!> iMsg_exist fun a => iMsg_base (v a) (P a) (p a))] :
    {{ ((lr_chan, rl_chan) ↣{γ} p0) ∗ P a }}
      (App (App (Val (chan.send t)) (Val #lr_chan)) (Val #(v a)))
    {{ RET #(); (lr_chan, rl_chan) ↣{γ} p a }} := by
  iintro %Φ H HΦ
  wp_apply tac_wp_send (TT := Tele.cons fun (_ : A) => Tele.nil) (Tele.Arg.cons a Tele.Arg.nil)
    γ lr_chan rl_chan p0 _
    (fun a => ULift.up (v a)) (fun a => ULift.up (P a)) (fun a => ULift.up (p a)) $$ H as H
  iapply HΦ $$ H

theorem wp_dsp_send2 {A B : Type} (a : A) (b : B) (γ : dsp_names) (lr_chan rl_chan : loc)
    (p0 : iProto GF V) (v : A → B → V) (P : A → B → IProp GF) (p : A → B → iProto GF V)
    [ProtoNormalize false p0 []
      (<!> iMsg_exist fun a => iMsg_exist fun b => iMsg_base (v a b) (P a b) (p a b))] :
    {{ ((lr_chan, rl_chan) ↣{γ} p0) ∗ P a b }}
      (App (App (Val (chan.send t)) (Val #lr_chan)) (Val #(v a b)))
    {{ RET #(); (lr_chan, rl_chan) ↣{γ} p a b }} := by
  iintro %Φ H HΦ
  wp_apply tac_wp_send (TT := Tele.cons fun (_ : A) => Tele.cons fun (_ : B) => Tele.nil)
    (Tele.Arg.cons a (Tele.Arg.cons b Tele.Arg.nil)) γ lr_chan rl_chan p0 _
    (fun a b => ULift.up (v a b)) (fun a b => ULift.up (P a b)) (fun a b => ULift.up (p a b))
    $$ H as H
  iapply HΦ $$ H

end dsp_wrappers

/-! ## Examples -/

section proof
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : heapGS HasLC.hasLC GF] [allG GF]
variable [sem : go.Semantics] [package_sem : channel.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel

set_option goose.wp.extras true

section dsp_examples
variable [val_countable : Pos.Countable val]

def ref_prot : iProto GF interface.t :=
  <!> iMsg_exist fun (l : loc) => iMsg_exist fun (x : Int) =>
    iMsg_base (interface.mk_ok (go.type.PointerType go.int) #l) iprop(l ↦ W64 x)
      (<?> iMsg_base (interface.mk_ok (go.type.StructType []) #()) iprop(l ↦ (W64 x + W64 2)) END)

theorem wp_DSPExample :
    {{ is_pkg_init (PROP := IProp GF) pkg }}
      (App (Val (@! DSPExample)) (Val #()))
    {{ RET #(W64 42); True }} := by
  wp_start
  wp_auto
  wp_apply chan.wp_make1 (V := interface.t) as %c %γ ⟨#Hic, -, Hoc⟩
  wp_auto
  wp_apply chan.wp_make1 (V := interface.t) as %signal %γ' ⟨#Hicsignal, -, Hocsignal⟩
  wp_auto
  sorry

end dsp_examples

end proof

end github_com.mit_pdos.perennial.goose.testdata.examples.channel

end Perennial
