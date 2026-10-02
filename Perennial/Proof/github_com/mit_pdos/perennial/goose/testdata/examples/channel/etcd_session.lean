/-
Port of `new/proof/github_com/mit_pdos/perennial/goose/testdata/examples/channel/etcd_session.v`:
an etcd-style session monitor, using a broadcast channel (`sessionc`) that is
closed (and replaced) whenever the session expires.
-/
import Perennial.Proof.ProofPrelude
import Perennial.Proof.errors
import Perennial.Proof.time
import Perennial.Proof.sync_proof.mutex
import Perennial.Proof.github_com.goose_lang.primitive
import Perennial.Golang.Theory.Chan
import Perennial.Golang.Theory.Chan.Idioms.Bag
import Perennial.Golang.Theory.Chan.Idioms.Broadcast
import Perennial.GeneratedProof.github_com.mit_pdos.perennial.goose.testdata.examples.channel.etcd_session

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

namespace github_com.mit_pdos.perennial.goose.testdata.examples.channel.etcd_session

section wps
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : heapGS HasLC.hasLC GF] [allG GF]
variable [sem : go.Semantics] [package_sem : etcd_session.Assumptions]

local notation "pkg" =>
  pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel.etcd_session

/-- The resources protected by `mu`: half of `sessionc` and the current
broadcast channel. -/
abbrev mu_inv : IProp GF :=
  iprop(∃ (ch : chan.t) (γch : chan_names),
    "sessionc" ∷ typed_pointsto (global_addr sessionc) ch (DFrac.own (1 : Qp).half) ∗
    "#Hsessionc" ∷ own_broadcast_chan ch γch iprop(True) broadcast.t.Unknown ∗
    "#Hsessionc_is" ∷ is_chan ch γch Unit)

abbrev is_inv : IProp GF :=
  iprop("#Hmu" ∷ sync.is_Mutex (global_addr mu) mu_inv)

instance is_pkg_init_inst : IsPkgInit (IProp GF) pkg := define_is_pkg_init is_inv
instance get_is_pkg_init_wf_inst : GetIsPkgInitWf (IProp GF) pkg := build_get_is_pkg_init_wf

theorem is_inv_access : is_pkg_init (PROP := IProp GF) pkg ⊢ is_inv :=
  is_pkg_init_access (PROP := IProp GF) pkg

omit [allG GF] in
theorem pointsto_halves {V : Type} [TypedPointsto (GF := GF) V] (l : loc) (v : V) :
    typed_pointsto (GF := GF) l v (DFrac.own 1) ⊣⊢
      typed_pointsto l v (DFrac.own (1 : Qp).half) ∗ typed_pointsto l v (DFrac.own (1 : Qp).half) := by
  have h := (typed_pointsto_dfractional (GF := GF) l v).dfractional
    (DFrac.own (1 : Qp).half) (DFrac.own (1 : Qp).half)
  rwa [DFrac.op_own, Qp.half_add_half] at h

set_option goose.wp.extras true

set_option maxHeartbeats 400000 in
theorem wp_initialize' (get_is_pkg_init : go_string → IProp GF)
    (Hinit : get_is_pkg_init_prop pkg get_is_pkg_init) :
    {{ own_initializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); own_initializing get_is_pkg_init ∗ is_pkg_init (PROP := IProp GF) pkg }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  sorry -- TODO(port)

theorem wp_newSession :
    {{ (True : IProp GF) }}
      (App (Val (@! newSession)) (Val #()))
    {{ (err : error.t), RET #err; True }} := by
  wp_start
  wp_apply github_com.goose_lang.primitive.wp_RandomUint64 as %x _
  wp_if_destruct
  · wp_apply errors.wp_New as %_ _
    wp_end
  · wp_end

theorem wp_waitForSessionExpiration :
    {{ is_pkg_init (PROP := IProp GF) pkg }}
      (App (Val (@! waitForSessionExpiration)) (Val #()))
    {{ RET #(); True }} := by
  wp_start
  wp_end

/-- The postcondition of the nonblocking `select` in `monitorSession`. -/
abbrev monitor_select_post (v : val) : IProp GF :=
  iprop(⌜v = execute_val⌝ ∗
    ∃ (ch : chan.t) (γch : chan_names),
      "sessionc" ∷ typed_pointsto (global_addr sessionc) ch (DFrac.own 1) ∗
      "Hsessionc" ∷ own_broadcast_chan ch γch iprop(True) broadcast.t.Pending ∗
      "#Hsessionc_is" ∷ is_chan ch γch Unit)

set_option maxHeartbeats 1600000 in
theorem wp_monitorSession (ch : chan.t) (γch : chan_names) :
    {{ is_pkg_init (PROP := IProp GF) pkg ∗
        "sessionc" ∷ typed_pointsto (global_addr sessionc) ch (DFrac.own (1 : Qp).half) ∗
        "Hsessionc" ∷ own_broadcast_chan ch γch iprop(True) broadcast.t.Pending ∗
        "#Hsessionc_is" ∷ is_chan ch γch Unit }}
      (App (Val (@! monitorSession)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨sessionc, Hsessionc, #Hsessionc_is⟩
  ihave #Hpkg : is_pkg_init (PROP := IProp GF) pkg $$ []
  · iPkgInit
  ihave #Hinv := is_inv_access $$ Hpkg
  iNamed Hinv
  ihave HH : (∃ (ch : chan.t) (γch : chan_names) (cst : broadcast.t),
      "sessionc" ∷ typed_pointsto (global_addr sessionc) ch (DFrac.own (1 : Qp).half) ∗
      "Hsessionc" ∷ own_broadcast_chan ch γch iprop(True) cst ∗
      "#Hsessionc_is" ∷ is_chan ch γch Unit ∗
      "%Hcst" ∷ ⌜cst ≠ broadcast.t.Unknown⌝ : IProp GF) $$ [sessionc Hsessionc]
  · iexists ch, γch, broadcast.t.Pending
    iframe
    iframe #
    ipureintro; simp
  iclear Hsessionc_is
  wp_for HH
  wp_apply wp_waitForSessionExpiration
  wp_apply sync.wp_Mutex__Lock $$ [$Hmu] as ⟨Hlocked, Hown⟩
  icases Hown with ⟨%ch', %γch', sessionc_inv, #Hsessionc_inv, #Hsessionc_is_inv⟩
  icombine sessionc sessionc_inv gives %Heq
  subst Heq
  ihave sessionc := (pointsto_halves _ _).2 $$ [sessionc sessionc_inv]
  · iframe
  sorry -- TODO(port)

set_option maxHeartbeats 800000 in
/-- Rocq `waitSession` (renamed: the Lean name `waitSession` is the function). -/
theorem wp_waitSession {A' : Type} [ZeroVal A'] [TypedPointsto (GF := GF) A'] [Pos.Countable A']
    {A : go.type} [IntoValTyped (GF := GF) A' A]
    (cancel : loc) (γcancel : chan_names) (Pcancel : A' → IProp GF) :
    {{ is_pkg_init (PROP := IProp GF) pkg ∗ is_chan_bag γcancel cancel Pcancel }}
      (App (Val #(functions waitSession [A])) (Val #cancel))
    {{ (err : error.t), RET #err;
        match err with
        | interface.t.nil => iprop(True)
        | _ => iprop(∃ a, Pcancel a) }} := by
  wp_start as #Hcancel
  ihave #Hpkg : is_pkg_init (PROP := IProp GF) pkg $$ []
  · iPkgInit
  ihave #Hinv := is_inv_access $$ Hpkg
  iNamed Hinv
  wp_auto
  wp_apply sync.wp_Mutex__Lock $$ [$Hmu] as ⟨Hlocked, Hown⟩
  icases Hown with ⟨%ch, %γch, sessionc, #Hsessionc, #Hsessionc_is⟩
  wp_auto
  wp_apply sync.wp_Mutex__Unlock $$ [$Hmu $Hlocked sessionc]
  · inext; iexists ch, γch; iframe; iframe #
  wp_auto_lc 2
  sorry -- TODO(port)

end wps

end github_com.mit_pdos.perennial.goose.testdata.examples.channel.etcd_session

end Perennial
