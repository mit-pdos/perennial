From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth.
From Perennial.goose_lang Require Import lang.
From Perennial.program_logic Require Import recovery_weakestpre dist_weakestpre.
From Perennial.goose_lang Require Import crash_modality adequacy lang lifting recovery_lifting.
Set Default Proof Using "Type".

Section wpd_definitions.

Context `{ffi_sem: ffi_semantics}.
Context `{interp: !ffi_interp ffi}.
Context `{@ffi_interp_adequacy ffi interp ext ffi_sem}.
Context {go_gctx : GoGlobalContext}.

Definition wpd `{hG: !gooseGlobalGS Σ} (E: coPset) (ers: list node_init_cfg) :=
  ([∗ list] i↦σ ∈ ers, ∀ `(hG: !gooseLocalGS Σ),
    ffi_local_start (goose_ffiLocalGS) σ.(init_local_state).(world) -∗
    own_go_state σ.(init_local_state).(go_state).(package_state) ={E}=∗
    ∃ Φ Φrx Φinv, wpr NotStuck E σ.(init_thread) σ.(init_restart) Φ Φinv Φrx)%I.

Lemma wpd_compose `{hG: !gooseGlobalGS Σ} E ers1 ers2 :
  wpd E ers1 -∗
  wpd E ers2 -∗
  wpd E (ers1 ++ ers2).
Proof. rewrite /wpd big_sepL_app. iIntros "$ $". Qed.

End wpd_definitions.
