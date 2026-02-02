Require Export New.generatedproof.go_etcd_io.etcd.pkg.v3.wait.
Require Export New.proof.proof_prelude.
From New.proof Require Import log sync.
From New.proof.github_com.goose_lang.goose.model.channel
  Require Import logatom.chan_au_base idiom.handoff.handoff.

Class waitG `{ffi_syntax} Σ :=
  {
    #[local] wait_chanG :: chanG Σ any.t;
  }.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : wait.Assumptions}.
Context `{!waitG Σ}.
Local Set Default Proof Using "All".

#[global] Instance : IsPkgInit (iProp Σ) wait := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) wait := build_get_is_pkg_init_wf.

Record wait_params :=
  {
    I : iProp Σ;
    own_unregistered_id : w64 → iProp Σ;
  }.

Local Notation interface_call i m := #(methods i.(interface.ty) m i.(interface.v)).

(* This is non-duplicable so that ownership of the internal [I] can rule out
   overflow. This also permits non-concurrent implementations. *)
Definition own_Wait γ w R : iProp Σ :=
    "HI" ∷ I γ ∗
    "#Register" ∷
      (∀ (id' : w64),
         {{{ I γ ∗ own_unregistered_id γ id' }}}
           interface_call w "Register" #id'
         {{{ ch, RET #ch;
             I γ ∗
             (∀ Φ, (∀ v, R id' v -∗ Φ v true) -∗ recv_au ch any.t Φ)
         }}}) ∗
    "#Trigger" ∷
      (∀ (id' : w64) (x : interface.t),
         {{{ I γ ∗ R id' x }}}
           interface_call w "Trigger" #id' #x
         {{{ RET #(); I γ }}}
      ) ∗
    "#IsRegistered" ∷
      (∀ (id' : w64),
         {{{ I γ }}}
           interface_call w "IsRegistered" #id'
         {{{ (reg : bool), RET #reg; I γ }}}
      ).
#[global] Opaque own_Wait.
#[local] Transparent own_Wait.

Lemma wp_Wait__Register γ w (id' : w64) R :
  {{{ is_pkg_init wait ∗ own_Wait γ w R ∗ own_unregistered_id γ id' }}}
    interface_call w "Register" #id'
  {{{ ch, RET #ch;
      own_Wait γ w R ∗
      (∀ Φ, (∀ v, R id' v -∗ Φ v true) -∗ recv_au ch any.t Φ)
  }}}.
Proof.
  wp_start as "[Hw Hid]". iNamed "Hw".
  iApply ("Register" with "[$]"). iIntros "!> * [I post]". iApply "HΦ". iFrame "∗#".
Qed.

Lemma wp_Wait__Trigger γ w (id' : w64) (x : interface.t) R :
  {{{ is_pkg_init wait ∗ own_Wait γ w R ∗ R id' x }}}
    interface_call w "Trigger" #id' #x
  {{{ RET #(); own_Wait γ w R }}}.
Proof.
  wp_start as "[Hw HR]". iNamed "Hw".
  iApply ("Trigger" with "[$]"). iIntros "!> * I". iApply "HΦ". iFrame "∗#".
Qed.

Lemma wp_Wait__IsRegistered γ w (id' : w64) R :
  {{{ is_pkg_init wait ∗ own_Wait γ w R }}}
    interface_call w "IsRegistered" #id'
  {{{ (reg : bool), RET #reg; own_Wait γ w R }}}.
Proof.
  wp_start as "Hw". iNamed "Hw".
  iApply ("IsRegistered" with "[$]"). iIntros "!> * I". iApply "HΦ". iFrame "∗#".
Qed.

End wps.
