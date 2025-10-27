Require Export New.generatedproof.go_etcd_io.etcd.pkg.v3.wait.
From New.golang.theory Require Import chan_old.
Require Export New.proof.proof_prelude.
From New.proof Require Import log sync.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.

#[global] Instance : IsPkgInit wait := define_is_pkg_init True%I.

Record wait_params :=
  {
    I : iProp Σ;
    own_unregistered_id : w64 → iProp Σ;
  }.
(* This is non-duplicable so that ownership of the internal [I] can rule out
   overflow. This also permits non-concurrent implementations. *)
Definition own_Wait γ (w : wait.Wait.t) R : iProp Σ :=
    "HI" ∷ I γ ∗
    "#Register" ∷
      (∀ (id' : w64),
         {{{ I γ ∗ own_unregistered_id γ id' }}}
           interface.get #"Register" #w #id'
         {{{ ch, RET #ch;
             I γ ∗
             |={⊤,∅}=>
               ∃ (st : chanstate.t interface.t),
               own_chan ch st ∗
               (∀ v, ⌜ v ∈ drop st.(chanstate.received) st.(chanstate.sent) ⌝ → R id' v) ∗
               (∀ r, own_chan ch (set chanstate.received (Nat.add r) st) ={⊤,∅}=∗ True)
         }}}
      ) ∗
    "#Trigger" ∷
      (∀ (id' : w64) (x : interface.t),
         {{{ I γ ∗ R id' x }}}
           interface.get #"Trigger" #w #id' #x
         {{{ RET #(); I γ }}}
      ) ∗
    "#IsRegistered" ∷
      (∀ (id' : w64),
         {{{ I γ }}}
           interface.get #"IsRegistered" #w #id'
         {{{ (reg : bool), RET #reg; I γ }}}
      ).
#[global] Opaque own_Wait.
#[local] Transparent own_Wait.

Lemma wp_Wait__Register γ w (id' : w64) R :
  {{{ is_pkg_init wait ∗ own_Wait γ w R ∗ own_unregistered_id γ id' }}}
    interface.get #"Register" #w #id'
  {{{ ch, RET #ch;
      own_Wait γ w R ∗
      |={⊤,∅}=>
        ∃ (st : chanstate.t interface.t),
        own_chan ch st ∗
        (∀ v, ⌜ v ∈ drop st.(chanstate.received) st.(chanstate.sent) ⌝ → R id' v) ∗
        (∀ r, own_chan ch (set chanstate.received (Nat.add r) st) ={⊤,∅}=∗ True)
  }}}.
Proof.
  wp_start as "[Hw Hid]". iNamed "Hw".
  iApply ("Register" with "[$]"). iIntros "!> * [I post]". iApply "HΦ". iFrame "∗#".
Qed.

Lemma wp_Wait__Trigger γ w (id' : w64) (x : interface.t) R :
  {{{ is_pkg_init wait ∗ own_Wait γ w R ∗ R id' x }}}
    interface.get #"Trigger" #w #id' #x
  {{{ RET #(); own_Wait γ w R }}}.
Proof.
  wp_start as "[Hw HR]". iNamed "Hw".
  iApply ("Trigger" with "[$]"). iIntros "!> * I". iApply "HΦ". iFrame "∗#".
Qed.

Lemma wp_Wait__IsRegistered γ w (id' : w64) R :
  {{{ is_pkg_init wait ∗ own_Wait γ w R }}}
    interface.get #"IsRegistered" #w #id'
  {{{ (reg : bool), RET #reg; own_Wait γ w R }}}.
Proof.
  wp_start as "Hw". iNamed "Hw".
  iApply ("IsRegistered" with "[$]"). iIntros "!> * I". iApply "HΦ". iFrame "∗#".
Qed.

End wps.
