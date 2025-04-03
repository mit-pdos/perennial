From New.proof.sync_proof Require Import base.
From New.proof.sync_proof Require rwmutex.

(** A specification for RWMutex which guards a fractional resource [P q].
    [RLock] returns [P rfrac] while [Lock] returns [P 1]. *)
Section proof.

Context `{hG:heapGS Σ, !ffi_semantics _ _}.
Context `{!goGlobalsGS Σ}.
Context `{!syncG Σ}.

Definition rfrac_def : Qp := / pos_to_Qp (Z.to_pos (rwmutex.actualMaxReaders + 1)).
Program Definition rfrac := sealed @rfrac_def.
Definition rfrac_unseal : rfrac = _ := seal_eq _.

Local Definition is_inv P γ γmax γrlocked γlocked : iProp Σ :=
  inv (nroot.@"inv")
    (∃ st, rwmutex.own_RWMutex γ st ∗
           match st with
           | Locked => own_tok_auth γrlocked 0
           | RLocked n =>
               own_tok_auth γrlocked n ∗
               own_toks γmax n ∗
               ghost_var γlocked 1 () ∗
               P ((pos_to_Qp $ Z.to_pos $ (rwmutex.actualMaxReaders + 1 - Z.of_nat n)%Z) * rfrac)%Qp
           end
    ).

Definition own_RWMutex (rw : loc) (P : Qp → iProp Σ) : iProp Σ :=
  ∃ γ γmax γrlocked γlocked,
  "Hown" ∷ rwmutex.own_RLock_token γ ∗
  "Hmax" ∷ own_toks γmax 1 ∗
  "#His" ∷ rwmutex.is_RWMutex rw γ (nroot.@"rw") ∗
  "#HPfrac" ∷ □(∀ q1 q2, P (q1 + q2)%Qp ∗-∗ P q1 ∗ P q2) ∗
  "#Hauth" ∷ own_tok_auth_dfrac γmax DfracDiscarded (Z.to_nat rwmutex.actualMaxReaders) ∗
  "#Hinv" ∷ is_inv P γ γmax γrlocked γlocked.
#[global] Opaque own_RWMutex.
#[local] Transparent own_RWMutex.

Definition own_RWMutex_RLocked (rw : loc) (P : Qp → iProp Σ) : iProp Σ :=
  ∃ γ γmax γrlocked γlocked,
  "Hrlocked" ∷ own_toks γrlocked 1 ∗
  "#His" ∷ rwmutex.is_RWMutex rw γ (nroot.@"rw") ∗
  "#HPfrac" ∷ □(∀ q1 q2, P (q1 + q2)%Qp ∗-∗ P q1 ∗ P q2) ∗
  "#Hauth" ∷ own_tok_auth_dfrac γmax DfracDiscarded (Z.to_nat rwmutex.actualMaxReaders) ∗
  "#Hinv" ∷ is_inv P γ γmax γrlocked γlocked.
#[global] Opaque own_RWMutex_RLocked.
#[local] Transparent own_RWMutex_RLocked.

Definition own_RWMutex_Locked (rw : loc) (P : Qp → iProp Σ) : iProp Σ :=
  ∃ γ γmax γrlocked γlocked,
  "Hlocked" ∷ ghost_var γlocked 1 () ∗
  "Hown_rlock" ∷ rwmutex.own_RLock_token γ ∗
  "Hmax" ∷ own_toks γmax 1 ∗
  "#His" ∷ rwmutex.is_RWMutex rw γ (nroot.@"rw") ∗
  "#HPfrac" ∷ □(∀ q1 q2, P (q1 + q2)%Qp ∗-∗ P q1 ∗ P q2) ∗
  "#Hauth" ∷ own_tok_auth_dfrac γmax DfracDiscarded (Z.to_nat rwmutex.actualMaxReaders) ∗
  "#Hinv" ∷ is_inv P γ γmax γrlocked γlocked.
#[global] Opaque own_RWMutex_Locked.
#[local] Transparent own_RWMutex_Locked.

(* XXX: For iDestructExists. *)
Instance : Inhabited rwmutex := {| inhabitant := Locked |}.

Lemma wp_RWMutex__RLock rw P :
  {{{ is_pkg_init sync ∗ own_RWMutex rw P }}}
    rw @ sync @ "RWMutex'ptr" @ "RLock" #()
  {{{ RET #(); own_RWMutex_RLocked rw P ∗ ▷ P rfrac }}}.
Proof.
  wp_start_folded as "Hpre". iNamed "Hpre".
  wp_apply (rwmutex.wp_RWMutex__RLock with "[$]").
  iInv "Hinv" as "Hi" "Hclose".
  iDestruct "Hi" as (?) "[>Hown HP]".
  iFrame. iApply fupd_mask_intro. { solve_ndisj. }
  iIntros "Hmask". iIntros (?) "% H". subst.
  iDestruct "HP" as "(>Hrtok & >Htoks & ? & HP)".
  iCombine "Htoks Hmax" as "Htoks".
  iCombine "Hauth Htoks" gives %Hle.
  replace (pos_to_Qp _ * rfrac)%Qp with
    (rfrac + pos_to_Qp (Z.to_pos $ (rwmutex.actualMaxReaders + 1 - Z.of_nat (num_readers + 1))%Z) * rfrac)%Qp.
  2:{
    replace (rfrac) with (1 * rfrac)%Qp at 1.
    2:{ rewrite left_id //. }
    rewrite -Qp.mul_add_distr_r.
    f_equal. rewrite pos_to_Qp_add. f_equal.
    word.
  }
  iMod (own_tok_auth_add 1 with "Hrtok") as "[Hrtok Ht]".
  iDestruct ("HPfrac" with "HP") as "[HP' HP]".
  iSpecialize ("HΦ" with "[$]"). iFrame.
  iMod "Hmask" as "_".
  iMod ("Hclose" with "[-]").
  { iFrame. replace (num_readers + 1)%nat with (S num_readers) by word. iFrame. } (* FIXME: word simplifier *)
  done.
Qed.

Lemma wp_RWMutex__RUnlock rw P :
  {{{ is_pkg_init sync ∗ own_RWMutex_RLocked rw P ∗ ▷ P rfrac }}}
    rw @ sync @ "RWMutex'ptr" @ "RUnlock" #()
  {{{ RET #(); own_RWMutex rw P }}}.
Proof.
  wp_start_folded as "[Ho HP_in]". iNamed "Ho".
  wp_apply (rwmutex.wp_RWMutex__RUnlock with "[$]").
  iInv "Hinv" as "Hi" "Hclose".
  iDestruct "Hi" as (?) "[>Hown HP]".
  destruct st.
  2:{ iDestruct "HP" as ">HP". iExFalso.
    iCombine "HP Hrlocked" gives %Hbad. lia. }
  iDestruct "HP" as "(>Hrauth & >Htoks & Hl & HP)".
  iApply fupd_mask_intro. { solve_ndisj. }
  iIntros "Hmask".
  iCombine "Hrauth Hrlocked" gives %Hle.
  iCombine "Hauth Htoks" gives %Hmaxle.
  iExists (num_readers - 1)%nat.
  replace (S (num_readers - 1)) with num_readers by lia.
  iFrame. iIntros "[Hrlock Hown]".
  iMod (own_tok_auth_sub with "Hrauth Hrlocked") as "Hrauth".
  iDestruct (own_toks_add_1 (num_readers - 1)%nat 1 with "[Htoks]") as "[Htok Htoks]".
  { iExactEq "Htoks". f_equal. lia. }
  iSpecialize ("HΦ" with "[$]"). iFrame.
  iMod "Hmask" as "_". iMod ("Hclose" with "[-]"); last done.
  iFrame. iFrame. iNext.
  iDestruct ("HPfrac" with "[$HP $HP_in]") as "HP".
  iExactEq "HP". f_equal.
  replace (_ + 1 - (_ - 1)%nat) with (rwmutex.actualMaxReaders + 1 - num_readers + 1) by lia.
  rewrite Z2Pos.inj_add; try word.
  rewrite -pos_to_Qp_add. rewrite Qp.mul_add_distr_r.
  f_equal. rewrite left_id //.
Qed.

Lemma wp_RWMutex__Lock rw P :
  {{{ is_pkg_init sync ∗ own_RWMutex rw P }}}
    rw @ sync @ "RWMutex'ptr" @ "Lock" #()
  {{{ RET #(); own_RWMutex_Locked rw P ∗ ▷ P 1%Qp }}}.
Proof.
  wp_start_folded as "Ho". iNamed "Ho".
  wp_apply (rwmutex.wp_RWMutex__Lock with "[$]").
  iInv "Hinv" as "Hi" "Hclose".
  iDestruct "Hi" as (?) "[>Hstate HP]".
  iFrame. iApply fupd_mask_intro. { solve_ndisj. } iIntros "Hmask".
  iIntros "% Hst". subst.
  rewrite rfrac_unseal. rewrite /rfrac_def Qp.mul_inv_r.
  iDestruct "HP" as "(? & ? & >Hl & HP)".
  iDestruct ("HΦ" with "[$]") as "$".
  iMod "Hmask" as "_".
  iMod ("Hclose" with "[$]"); last done.
Qed.

Lemma wp_RWMutex__Unlock rw P :
  {{{ is_pkg_init sync ∗ own_RWMutex_Locked rw P ∗ ▷ P 1%Qp }}}
    rw @ sync @ "RWMutex'ptr" @ "Unlock" #()
  {{{ RET #(); own_RWMutex rw P }}}.
Proof.
  wp_start_folded as "[Ho HP_in]". iNamed "Ho".
  wp_apply (rwmutex.wp_RWMutex__Unlock with "[$]").
  iInv "Hinv" as "Hi" "Hclose".
  iDestruct "Hi" as (?) "[>Hstate HP]".
  destruct st.
  { iDestruct "HP" as "(_ & _ & >Hbad & _)". iCombine "Hlocked Hbad" gives %Hbad.
    exfalso. naive_solver. }
  iFrame. iApply fupd_mask_intro. { solve_ndisj. } iIntros "Hmask".
  iIntros "Hst". iDestruct ("HΦ" with "[$]") as "$".
  iMod own_toks_0 as "?".
  iMod "Hmask" as "_".
  iMod ("Hclose" with "[-]"); last done.
  iFrame.
  rewrite rfrac_unseal. rewrite /rfrac_def Qp.mul_inv_r. iFrame.
Qed.

End proof.
