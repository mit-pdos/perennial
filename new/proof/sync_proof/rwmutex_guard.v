From New.proof.sync_proof Require Import base.
From New.proof.sync_proof Require rwmutex.
Import Qextra.

Section proof.

Context `{hG:heapGS Σ, !ffi_semantics _ _}.
Context `{!goGlobalsGS Σ}.
Context `{!syncG Σ}.

Definition rfrac_def : Qp := / pos_to_Qp (Z.to_pos rwmutex.actualMaxReaders + 1).
Program Definition rfrac := sealed @rfrac_def.
Definition rfrac_unseal : rfrac = _ := seal_eq _.

Definition own_RWMutex (rw : loc) (P : Qp → iProp Σ) : iProp Σ :=
  ∃ γ γmax,
  "Hown" ∷ rwmutex.own_RLock_token γ ∗
  "Hmax" ∷ own_toks γmax 1 ∗
  "#His" ∷ rwmutex.is_RWMutex rw γ (nroot.@"rw") ∗
  "#HPfrac" ∷ □(∀ q1 q2, P (q1 + q2)%Qp ∗-∗ P q1 ∗ P q2) ∗
  "#Hinv" ∷ inv (nroot.@"inv")
    (∃ st, rwmutex.own_RWMutex γ st ∗
           match st with
           | Locked => True
           | RLocked n =>
               own_tok_auth γmax (Z.to_nat rwmutex.actualMaxReaders) ∗
               own_toks γmax n ∗
               P ((pos_to_Qp $ Z.to_pos $ (rwmutex.actualMaxReaders + 1 - Z.of_nat n)%Z) * rfrac)%Qp
           end
    ).

Definition own_RWMutex_RLocked (rw : loc) (P : Qp → iProp Σ) : iProp Σ :=
  True
.

(* XXX: For iDestructExists. *)
Instance : Inhabited rwmutex := {| inhabitant := Locked |}.

Lemma wp_RWMutex__RLock rw P :
  {{{ is_pkg_init sync ∗ own_RWMutex rw P }}}
    rw @ sync @ "RWMutex'ptr" @ "RLock" #()
  {{{ RET #(); ▷ P rfrac }}}.
Proof.
  wp_start_folded as "Hpre". iNamed "Hpre".
  wp_apply (rwmutex.wp_RWMutex__RLock with "[$]").
  iInv "Hinv" as "Hi" "Hclose".
  iDestruct "Hi" as (?) "[>Hown HP]".
  iFrame. iApply fupd_mask_intro. { solve_ndisj. }
  iIntros "Hmask". iIntros (?) "% H". subst.
  iDestruct "HP" as "(>Hauth & >Htoks & HP)".
  iCombine "Htoks Hmax" as "Htoks".
  iCombine "Hauth Htoks" gives %Hle.
  replace
    (pos_to_Qp _ * rfrac)%Qp
    with
    (rfrac + pos_to_Qp (Z.to_pos $ (rwmutex.actualMaxReaders + 1 - Z.of_nat (num_readers + 1))%Z) * rfrac)%Qp.
  2:{
    replace (rfrac) with (1 * rfrac)%Qp at 1.
    2:{ rewrite left_id //. }
    rewrite -Qp.mul_add_distr_r.
    f_equal. rewrite pos_to_Qp_add. f_equal.
    word.
  }
  iDestruct ("HPfrac" with "HP") as "[HP' HP]".
  iSpecialize ("HΦ" with "HP'"). iFrame.
  iMod "Hmask" as "_".
  iMod ("Hclose" with "[-]").
  { iFrame. replace (num_readers + 1)%nat with (S num_readers) by word. iFrame. } (* FIXME: word simplifier *)
  done.
Qed.

End proof.
