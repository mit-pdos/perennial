From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv Require paxos.
From Perennial Require Export paxos.definitions.

Section withlock_proof.

Context `{!heapGS Σ}.

Context `{!paxosG Σ}.
Context `{!paxosParams.t Σ}.
Import paxosParams.

Lemma encodes_paxosState_inj st1 st2 data :
  encodes_paxosState st1 data →
  encodes_paxosState st2 data →
  st1 = st2.
Proof.
  intros H1 H2.
  destruct H1 as [H1 | [-> ->]].
  {
    subst.
    destruct H2 as [H2 | [? ->]].
    { by eapply inj in H2; last apply _. }
    exfalso.
    done.
  }
  destruct H2 as [H2 | [? ->]].
  { by exfalso. }
  done.
Qed.

Lemma wp_Server__withLock (s:loc) γ γsrv (f:val) Φ :
  is_Server s γ γsrv -∗
  (∀ ps pst,
  ("Hvol" ∷ paxosState.own_vol ps pst ∗
   "#HP" ∷ □ Pwf pst.(paxosState.state)) -∗
  WP f #ps {{ λ _, ∃ pst', paxosState.own_vol ps pst' ∗
                   (□ Pwf pst'.(paxosState.state)) ∗
                   (own_paxosState_ghost γ γsrv pst ={⊤∖↑fileN}=∗
                    own_paxosState_ghost γ γsrv pst' ∗ Φ #())
    }}) -∗
  WP Server__withLock #s f {{ Φ }}
.
Proof.
  iIntros "#Hsrv Hwp".
  wp_rec.
  wp_pures.
  iNamed "Hsrv".
  wp_loadField.
  wp_apply (wp_Mutex__Lock with "[$]").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".
  wp_pures.
  wp_loadField.
  wp_bind (f #ps).
  wp_apply (wp_wand with "[Hwp Hvol]").
  { wp_apply ("Hwp" with "[$]"). }
  iIntros (?) "Hpost".
  iClear "HP".
  iDestruct "Hpost" as (?) "(Hvol & #HP & Hupd)".
  wp_pures.
  wp_loadField.
  wp_apply (paxosState.wp_encode with "[$]").
  iIntros (?) "[Hvol Hsl]".
  wp_loadField.
  iDestruct (own_slice_to_small with "Hsl") as "Hsl".
  wp_apply (wp_AsyncFile__Write with "[$Hfile $Hsl Hupd]").
  {
    iIntros "Hi".
    iNamed "Hi".
    eapply encodes_paxosState_inj in Henc; last exact HencPaxos.
    subst.
    subst.
    iMod (fupd_mask_subseteq _) as "Hmask".
    2: iMod ("Hupd" with "[$]") as "[Hghost HΦ]".
    { solve_ndisj. }
    iMod "Hmask".
    iModIntro.
    iSplitR "HΦ".
    { repeat iExists _; iFrame. iPureIntro.
      by left. }
    iAccu.
  }
  iIntros (?) "[Hfile Hwp]".
  wp_pures.
  wp_loadField.
  wp_apply (wp_Mutex__Unlock with "[-Hwp]").
  {
    iFrame "HmuInv Hlocked".
    iNext.
    repeat iExists _.
    iFrame "∗#%". iPureIntro. by left.
  }
  wp_pures.
  wp_apply (wp_wand with "Hwp").
  iIntros (?) "HΦ".
  wp_pures. iModIntro. iFrame.
Qed.

End withlock_proof.
