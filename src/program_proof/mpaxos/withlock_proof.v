From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv Require mpaxos.
From Perennial.program_proof.mpaxos Require Export definitions.

Section withlock_proof.

Context `{!heapGS Σ}.

Context `{!mpG Σ}.
Context `{HconfigTC:!configTC}.

Lemma wp_Server__withLock (s:loc) γ γsrv (f:val) Φ :
  is_Server s γ γsrv -∗
  (∀ ps pst,
  paxosState.own_vol ps pst -∗
  WP f #ps {{ λ _, ∃ pst', paxosState.own_vol ps pst' ∗
                   (paxosState.own_ghost γ γsrv pst ={⊤∖↑fileN}=∗
                    paxosState.own_ghost γ γsrv pst' ∗ Φ #())
    }}) -∗
  WP Server__withLock #s f {{ Φ }}
.
Proof.
  iIntros "#Hsrv Hwp".
  wp_lam.
  wp_pures.
  iNamed "Hsrv".
  wp_loadField.
  wp_apply (acquire_spec with "[$]").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".
  wp_pures.
  wp_loadField.
  wp_bind (f #ps).
  wp_apply (wp_wand with "[Hwp Hvol]").
  { wp_apply ("Hwp" with "Hvol"). }
  iIntros (?) "Hpost".
  iDestruct "Hpost" as (?) "[Hvol Hupd]".
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
    eapply inj in Henc; last apply _.
    subst.
    iMod ("Hupd" with "[$]") as "[Hghost HΦ]".
    iModIntro.
    iSplitR "HΦ".
    { repeat iExists _; iFrame. done. }
    iAccu.
  }
  iIntros (?) "[Hfile Hwp]".
  wp_pures.
  wp_loadField.
  wp_apply (release_spec with "[-Hwp]").
  {
    iFrame "HmuInv Hlocked".
    iNext.
    repeat iExists _.
    iFrame.
  }
  wp_pures.
  wp_apply (wp_wand with "Hwp").
  iIntros (?) "HΦ".
  wp_pures. iModIntro. iFrame.
Qed.

End withlock_proof.
