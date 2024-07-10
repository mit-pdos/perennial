From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.vrsm Require paxos.
From Perennial Require Export paxos.definitions.

Section weakread_proof.

Context `{!heapGS Σ}.
Context `{Hparams:!paxosParams.t Σ}.
Import paxosParams.
Context `{!paxosG Σ}.

Lemma wp_Server__WeakRead s γ γsrv :
  {{{
        is_Server s γ γsrv
  }}}
    Server__WeakRead #s
  {{{
        (state:list u8) sl, RET (slice_val sl);
        readonly (own_slice_small sl byteT (DfracOwn 1) state) ∗
        Pwf state
  }}}.
Proof.
  iIntros (Φ) "#Hsrv HΦ".
  wp_call.
  iNamed "Hsrv".
  wp_loadField.
  wp_apply (acquire_spec with "[$]").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".
  iNamed "Hvol".
  wp_loadField.
  wp_loadField.
  wp_loadField.
  wp_apply (release_spec with "[-HΦ]").
  {
    do 2 iFrame "∗#%".
  }
  wp_pures.
  iModIntro.
  iApply "HΦ".
  iFrame "∗#".
Qed.

End weakread_proof.
