From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv Require paxos.
From Perennial.program_proof.reconnectclient Require Import proof.
From Perennial Require Export paxos.definitions.

Section clerk_proof.
Context `{!heapGS Σ}.
Context `{!paxosG Σ}.
Context `{Hparams:!paxosParams.t Σ}.
Import paxosParams.

Lemma wp_makeSingleClerk (host:u64) γ γsrv :
  {{{
        is_paxos_host host γ γsrv
  }}}
    MakeSingleClerk #host
  {{{
        ck, RET #ck; is_singleClerk ck γ γsrv
  }}}
.
Proof.
  iIntros (?) "#Hhost HΦ".
  wp_rec.
  wp_apply wp_MakeReconnectingClient.
  iIntros (?) "#Hcl".
  wp_apply (wp_allocStruct); first by val_ty.
  iIntros (?) "Hs". iDestruct (struct_fields_split with "Hs") as "HH".
  iNamed "HH".
  iMod (readonly_alloc_1 with "cl") as "#cl".
  wp_pures. iModIntro. iApply "HΦ".
  repeat iExists _; iFrame "#".
Qed.

End clerk_proof.
