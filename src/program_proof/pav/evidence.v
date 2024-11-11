From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.pav Require Import kt.

From Perennial.program_proof.pav Require Import core cryptoffi serde.

Module Evid.
Record t :=
  mk {
    sigDig0: SigDig.t;
    sigDig1: SigDig.t;
  }.
Section defs.
Context `{!heapGS Σ, !pavG Σ}.
Definition own ptr obj : iProp Σ :=
  ∃ ptr_sigDig0 ptr_sigDig1,
  "Hown_sigDig0" ∷ SigDig.own ptr_sigDig0 obj.(sigDig0) ∗
  "Hptr_sigDig0" ∷ ptr ↦[Evid :: "sigDig0"] #ptr_sigDig0 ∗
  "Hown_sigDig1" ∷ SigDig.own ptr_sigDig1 obj.(sigDig1) ∗
  "Hptr_sigDig1" ∷ ptr ↦[Evid :: "sigDig1"] #ptr_sigDig1.
End defs.
End Evid.

Section defs.
Context `{!heapGS Σ, !pavG Σ}.

Definition is_SigDig obj pk : iProp Σ :=
  is_sig pk (PreSigDig.encodesF (PreSigDig.mk obj.(SigDig.Epoch) obj.(SigDig.Dig))) obj.(SigDig.Sig).

Definition is_Evid obj pk : iProp Σ :=
  "His_sigDig0" ∷ is_SigDig obj.(Evid.sigDig0) pk ∗
  "His_sigDig1" ∷ is_SigDig obj.(Evid.sigDig1) pk.
End defs.

Section wps.
Context `{!heapGS Σ, !pavG Σ}.

Lemma wp_CheckSigDig ptr obj sl_pk pk :
  {{{
    "Hown_SigDig" ∷ SigDig.own ptr obj ∗
    "#Hsl_pk" ∷ own_slice_small sl_pk byteT DfracDiscarded pk
  }}}
  CheckSigDig #ptr (slice_val sl_pk)
  {{{
    (err : bool), RET #err;
    "Hown_SigDig" ∷ SigDig.own ptr obj ∗
    "Hgenie" ∷ (is_SigDig obj pk ∗-∗ ⌜ err = false ⌝)
  }}}.
Proof. Admitted.

End wps.
