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
Definition own ptr obj d : iProp Σ :=
  ∃ ptr_sigDig0 ptr_sigDig1,
  "Hown_sigDig0" ∷ SigDig.own ptr_sigDig0 obj.(sigDig0) d ∗
  "Hptr_sigDig0" ∷ ptr ↦[Evid :: "sigDig0"]{d} #ptr_sigDig0 ∗
  "Hown_sigDig1" ∷ SigDig.own ptr_sigDig1 obj.(sigDig1) d ∗
  "Hptr_sigDig1" ∷ ptr ↦[Evid :: "sigDig1"]{d} #ptr_sigDig1.
End defs.
End Evid.

Section defs.
Context `{!heapGS Σ, !pavG Σ}.

Definition is_SigDig obj pk : iProp Σ :=
  is_sig pk (PreSigDig.encodesF
    (PreSigDig.mk obj.(SigDig.Epoch) obj.(SigDig.Dig))) obj.(SigDig.Sig).

Definition is_Evid obj pk : iProp Σ :=
  "#His_sigDig0" ∷ is_SigDig obj.(Evid.sigDig0) pk ∗
  "#His_sigDig1" ∷ is_SigDig obj.(Evid.sigDig1) pk ∗
  "%Heq_ep" ∷ ⌜ obj.(Evid.sigDig0).(SigDig.Epoch) =
                obj.(Evid.sigDig1).(SigDig.Epoch) ⌝ ∗
  "%Hneq_dig" ∷ ⌜ obj.(Evid.sigDig0).(SigDig.Dig) ≠
                  obj.(Evid.sigDig1).(SigDig.Dig) ⌝.
End defs.

Section wps.
Context `{!heapGS Σ, !pavG Σ}.

Lemma wp_CheckSigDig ptr obj sl_pk pk d0 :
  {{{
    "Hown_SigDig" ∷ SigDig.own ptr obj d0 ∗
    "#Hsl_pk" ∷ own_slice_small sl_pk byteT DfracDiscarded pk
  }}}
  CheckSigDig #ptr (slice_val sl_pk)
  {{{
    (err : bool), RET #err;
    "Hgenie" ∷ (⌜ err = false ⌝ ∗-∗ is_SigDig obj pk) ∗
    "Hown_SigDig" ∷ SigDig.own ptr obj d0
  }}}.
Proof. Admitted.

End wps.
