From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.pav Require Import kt.

From Perennial.program_proof.pav Require Import core cryptoffi serde.

Section inv.
Context `{!heapGS Σ}.
Definition serv_sigpred (γ : gname) : (list w8 → iProp Σ) :=
  (* TODO: fill in. *)
  λ data, True%I.
End inv.

Module Server.
Definition t : Type. Admitted.

Section defs.
Context `{!heapGS Σ}.
Definition own (ptr : loc) (obj : t) : iProp Σ. Admitted.
End defs.
End Server.

Section wps.
Context `{!heapGS Σ}.
Lemma wp_compMapVal (epoch : w64) ptr_pk_open pk_open :
  {{{
    "Hown_pk_open" ∷ CommitOpen.own ptr_pk_open pk_open
  }}}
  compMapVal #epoch #ptr_pk_open
  {{{
    sl_map_val commit, RET (slice_val sl_map_val);
    "Hown_pk_open" ∷ CommitOpen.own ptr_pk_open pk_open ∗
    "#His_commit" ∷ is_commit pk_open.(CommitOpen.Val) commit ∗
    "Hsl_map_val" ∷ own_slice_small sl_map_val byteT (DfracOwn 1)
      (MapValPre.encodesF (MapValPre.mk epoch commit))
  }}}.
Proof.
  iIntros (Φ) "H HΦ". iNamed "H". wp_rec.
  wp_apply wp_NewSlice_0. iIntros "* Hsl_enc".
  wp_apply (CommitOpen.wp_enc with "[$Hsl_enc $Hown_pk_open]").
  iIntros "*". iNamedSuffix 1 "_open". simpl.
  iDestruct (own_slice_to_small with "Hsl_enc_open") as "Hsl_enc_open".
  wp_apply (wp_Hash with "[$Hsl_enc_open]"). iIntros "*". iNamed 1.
  wp_apply wp_allocStruct; [val_ty|]. iIntros "* H".
  iDestruct (struct_fields_split with "H") as "H". iNamed "H".
  wp_apply wp_NewSlice_0. iIntros "* Hsl_enc".
  iMod (own_slice_small_persist with "Hhash") as "#Hhash".
  wp_apply (MapValPre.wp_enc (MapValPre.mk _ _) with "[$Hsl_enc $Epoch $PkCommit $Hhash]").
  iIntros "*". iNamedSuffix 1 "_mapval". simpl.
  iDestruct (own_slice_to_small with "Hsl_enc_mapval") as "Hsl_enc_mapval".
  iApply "HΦ". iFrame "∗#".
Qed.

Lemma wp_newServer :
  {{{ True }}}
  NewServer #()
  {{{
    ptr_serv (serv : Server.t) sl_sigPk sigPk γ (vrfPk : loc), RET (#ptr_serv, slice_val sl_sigPk, #vrfPk);
    "Hown_serv" ∷ Server.own ptr_serv serv ∗
    "#Hsl_sigPk" ∷ own_slice_small sl_sigPk byteT DfracDiscarded sigPk ∗
    "#His_sigPk" ∷ is_sig_pk sigPk (serv_sigpred γ)
  }}}.
Proof. Admitted.
End wps.
