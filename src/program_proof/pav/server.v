From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.pav Require Import kt.

From Perennial.program_proof.pav Require Import core cryptoffi cryptoutil serde merkle.
From Perennial.goose_lang.lib.rwlock Require Import rwlock_noncrash.

Module userState.
Record t :=
  mk {
    numVers: w64;
    plainPk: list w8;
  }.

Section defs.
Context `{!heapGS Σ, !pavG Σ}.

Definition own ptr x d : iProp Σ :=
  ∃ sl_plain_pk,
  "Hptr_num_vers" ∷ ptr ↦[userState :: "numVers"]{d} #x.(numVers) ∗
  "#Hsl_plain_pk" ∷ own_slice_small sl_plain_pk byteT DfracDiscarded x.(plainPk) ∗
  "Hptr_plain_pk" ∷ ptr ↦[userState :: "plainPk"]{d} (slice_val sl_plain_pk).
End defs.
End userState.

Module servEpochInfo.
Record t :=
  mk {
    updates: gmap byte_string (list w8);
    dig: list w8;
    sig: list w8;
  }.

Section defs.
Context `{!heapGS Σ, !pavG Σ}.

Definition own ptr x : iProp Σ :=
  ∃ ptr2_upd ptr_upd sl_dig sl_sig,
  "#Hupd" ∷ ([∗ map] sl;u ∈ ptr2_upd;x.(updates),
    own_slice_small sl byteT DfracDiscarded u) ∗
  "#Hptr2_upd" ∷ own_map ptr_upd DfracDiscarded ptr2_upd ∗
  "#Hptr_upd" ∷ ptr ↦[servEpochInfo :: "updates"]□ #ptr_upd ∗
  "#Hsl_dig" ∷ own_slice_small sl_dig byteT DfracDiscarded x.(dig) ∗
  "#Hptr_dig" ∷ ptr ↦[servEpochInfo :: "dig"]□ (slice_val sl_dig) ∗
  "#Hsl_sig" ∷ own_slice_small sl_sig byteT DfracDiscarded x.(sig) ∗
  "#Hptr_sig" ∷ ptr ↦[servEpochInfo :: "sig"]□ (slice_val sl_sig).
End defs.
End servEpochInfo.

Section proof.
Context `{!heapGS Σ, !pavG Σ}.

Definition serv_sigpred (γ : gname) : (list w8 → iProp Σ) :=
  (* TODO: fill in. *)
  λ data, True%I.

Definition is_WorkQ (ptr : loc) : iProp Σ. Admitted.

Definition own_Server (ptr : loc) (d : dfrac) : iProp Σ :=
  ∃ ptr_key_map key_map ptr_user_info
    (ptr2_user_info : gmap w64 _) user_info
    sl_epoch_hist ptr2_epoch_hist epoch_hist,
  "Hkey_map" ∷ own_Tree ptr_key_map key_map d ∗
  "#Hptr_key_map" ∷ ptr ↦[Server :: "keyMap"]□ #ptr_key_map ∗
  "Huser_info" ∷ ([∗ map] l;x ∈ ptr2_user_info;user_info, userState.own l x d) ∗
  "Hptr2_user_info" ∷ own_map ptr_user_info d ptr2_user_info ∗
  "#Hptr_user_info" ∷ ptr ↦[Server :: "userInfo"]□ #ptr_user_info ∗
  "#Hepoch_hist" ∷ ([∗ list] l;x ∈ ptr2_epoch_hist;epoch_hist, servEpochInfo.own l x) ∗
  "Hptr2_epoch_hist" ∷ own_slice sl_epoch_hist ptrT d ptr2_epoch_hist ∗
  "Hptr_epoch_hist" ∷ ptr ↦[Server :: "epochHist"]{d} (slice_val sl_epoch_hist).

Definition is_Server ptr : iProp Σ :=
  ∃ mu ptr_sig_sk sig_pk γ ptr_vrf_sk vrf_pk
    sl_commit_secret (commit_secret : list w8) ptr_workq,
  "#HmuR" ∷ is_rwlock nroot #mu (λ q, own_Server ptr (DfracOwn (q / 2))) ∗
  "#Hptr_mu" ∷ ptr ↦[Server :: "mu"]□ #mu ∗
  "#His_sig_sk" ∷ is_sig_sk ptr_sig_sk sig_pk (serv_sigpred γ) ∗
  "#Hptr_sig_sk" ∷ ptr ↦[Server :: "sigSk"]□ #ptr_sig_sk ∗
  "#His_vrf_sk" ∷ is_vrf_sk ptr_vrf_sk vrf_pk ∗
  "#Hptr_vrf_sk" ∷ ptr ↦[Server :: "vrfSk"]□ #ptr_vrf_sk ∗
  "#Hsl_commit_secret" ∷ own_slice_small sl_commit_secret byteT DfracDiscarded commit_secret ∗
  "#Hptr_commit_secret" ∷ ptr ↦[Server :: "commitSecret"]□ (slice_val sl_commit_secret) ∗
  "#His_workq" ∷ is_WorkQ ptr_workq ∗
  "#Hptr_workq" ∷ ptr ↦[Server :: "workQ"]□ #ptr_workq.

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
  iNamed"Hown_pk_open". wp_loadField.
  wp_apply wp_slice_len.
  wp_apply wp_NewSliceWithCap; [word|]. iIntros "* Hsl_enc".
  destruct pk_open. simpl.
  wp_apply (CommitOpen.wp_enc _ _ _ (CommitOpen.mk _ _ _)
    with "[$Hsl_enc $Hsl_val $Hptr_val $Hsl_rand $Hptr_rand]").
  iIntros "*". iNamedSuffix 1 "_open". simpl.
  iDestruct (own_slice_to_small with "Hsl_enc_open") as "Hsl_enc_open".
  wp_apply (wp_Hash with "[$Hsl_enc_open]"). iIntros "*". iNamed 1.
  wp_apply wp_allocStruct; [val_ty|]. iIntros "* H".
  iDestruct (struct_fields_split with "H") as "H". iNamed "H".
  wp_apply wp_NewSliceWithCap; [word|]. iIntros "* Hsl_enc".
  iDestruct (own_slice_to_small with "Hsl_hash") as "Hsl_hash".
  iPersist "Hsl_hash".
  wp_apply (MapValPre.wp_enc (MapValPre.mk _ _) with "[$Hsl_enc $Epoch $PkCommit $Hsl_hash]").
  iIntros "*". iNamedSuffix 1 "_mapval". simpl.
  iDestruct (own_slice_to_small with "Hsl_enc_mapval") as "Hsl_enc_mapval".
  iApply "HΦ". iFrame "∗#".
Qed.

End proof.
