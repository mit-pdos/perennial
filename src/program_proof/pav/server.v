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

Module Server.
Record t :=
  mk {
    sig_pk: list w8;
    vrf_pk: list w8;
    γepoch: gname;
    γdigs: gname;
    γmap: gname;
  }.
End Server.

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
  "HkeyM" ∷ own_Tree ptr_key_map key_map d ∗
  "#Hptr_keyM" ∷ ptr ↦[Server :: "keyMap"]□ #ptr_key_map ∗
  "Huinfo" ∷ ([∗ map] l;x ∈ ptr2_user_info;user_info, userState.own l x d) ∗
  "Hptr2_uinfo" ∷ own_map ptr_user_info d ptr2_user_info ∗
  "#Hptr_uinfo" ∷ ptr ↦[Server :: "userInfo"]□ #ptr_user_info ∗
  "#Hep_hist" ∷ ([∗ list] l;x ∈ ptr2_epoch_hist;epoch_hist, servEpochInfo.own l x) ∗
  "Hptr2_ep_hist" ∷ own_slice sl_epoch_hist ptrT d ptr2_epoch_hist ∗
  "Hptr_ep_hist" ∷ ptr ↦[Server :: "epochHist"]{d} (slice_val sl_epoch_hist).

Definition is_Server ptr serv : iProp Σ :=
  ∃ mu ptr_sig_sk sig_pk γ ptr_vrf_sk
    sl_commit_secret (commit_secret : list w8) ptr_workq,
  "#HmuR" ∷ is_rwlock nroot #mu (λ q, own_Server ptr (DfracOwn (q / 2))) ∗
  "#Hptr_mu" ∷ ptr ↦[Server :: "mu"]□ #mu ∗
  "#Hsig_sk" ∷ is_sig_sk ptr_sig_sk sig_pk (serv_sigpred γ) ∗
  "#Hptr_sig_sk" ∷ ptr ↦[Server :: "sigSk"]□ #ptr_sig_sk ∗
  "#Hvrf_sk" ∷ is_vrf_sk ptr_vrf_sk serv.(Server.vrf_pk) ∗
  "#Hptr_vrf_sk" ∷ ptr ↦[Server :: "vrfSk"]□ #ptr_vrf_sk ∗
  "#Hsl_sec" ∷ own_slice_small sl_commit_secret byteT DfracDiscarded commit_secret ∗
  "#Hptr_sec" ∷ ptr ↦[Server :: "commitSecret"]□ (slice_val sl_commit_secret) ∗
  "#Hworkq" ∷ is_WorkQ ptr_workq ∗
  "#Hptr_workq" ∷ ptr ↦[Server :: "workQ"]□ #ptr_workq.

Definition wish_memb vrf_pk uid ver sigdig memb : iProp Σ :=
  ∃ label map_val,
  let label_pre := (MapLabelPre.encodesF $ MapLabelPre.mk uid ver) in
  "#Hvrf_proof" ∷ is_vrf_proof vrf_pk label_pre memb.(Memb.LabelProof) ∗
  "#Hvrf_out" ∷ is_vrf_out vrf_pk label_pre label ∗
  "#Hmap_val" ∷ is_hash (CommitOpen.encodesF memb.(Memb.PkOpen)) map_val ∗
  "#Hmerk" ∷ Verify_wish true label map_val memb.(Memb.MerkleProof) sigdig.(SigDig.Dig).

Definition wish_nonmemb vrf_pk uid ver sigdig nonmemb : iProp Σ :=
  ∃ label,
  let label_pre := (MapLabelPre.encodesF $ MapLabelPre.mk uid ver) in
  "#Hvrf_proof" ∷ is_vrf_proof vrf_pk label_pre nonmemb.(NonMemb.LabelProof) ∗
  "#Hvrf_out" ∷ is_vrf_out vrf_pk label_pre label ∗
  "#Hmerk" ∷ Verify_wish false label [] nonmemb.(NonMemb.MerkleProof)
    sigdig.(SigDig.Dig).

(* TODO: server correctness not just that all client fns
(including audit) will not error.
also that without even talking to auditor, clients can have agreement.
for that, the server needs to guarantee that put / get elems
are actually in server ghost state, and that ghost state
satisfies certain invs, similar to auditor. *)

Lemma wp_Server__Put ptr serv uid nVers sl_pk (pk : list w8) cli_ep :
  {{{
    "#Hserv" ∷ is_Server ptr serv ∗
    "Hpks" ∷ uid ↪[serv.(Server.γmap)] nVers ∗
    "#Hsl_pk" ∷ own_slice_small sl_pk byteT DfracDiscarded pk ∗
    "#Hlb_ep" ∷ mono_nat_lb_own serv.(Server.γepoch) cli_ep
  }}}
  Server__Put #ptr #uid (slice_val sl_pk)
  {{{
    ptr_sigdig sigdig ptr_memb memb ptr_nonmemb nonmemb err,
    RET (#ptr_sigdig, #ptr_memb, #ptr_nonmemb, #err);
    "Hpks" ∷ uid ↪[serv.(Server.γmap)] (nVers + 1) ∗
    "%Heq_ep" ∷ ⌜ sigdig.(SigDig.Epoch) = memb.(Memb.EpochAdded) ⌝ ∗
    "%Heq_pk" ∷ ⌜ pk = memb.(Memb.PkOpen).(CommitOpen.Val) ⌝ ∗
    "#Hsigdig" ∷ SigDig.own ptr_sigdig sigdig DfracDiscarded ∗
    (* currently, sigpred can just be:
    (global digs) !! sigdig.Epoch = sigdig.Dig *)
    "#Hsig" ∷ is_sig serv.(Server.sig_pk)
      (PreSigDig.encodesF $ PreSigDig.mk sigdig.(SigDig.Epoch) sigdig.(SigDig.Dig))
      sigdig.(SigDig.Sig) ∗
    "#Hlb_ep" ∷ mono_nat_lb_own serv.(Server.γepoch) (uint.nat sigdig.(SigDig.Epoch)) ∗
    "%Hlt_ep" ∷ ⌜ Z.of_nat cli_ep < uint.Z sigdig.(SigDig.Epoch) ⌝ ∗
    "Hmemb" ∷ Memb.own ptr_memb memb (DfracOwn 1) ∗
    "#Hwish_memb" ∷ wish_memb serv.(Server.vrf_pk) uid (W64 $ nVers) sigdig memb ∗
    "Hnonmemb" ∷ NonMemb.own ptr_nonmemb nonmemb (DfracOwn 1) ∗
    "#Hwish_nonmemb" ∷ wish_nonmemb serv.(Server.vrf_pk)
      uid (W64 $ (nVers + 1)) sigdig nonmemb ∗
    "%Herr" ∷ ⌜ err = false ⌝
  }}}.
Proof. Admitted.

(*
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
*)

End proof.
