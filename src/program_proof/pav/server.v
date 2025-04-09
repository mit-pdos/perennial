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
    updates: gmap (list w8) (w64 * list w8);
    dig: list w8;
    sig: list w8;
  }.

Section defs.
Context `{!heapGS Σ, !pavG Σ}.

Definition own ptr x : iProp Σ :=
  ∃ ptr2_upd ptr_upd sl_dig sl_sig,
  "#Hupd" ∷ ([∗ map] sl;y ∈ ptr2_upd;x.(updates),
    own_slice_small sl byteT DfracDiscarded
      (MapValPre.encodesF $ MapValPre.mk y.1 y.2)) ∗
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
    γsig: gname;
    γcli: gname;
  }.
End Server.

Section proof.
Context `{!heapGS Σ, !pavG Σ}.

(* serv_sigpred is more simple than adtr_sigpred bc more things
are moved to inv_gs. *)
Definition serv_sigpred (γsig : gname) : (list w8 → iProp Σ) :=
  λ preByt,
  (∃ pre gs_hist,
  "%Henc" ∷ ⌜ PreSigDig.encodes preByt pre ⌝ ∗
  "#Hlb_hist" ∷ mono_list_lb_own γsig gs_hist ∗
  "%Hlook_dig" ∷ ⌜ gs_hist.*2 !! uint.nat pre.(PreSigDig.Epoch) =
    Some pre.(PreSigDig.Dig) ⌝)%I.

Definition is_WorkQ (ptr : loc) : iProp Σ. Admitted.

Definition maps_mono (ms : list adtr_map_ty) :=
  ∀ (i j : w64) mi mj,
  ms !! (uint.nat i) = Some mi →
  ms !! (uint.nat j) = Some mj →
  uint.Z i ≤ uint.Z j →
  mi ⊆ mj.

Definition epochs_ok (ms : list adtr_map_ty) :=
  ∀ (ep : w64) m_ep k ep' comm,
  ms !! (uint.nat ep) = Some m_ep →
  m_ep !! k = Some (ep', comm) →
  uint.Z ep' ≤ uint.Z ep.

Definition lower_map (m : adtr_map_ty) : merkle_map_ty :=
  (λ v, MapValPre.encodesF (MapValPre.mk v.1 v.2)) <$> m.

(* inv_gs will be a proper iris invariant so that clients can access
and learn that their own key is fresh even in latest epoch. *)
Definition inv_gs serv : iProp Σ :=
  ∃ gs_hist gs_vers,
  "Hgs_ep" ∷ mono_nat_auth_own serv.(Server.γepoch) (1/2) (length gs_hist) ∗
  "Hgs_sig" ∷ mono_list_auth_own serv.(Server.γsig) (1/2) gs_hist ∗
  "Hgs_cli" ∷ ghost_map_auth serv.(Server.γcli) (1/2) gs_vers ∗

  "%Hmono_maps" ∷ ⌜ maps_mono gs_hist.*1 ⌝ ∗
  "%Hok_epochs" ∷ ⌜ epochs_ok gs_hist.*1 ⌝ ∗
  "#Hok_vers" ∷ ([∗ map] uid ↦ nVers ∈ gs_vers,
    ∃ label,
    "#Hvrf_out" ∷ is_vrf_out serv.(Server.vrf_pk)
      (MapLabelPre.encodesF $ MapLabelPre.mk uid nVers) label ∗
    "%Hlook_map" ∷ ⌜ (default ∅ (last gs_hist.*1)) !! label = None ⌝).

Definition own_Server ptr serv q : iProp Σ :=
  ∃ ptr_key_map key_map ptr_user_info
    ptr2_user_info user_info sl_commit_secret commit_secret
    sl_epoch_hist ptr2_epoch_hist epoch_hist
    gs_hist gs_vers,

  (* ghost ownership. the other 1/2 is in the inv. *)
  "Hgs_ep" ∷ mono_nat_auth_own serv.(Server.γepoch) (q/2) (length gs_hist) ∗
  "Hgs_sig" ∷ mono_list_auth_own serv.(Server.γsig) (q/2) gs_hist ∗
  "Hgs_cli" ∷ ghost_map_auth serv.(Server.γcli) (q/2) gs_vers ∗

  (* physical ownership. *)
  "HkeyM" ∷ own_Tree ptr_key_map key_map (DfracOwn q) ∗
  "#Hptr_keyM" ∷ ptr ↦[Server :: "keyMap"]□ #ptr_key_map ∗
  "Huinfo" ∷ ([∗ map] l;x ∈ ptr2_user_info;user_info,
    userState.own l x (DfracOwn q)) ∗
  "Hptr2_uinfo" ∷ own_map ptr_user_info (DfracOwn q) ptr2_user_info ∗
  "#Hptr_uinfo" ∷ ptr ↦[Server :: "userInfo"]□ #ptr_user_info ∗
  "#Hep_hist" ∷ ([∗ list] l;x ∈ ptr2_epoch_hist;epoch_hist,
    servEpochInfo.own l x) ∗
  "Hptr2_ep_hist" ∷ own_slice sl_epoch_hist ptrT (DfracOwn q) ptr2_epoch_hist ∗
  "Hptr_ep_hist" ∷ ptr ↦[Server :: "epochHist"]{DfracOwn q} (slice_val sl_epoch_hist) ∗
  "#Hsl_sec" ∷ own_slice_small sl_commit_secret byteT DfracDiscarded commit_secret ∗
  "#Hptr_sec" ∷ ptr ↦[Server :: "commitSecret"]□ (slice_val sl_commit_secret) ∗

  (* physical invariants. *)
  "#Hsig_hist" ∷ ([∗ list] ep ↦ x ∈ epoch_hist,
    is_sig serv.(Server.sig_pk)
      (PreSigDig.encodesF $ PreSigDig.mk (W64 ep) x.(servEpochInfo.dig))
      x.(servEpochInfo.sig)) ∗
  "Hplain_pk" ∷ ([∗ map] uid ↦ x ∈ user_info,
    ∃ label commit ep,
    "#Hvrf_out" ∷ is_vrf_out serv.(Server.vrf_pk)
      (MapLabelPre.encodesF $
        MapLabelPre.mk uid (word.sub x.(userState.numVers) (W64 1)))
      label ∗
    "#Hcommit" ∷ is_hash (CommitOpen.encodesF $
      CommitOpen.mk x.(userState.plainPk) commit_secret)
      commit ∗
    "%Hlook_map" ∷ ⌜ key_map !! label =
      Some (MapValPre.encodesF $ MapValPre.mk ep commit) ⌝) ∗

  (* physical-ghost reln. *)
  "%Heq_dig_hist" ∷ ⌜ gs_hist.*2 = servEpochInfo.dig <$> epoch_hist ⌝ ∗
  "%Heq_vers" ∷ ⌜ gs_vers = userState.numVers <$> user_info ⌝ ∗
  "%Heq_keyM" ∷ ⌜ key_map = lower_map (default ∅ (last gs_hist.*1)) ⌝ ∗
  "%Heq_map_hist" ∷ ([∗ list] ep ↦ x ∈ (drop 1 epoch_hist),
    ∃ prevM nextM,
    "%Hlook_prevM" ∷ ⌜ gs_hist.*1 !! (pred ep) = Some prevM ⌝ ∗
    "%Hlook_nextM" ∷ ⌜ gs_hist.*1 !! ep = Some nextM ⌝ ∗
    "%HupdM" ∷ ⌜ nextM = x.(servEpochInfo.updates) ∪ prevM ⌝).

Definition is_Server ptr serv : iProp Σ :=
  ∃ mu ptr_sig_sk sig_pk γ ptr_vrf_sk ptr_workq,
  "#Hinv_gs" ∷ inv nroot (inv_gs serv) ∗
  (* rwmutex has 1/2 physical ownership. other 1/2 owned by worker thread. *)
  "#HmuR" ∷ is_rwlock nroot #mu (λ q, own_Server ptr serv (q / 2)) ∗
  "#Hptr_mu" ∷ ptr ↦[Server :: "mu"]□ #mu ∗
  "#Hsig_sk" ∷ is_sig_sk ptr_sig_sk sig_pk (serv_sigpred γ) ∗
  "#Hptr_sig_sk" ∷ ptr ↦[Server :: "sigSk"]□ #ptr_sig_sk ∗
  "#Hvrf_sk" ∷ is_vrf_sk ptr_vrf_sk serv.(Server.vrf_pk) ∗
  "#Hptr_vrf_sk" ∷ ptr ↦[Server :: "vrfSk"]□ #ptr_vrf_sk ∗
  "#Hworkq" ∷ is_WorkQ ptr_workq ∗
  "#Hptr_workq" ∷ ptr ↦[Server :: "workQ"]□ #ptr_workq.

Definition wish_memb vrf_pk uid ver sigdig memb : iProp Σ :=
  ∃ label commit,
  let label_pre := (MapLabelPre.encodesF $ MapLabelPre.mk uid ver) in
  "#Hvrf_proof" ∷ is_vrf_proof vrf_pk label_pre memb.(Memb.LabelProof) ∗
  "#Hvrf_out" ∷ is_vrf_out vrf_pk label_pre label ∗
  "#Hcommit" ∷ is_hash (CommitOpen.encodesF memb.(Memb.PkOpen)) commit ∗
  "#Hmerk" ∷ Verify_wish true label
    (MapValPre.encodesF $ MapValPre.mk sigdig.(SigDig.Epoch) commit)
    memb.(Memb.MerkleProof) sigdig.(SigDig.Dig).

Definition wish_nonmemb vrf_pk uid ver sigdig nonmemb : iProp Σ :=
  ∃ label,
  let label_pre := (MapLabelPre.encodesF $ MapLabelPre.mk uid ver) in
  "#Hvrf_proof" ∷ is_vrf_proof vrf_pk label_pre nonmemb.(NonMemb.LabelProof) ∗
  "#Hvrf_out" ∷ is_vrf_out vrf_pk label_pre label ∗
  "#Hmerk" ∷ Verify_wish false label [] nonmemb.(NonMemb.MerkleProof)
    sigdig.(SigDig.Dig).

Lemma wp_Server__Put ptr serv uid nVers sl_pk (pk : list w8) cli_ep :
  {{{
    "#Hserv" ∷ is_Server ptr serv ∗
    "Hpks" ∷ uid ↪[serv.(Server.γcli)] nVers ∗
    "#Hsl_pk" ∷ own_slice_small sl_pk byteT DfracDiscarded pk ∗
    "#Hlb_ep" ∷ mono_nat_lb_own serv.(Server.γepoch) cli_ep
  }}}
  Server__Put #ptr #uid (slice_val sl_pk)
  {{{
    ptr_sigdig sigdig ptr_memb memb ptr_nonmemb nonmemb err,
    RET (#ptr_sigdig, #ptr_memb, #ptr_nonmemb, #err);
    "Hpks" ∷ uid ↪[serv.(Server.γcli)] (word.add nVers (W64 1)) ∗
    "%Heq_ep" ∷ ⌜ sigdig.(SigDig.Epoch) = memb.(Memb.EpochAdded) ⌝ ∗
    "%Heq_pk" ∷ ⌜ pk = memb.(Memb.PkOpen).(CommitOpen.Val) ⌝ ∗
    "#Hsigdig" ∷ SigDig.own ptr_sigdig sigdig DfracDiscarded ∗
    "#Hsig" ∷ is_sig serv.(Server.sig_pk)
      (PreSigDig.encodesF $ PreSigDig.mk sigdig.(SigDig.Epoch) sigdig.(SigDig.Dig))
      sigdig.(SigDig.Sig) ∗
    "#Hlb_ep" ∷ mono_nat_lb_own serv.(Server.γepoch) (uint.nat sigdig.(SigDig.Epoch)) ∗
    "%Hlt_ep" ∷ ⌜ Z.of_nat cli_ep < uint.Z sigdig.(SigDig.Epoch) ⌝ ∗
    "Hmemb" ∷ Memb.own ptr_memb memb (DfracOwn 1) ∗
    "#Hwish_memb" ∷ wish_memb serv.(Server.vrf_pk) uid nVers sigdig memb ∗
    "Hnonmemb" ∷ NonMemb.own ptr_nonmemb nonmemb (DfracOwn 1) ∗
    "#Hwish_nonmemb" ∷ wish_nonmemb serv.(Server.vrf_pk)
      uid (word.add nVers (W64 1)) sigdig nonmemb ∗
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
