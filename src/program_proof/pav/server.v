From New.experiments Require Import glob.
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

Definition is_own ptr x : iProp Σ :=
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

Global Instance pers ptr x : Persistent (is_own ptr x) := _.
End defs.

End servEpochInfo.

Module Server.
Record t :=
  mk {
    sig_pk: list w8;
    vrf_pk: list w8;
    γepoch: gname;
    γhist: gname;
    γvers: gname;
    addr: w64;
  }.
End Server.

Section proof.
Context `{!heapGS Σ, !pavG Σ}.

(* serv_sigpred is more simple than adtr_sigpred bc more things
are moved to inv_gs. *)
Definition serv_sigpred (γhist : gname) : (list w8 → iProp Σ) :=
  λ preByt,
  (∃ pre gs_hist,
  "%Henc" ∷ ⌜ PreSigDig.encodes preByt pre ⌝ ∗
  "#Hlb_hist" ∷ mono_list_lb_own γhist gs_hist ∗
  "%Hlook_dig" ∷ ⌜ gs_hist.*2 !! uint.nat pre.(PreSigDig.Epoch) =
    Some pre.(PreSigDig.Dig) ⌝)%I.

Definition is_WorkQ (ptr : loc) : iProp Σ := True.

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
  "Hgs_hist" ∷ mono_list_auth_own serv.(Server.γhist) (1/2) gs_hist ∗
  "Hgs_vers" ∷ ghost_map_auth serv.(Server.γvers) (1/2) gs_vers ∗

  "%Hmono_maps" ∷ ⌜ maps_mono gs_hist.*1 ⌝ ∗
  "%Hok_epochs" ∷ ⌜ epochs_ok gs_hist.*1 ⌝ ∗
  "#Hok_vers" ∷ ([∗ map] uid ↦ nVers ∈ gs_vers,
    ∃ label,
    "#Hvrf_out" ∷ is_vrf_out serv.(Server.vrf_pk)
      (MapLabelPre.encodesF $ MapLabelPre.mk uid nVers) label ∗
    "%Hlook_map" ∷ ⌜ (default ∅ (last gs_hist.*1)) !! label = None ⌝).

(* TODO: lemma like hist_extend_selfmon. *)

Definition own_epoch_hist (hist_sl : Slice.t) (hist : list servEpochInfo.t) : iProp Σ :=
  ∃ hist_ptrs,
  "Hsl" ∷ own_slice_small hist_sl byteT (DfracOwn 1) hist_ptrs ∗
  "#His" ∷ [∗ list] ptr;info ∈ hist_ptrs;hist, servEpochInfo.is_own ptr info.

Definition own_Server ptr serv q : iProp Σ :=
  ∃ (keyMap_ptr userInfo_ptr : loc) userInfo_phys commitSecret_sl epochHist_sl
    epochHist_ptrs
    keyMap userInfo commitSecret epochHist
    gs_hist gs_vers,

  (* physical ownership. *)
  "epochHist" ∷ ptr ↦[Server :: "epochHist"]{DfracOwn q} (slice_val epochHist_sl) ∗
  "#userInfo" ∷ ptr ↦[Server :: "userInfo"]□ #userInfo_ptr ∗
  "#keyMap" ∷ ptr ↦[Server :: "keyMap"]□ #keyMap_ptr ∗
  "#commitSecret" ∷ ptr ↦[Server :: "commitSecret"]□ (slice_val commitSecret_sl) ∗
  "HkeyMap" ∷ own_Tree keyMap_ptr keyMap (DfracOwn q) ∗
  "HuserInfo_map" ∷ own_map userInfo_ptr (DfracOwn q) userInfo_phys ∗
  "HuserInfo_own" ∷ ([∗ map] l;x ∈ userInfo_phys; userInfo, userState.own l x (DfracOwn q)) ∗
  "HepochHist_sl" ∷ own_slice epochHist_sl ptrT (DfracOwn q) epochHist_ptrs ∗
  "#HepochHist_own" ∷ ([∗ list] l;x ∈ epochHist_ptrs;epochHist, servEpochInfo.is_own l x) ∗
  "#HcommitSecret" ∷ own_slice_small commitSecret_sl byteT DfracDiscarded commitSecret ∗

  (* physical invariants. *)
  "#Hsig_hist" ∷ ([∗ list] ep ↦ x ∈ epochHist,
    is_sig serv.(Server.sig_pk)
      (PreSigDig.encodesF $ PreSigDig.mk (W64 ep) x.(servEpochInfo.dig))
      x.(servEpochInfo.sig)) ∗
  "Hplain_pk" ∷ ([∗ map] uid ↦ x ∈ userInfo,
    ∃ label commit ep,
    "#Hvrf_out" ∷ is_vrf_out serv.(Server.vrf_pk)
      (MapLabelPre.encodesF $
        MapLabelPre.mk uid (word.sub x.(userState.numVers) (W64 1)))
      label ∗
    "#Hcommit" ∷ is_hash (CommitOpen.encodesF $
      CommitOpen.mk x.(userState.plainPk) commitSecret)
      commit ∗
    "%Hlook_map" ∷ ⌜ keyMap !! label =
      Some (MapValPre.encodesF $ MapValPre.mk ep commit) ⌝) ∗
  (* TODO: something here needs to tie the versions in userInfo_phys to keyMap.
  this will allow the getHist, etc. helper fns to prove that they got
  memb / non-memb proofs. *)

  (* ghost ownership. the other 1/2 is in the inv. *)
  "Hgs_ep" ∷ mono_nat_auth_own serv.(Server.γepoch) (q/2) (length gs_hist) ∗
  "Hgs_hist" ∷ mono_list_auth_own serv.(Server.γhist) (q/2) gs_hist ∗
  "Hgs_vers" ∷ ghost_map_auth serv.(Server.γvers) (q/2) gs_vers ∗

  (* physical-ghost reln. *)
  "%Heq_dig_hist" ∷ ⌜ gs_hist.*2 = servEpochInfo.dig <$> epochHist ⌝ ∗
  "%Heq_vers" ∷ ⌜ gs_vers = userState.numVers <$> userInfo ⌝ ∗
  "%Heq_keyM" ∷ ⌜ keyMap = lower_map (default ∅ (last gs_hist.*1)) ⌝ ∗
  "%Heq_map_hist" ∷ ([∗ list] ep ↦ x ∈ epochHist,
    ∃ prevM nextM,
    "%Hlook_prevM" ∷ ⌜ gs_hist.*1 !! (pred ep) = Some prevM ⌝ ∗
    "%Hlook_nextM" ∷ ⌜ gs_hist.*1 !! ep = Some nextM ⌝ ∗
    "%HupdM" ∷ ⌜ nextM = x.(servEpochInfo.updates) ∪ prevM ⌝).

Definition is_Server ptr serv : iProp Σ :=
  ∃ mu (sigSk_ptr vrfSk_ptr workQ : loc) sig_pk γ,
  "#Hinv_gs" ∷ inv nroot (inv_gs serv) ∗
  (* rwmutex has 1/2 physical ownership. other 1/2 owned by worker thread. *)
  "#mu" ∷ ptr ↦[Server :: "mu"]□ #mu ∗
  "#Hmu" ∷ is_rwlock nroot #mu (λ q, own_Server ptr serv (q / 2)) ∗
  "#sigSk" ∷ ptr ↦[Server :: "sigSk"]□ #sigSk_ptr ∗
  "#HsigSk" ∷ is_sig_sk sigSk_ptr sig_pk (serv_sigpred γ) ∗
  "#vrfSk" ∷ ptr ↦[Server :: "vrfSk"]□ #vrfSk_ptr ∗
  "#HvrfSk" ∷ is_vrf_sk vrfSk_ptr serv.(Server.vrf_pk) ∗
  "#Hptr_workq" ∷ ptr ↦[Server :: "workQ"]□ #workQ ∗
  "#workQ" ∷ is_WorkQ workQ.

Definition wish_checkMembHide vrf_pk uid ver dig memb_hide label : iProp Σ :=
  "#Hvrf_proof" ∷ is_vrf_proof vrf_pk (enc_label_pre uid ver) memb_hide.(MembHide.LabelProof) ∗
  "#Hvrf_out" ∷ is_vrf_out vrf_pk (enc_label_pre uid ver) label ∗
  "#Hmerk" ∷ wish_merkle_Verify true label
    memb_hide.(MembHide.MapVal) memb_hide.(MembHide.MerkleProof) dig.

Definition wish_checkMemb vrf_pk uid ver dig memb label commit : iProp Σ :=
  "#Hvrf_proof" ∷ is_vrf_proof vrf_pk (enc_label_pre uid ver) memb.(Memb.LabelProof) ∗
  "#Hvrf_out" ∷ is_vrf_out vrf_pk (enc_label_pre uid ver) label ∗
  "#Hcommit" ∷ is_hash (CommitOpen.encodesF memb.(Memb.PkOpen)) commit ∗
  "#Hmerk" ∷ wish_merkle_Verify true label
    (enc_val memb.(Memb.EpochAdded) commit)
    memb.(Memb.MerkleProof) dig.

Definition wish_checkNonMemb vrf_pk uid ver dig non_memb : iProp Σ :=
  ∃ label,
  "#Hvrf_proof" ∷ is_vrf_proof vrf_pk (enc_label_pre uid ver) non_memb.(NonMemb.LabelProof) ∗
  "#Hvrf_out" ∷ is_vrf_out vrf_pk (enc_label_pre uid ver) label ∗
  "#Hmerk" ∷ wish_merkle_Verify false label []
    non_memb.(NonMemb.MerkleProof) dig.

Lemma wp_Server__Put ptr serv uid nVers sl_pk (pk : list w8) cli_ep :
  {{{
    "#Hserv" ∷ is_Server ptr serv ∗
    "Hvers" ∷ uid ↪[serv.(Server.γvers)] nVers ∗
    "#Hsl_pk" ∷ own_slice_small sl_pk byteT DfracDiscarded pk ∗
    "#Hlb_ep" ∷ mono_nat_lb_own serv.(Server.γepoch) cli_ep
  }}}
  Server__Put #ptr #uid (slice_val sl_pk)
  {{{
    ptr_sigdig sigdig ptr_lat lat ptr_bound bound label commit,
    RET (#ptr_sigdig, #ptr_lat, #ptr_bound, #false);
    "Hvers" ∷ uid ↪[serv.(Server.γvers)] (word.add nVers (W64 1)) ∗
    "%Heq_ep" ∷ ⌜ sigdig.(SigDig.Epoch) = lat.(Memb.EpochAdded) ⌝ ∗
    "%Heq_pk" ∷ ⌜ pk = lat.(Memb.PkOpen).(CommitOpen.Val) ⌝ ∗
    "#Hlb_ep" ∷ mono_nat_lb_own serv.(Server.γepoch) (uint.nat sigdig.(SigDig.Epoch)) ∗
    "%Hlt_ep" ∷ ⌜ Z.of_nat cli_ep < uint.Z sigdig.(SigDig.Epoch) ⌝ ∗
    "#Hsigdig" ∷ SigDig.own ptr_sigdig sigdig DfracDiscarded ∗
    "#Hsig" ∷ is_sig serv.(Server.sig_pk)
      (PreSigDig.encodesF $ PreSigDig.mk sigdig.(SigDig.Epoch) sigdig.(SigDig.Dig))
      sigdig.(SigDig.Sig) ∗
    "Hlat" ∷ Memb.own ptr_lat lat (DfracOwn 1) ∗
    "#Hwish_lat" ∷ wish_checkMemb serv.(Server.vrf_pk) uid nVers
      sigdig.(SigDig.Dig) lat label commit ∗
    "Hbound" ∷ NonMemb.own ptr_bound bound (DfracOwn 1) ∗
    "#Hwish_bound" ∷ wish_checkNonMemb serv.(Server.vrf_pk)
      uid (word.add nVers (W64 1)) sigdig.(SigDig.Dig) bound
  }}}.
Proof.
  iIntros (?) "Hpre HΦ". iNamed "Hpre".
  wp_rec. wp_pures. wp_apply wp_allocStruct; [val_ty | ].
  iIntros (wq_ptr) "wq". wp_apply wp_allocStruct; [val_ty | ].
  iIntros (work_ptr) "work". wp_pures. iNamed "Hserv". wp_loadField.
  (* TODO: WorkQ spec *)
Admitted.

Lemma wp_getDig epochHist_sl epochHist_ptrs epochHist info q :
  last epochHist = Some info →
  {{{
        "HepochHist_sl" ∷ own_slice epochHist_sl ptrT (DfracOwn q) epochHist_ptrs ∗
        "#HepochHist_own" ∷ ([∗ list] l;x ∈ epochHist_ptrs;epochHist, servEpochInfo.is_own l x)
  }}}
    getDig (slice_val epochHist_sl)
  {{{
      (sigdig_ptr : loc), RET #sigdig_ptr;
        own_slice epochHist_sl ptrT (DfracOwn q) epochHist_ptrs ∗
        SigDig.own sigdig_ptr (SigDig.mk (W64 (length epochHist - 1))
                                 info.(servEpochInfo.dig)
                                 info.(servEpochInfo.sig))
          DfracDiscarded (* because of the slices *)
  }}}.
Proof.
  intros Hlast. iIntros (?) "Hpre HΦ". iNamed "Hpre".
  wp_rec. wp_apply wp_slice_len. iDestruct (own_slice_sz with "[$]") as %Hsz.
  wp_pures. iDestruct (own_slice_split_1 with "[$]") as "[Hsl ?]".
  iDestruct (big_sepL2_length with "[$]") as %Hlen_eq.
  rewrite last_lookup in Hlast.
  opose proof (lookup_lt_Some _ _ _ Hlast).
  iDestruct (big_sepL2_lookup_2_some with "[$]") as %[ptr Hlookup2]; [done|].

  wp_apply (wp_SliceGet with "[$Hsl]").
  { iPureIntro. replace (uint.nat _) with (Init.Nat.pred (length epochHist)) by word.
    eassumption. }
  iIntros "Hsl". wp_pures.
  iDestruct (big_sepL2_lookup with "[$]") as "H"; [eassumption.. | ].
  iNamed "H".
  wp_loadField. wp_loadField.
  iApply wp_fupd.
  wp_apply wp_allocStruct; [val_ty|].
  iIntros "* Hl". iApply "HΦ".
  iDestruct (struct_fields_split with "Hl") as "H". iNamed "H".
  iMod (struct_field_pointsto_persist with "Dig") as "#Dig".
  iMod (struct_field_pointsto_persist with "Sig") as "#Sig".
  iMod (struct_field_pointsto_persist with "Epoch") as "#Epoch".
  iModIntro.
  replace (w64_word_instance.(word.sub) epochHist_sl.(Slice.sz) (W64 1)) with
    (W64 (length epochHist - 1)) by word.
  iFrame "∗#".
Qed.

Lemma wp_Server__Get ptr serv uid cli_ep :
  {{{
    "#Hserv" ∷ is_Server ptr serv ∗
    "#Hlb_ep" ∷ mono_nat_lb_own serv.(Server.γepoch) cli_ep
  }}}
  Server__Get #ptr #uid
  {{{
    ptr_sigdig sigdig sl_hist ptr2_hist hist
    is_reg ptr_lat lat ptr_bound bound (nVers : w64),
    RET (#ptr_sigdig, slice_val sl_hist, #ptr_lat, #ptr_bound);
    "#Hlb_ep" ∷ mono_nat_lb_own serv.(Server.γepoch) (uint.nat sigdig.(SigDig.Epoch)) ∗
    "%Hlt_ep" ∷ ⌜ Z.of_nat cli_ep ≤ uint.Z sigdig.(SigDig.Epoch) ⌝ ∗
    "#Hsigdig" ∷ SigDig.own ptr_sigdig sigdig DfracDiscarded ∗
    "#Hsig" ∷ is_sig serv.(Server.sig_pk)
      (PreSigDig.encodesF $ PreSigDig.mk sigdig.(SigDig.Epoch) sigdig.(SigDig.Dig))
      sigdig.(SigDig.Sig) ∗
    "%Hlen_hist" ∷ ⌜ length hist = pred (uint.nat nVers) ⌝ ∗
    "Hhist" ∷ ([∗ list] l;x ∈ ptr2_hist;hist,
      MembHide.own l x (DfracOwn 1)) ∗
    "Hsl_hist" ∷ own_slice_small sl_hist ptrT (DfracOwn 1) ptr2_hist ∗
    "#Hwish_hist" ∷ ([∗ list] ver ↦ x ∈ hist,
      ∃ label,
      wish_checkMembHide serv.(Server.vrf_pk) uid (W64 ver)
        sigdig.(SigDig.Dig) x label) ∗
    "Hlat" ∷ Memb.own ptr_lat lat (DfracOwn 1) ∗
    "%Heq_is_reg" ∷ ⌜ is_reg = negb $ bool_decide (nVers = (W64 0)) ⌝ ∗
    "#Hwish_lat" ∷ (if negb is_reg then True else
      ∃ label commit,
      wish_checkMemb serv.(Server.vrf_pk) uid (word.sub nVers (W64 1))
        sigdig.(SigDig.Dig) lat label commit) ∗
    "Hbound" ∷ NonMemb.own ptr_bound bound (DfracOwn 1) ∗
    "#Hwish_bound" ∷ wish_checkNonMemb serv.(Server.vrf_pk) uid nVers
      sigdig.(SigDig.Dig) bound
  }}}.
Proof.
  iIntros (?) "Hpre HΦ". iNamed "Hpre". iNamed "Hserv".
  wp_rec. wp_pures. wp_loadField. wp_apply (read_wp_Mutex__Lock with "[$]").
  iIntros "Hown". iNamedSuffix "Hown" "_own". wp_pures.
  wp_loadField. wp_apply (wp_MapGet with "[$]"). iIntros "%userState_ptr %ok [%Hlookup H1_own]".
  wp_pures. wp_apply wp_ref_of_zero; [done | ]. iIntros "%numVers_ptr numVers".
  wp_pures. wp_apply wp_ref_of_zero; [done | ]. iIntros "%plainPk plainPk".
  wp_pures.
  (* TODO: optional if. *)
  wp_if_destruct.
  2:{
    admit.
  }
  destruct ok.
  2:{ exfalso. apply map_get_false in Hlookup. naive_solver. }
  apply map_get_true in Hlookup.
  iDestruct (big_sepM2_lookup_l_some with "[$]") as "%H".
  { eassumption. }
  destruct H as [userState Hlookup2].
  iDestruct (big_sepM2_lookup_acc with "[$]") as "[Huinfo Huinfo_own]"; [eassumption.. | ].
  iNamedSuffix "Huinfo" "_uinfo".
  wp_loadField. wp_store. wp_loadField. wp_store.
  wp_pures.
  iCombineNamed "*_uinfo" as "Huinfo".
  iDestruct ("Huinfo_own" with "[Huinfo]") as "Huinfo_own".
  { iNamed "Huinfo". iFrame "∗#". }
  wp_loadField. wp_apply (wp_getDig with "[$]").
  { admit. } (* FIXME: maintain that epochHistory is non-empty *)
  iIntros (?) "[H2_own #?]". wp_pures.
  wp_loadField. wp_load. wp_loadField.
  (* TODO: wp_getHist *)
Admitted.

Lemma wp_Server__SelfMon ptr serv uid nVers cli_ep :
  {{{
    "#Hserv" ∷ is_Server ptr serv ∗
    "Hvers" ∷ uid ↪[serv.(Server.γvers)] nVers ∗
    "#Hlb_ep" ∷ mono_nat_lb_own serv.(Server.γepoch) cli_ep
  }}}
  Server__SelfMon #ptr #uid
  {{{
    ptr_sigdig sigdig ptr_bound bound,
    RET (#ptr_sigdig, #ptr_bound);
    "Hvers" ∷ uid ↪[serv.(Server.γvers)] nVers ∗
    "#Hlb_ep" ∷ mono_nat_lb_own serv.(Server.γepoch) (uint.nat sigdig.(SigDig.Epoch)) ∗
    "%Hlt_ep" ∷ ⌜ Z.of_nat cli_ep ≤ uint.Z sigdig.(SigDig.Epoch) ⌝ ∗
    "#Hsigdig" ∷ SigDig.own ptr_sigdig sigdig DfracDiscarded ∗
    "#Hsig" ∷ is_sig serv.(Server.sig_pk)
      (PreSigDig.encodesF $ PreSigDig.mk sigdig.(SigDig.Epoch) sigdig.(SigDig.Dig))
      sigdig.(SigDig.Sig) ∗
    "Hbound" ∷ NonMemb.own ptr_bound bound (DfracOwn 1) ∗
    "#Hwish_bound" ∷ wish_checkNonMemb serv.(Server.vrf_pk) uid nVers
      sigdig.(SigDig.Dig) bound
  }}}.
Proof. Admitted.

(* NOTE: hard to prove that client.Audit never errors,
unless assume that Auditor up-to-date thru client's epoch. *)
Lemma wp_Server__Audit ptr serv (ep : w64) :
  let wish := (mono_nat_lb_own serv.(Server.γepoch) (uint.nat ep) : iProp Σ) in
  {{{
    "#Hserv" ∷ is_Server ptr serv
  }}}
  Server__Audit #ptr #ep
  {{{
    ptr_upd upd upd_dec err, RET (#ptr_upd, #err);
    "Hgenie" ∷ (⌜ err = false ⌝ ∗-∗ wish) ∗
    "Herr" ∷ (wish -∗
      ∃ gs_hist prevH nextH,
      "#Hupd" ∷ UpdateProof.own ptr_upd upd DfracDiscarded ∗
      "%Heq_upd_dec" ∷ ⌜ upd.(UpdateProof.Updates) =
        (λ x, MapValPre.encodesF $ MapValPre.mk x.1 x.2) <$> upd_dec ⌝ ∗
      "#Hlb_hist" ∷ mono_list_lb_own serv.(Server.γhist) gs_hist ∗
      "%Hlook_prevH" ∷ ⌜ gs_hist !! (pred $ uint.nat ep) = Some prevH ⌝ ∗
      "%Hlook_nextH" ∷ ⌜ gs_hist !! (uint.nat ep) = Some nextH ⌝ ∗
      "#Hsig" ∷ is_sig serv.(Server.sig_pk)
        (PreSigDig.encodesF $ PreSigDig.mk ep nextH.2)
        upd.(UpdateProof.Sig) ∗
      "%HupdM" ∷ ⌜ nextH.1 = upd_dec ∪ prevH.1 ⌝)
  }}}.
Proof. Admitted.

Lemma wp_compMapVal (epoch : w64) ptr_pk_open pk_open d0 :
  {{{
    "Hown_pk_open" ∷ CommitOpen.own ptr_pk_open pk_open d0
  }}}
  compMapVal #epoch #ptr_pk_open
  {{{
    sl_map_val commit, RET (slice_val sl_map_val);
    "Hown_pk_open" ∷ CommitOpen.own ptr_pk_open pk_open d0 ∗
    "#Hcommit" ∷ is_hash (CommitOpen.encodesF pk_open) commit ∗
    "Hsl_map_val" ∷ own_slice_small sl_map_val byteT (DfracOwn 1)
      (enc_val epoch commit)
  }}}.
Proof.
  iIntros (Φ) "H HΦ". iNamed "H". wp_rec.
  iNamed"Hown_pk_open". wp_loadField.
  wp_apply wp_slice_len.
  wp_apply wp_NewSliceWithCap; [word|]. iIntros "* Hsl_enc".
  destruct pk_open. simpl.
  wp_apply (CommitOpen.wp_enc _ _ _ (CommitOpen.mk _ _)
    with "[$Hsl_enc $Hsl_val $Hptr_val $Hsl_rand $Hptr_rand]").
  iIntros "*". iNamedSuffix 1 "_open". simpl.
  iDestruct (own_slice_to_small with "Hsl_enc_open") as "Hsl_enc_open".
  wp_apply (wp_Hash with "[$Hsl_enc_open]"). iIntros "*". iNamed 1.
  wp_apply wp_allocStruct; [val_ty|]. iIntros "* H".
  iDestruct (struct_fields_split with "H") as "H". iNamed "H".
  wp_apply wp_NewSliceWithCap; [word|]. iIntros "* Hsl_enc".
  iDestruct (own_slice_to_small with "Hsl_hash") as "Hsl_hash".
  wp_apply (MapValPre.wp_enc (MapValPre.mk _ _) with "[$Hsl_enc $Epoch $PkCommit $Hsl_hash]").
  iIntros "*". iNamedSuffix 1 "_mapval". simpl.
  iDestruct (own_slice_to_small with "Hsl_b_mapval") as "Hsl_b_mapval".
  replace (uint.nat (W64 0)) with (0%nat); [|word].
  destruct Henc_mapval. subst.
  iApply "HΦ". iFrame "∗#".
Qed.

End proof.
