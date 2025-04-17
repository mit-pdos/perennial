From New.experiments Require Import glob.
From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.pav Require Import kt.

From Perennial.goose_lang.lib Require Import waitgroup.waitgroup.
From Perennial.program_proof.pav Require Import prelude core cryptoffi cryptoutil serde merkle logical_audit workq.
From Perennial.goose_lang.lib.rwlock Require Import rwlock_noncrash.
Import RecordSetNotations.

Module WQReq.
Record t :=
  mk {
      Uid : w64;
      Pk : list w8;
    }.

Section defs.
Context `{!heapGS Σ}.

Definition is_own ptr x : iProp Σ :=
  ∃ Pk_sl,
  "Uid" ∷ ptr ↦[WQReq :: "Uid"]□ #x.(Uid) ∗
  "Pk" ∷ ptr ↦[WQReq:: "Pk"]□ (slice_val Pk_sl) ∗
  "Pk_sl" ∷ own_slice_small Pk_sl byteT DfracDiscarded x.(Pk).

Lemma inj ptr x1 x2 :
  is_own ptr x1 -∗
  is_own ptr x2 -∗ ⌜ x1 = x2 ⌝.
Proof.
  iNamed 1. iNamedSuffix 1 "2".
  destruct x1, x2.
  iDestruct (struct_field_pointsto_agree with "Uid Uid2") as %Heq. simplify_eq.
  iDestruct (struct_field_pointsto_agree with "Pk Pk2") as %Heq. rewrite Heq.
  simplify_eq. destruct Pk_sl, Pk_sl0. simpl in *. subst.
  iDestruct (own_slice_small_agree with "[$] [$]") as %->. done.
Qed.
End defs.
End WQReq.

Module WQResp.
Record t :=
  mk {
      Dig : SigDig.t;
      Lat : Memb.t;
      Bound : NonMemb.t;
      Err : bool
    }.

Section defs.
Context `{!heapGS Σ}.

Definition is_own ptr x : iProp Σ :=
  ∃ (dig_ptr lat_ptr bound_ptr : loc),
    "Dig" ∷ ptr ↦[WQResp::"Dig"]□ #dig_ptr ∗
    "HDig" ∷ SigDig.own dig_ptr x.(Dig) DfracDiscarded ∗
    "Lat" ∷ ptr ↦[WQResp::"Lat"]□ #lat_ptr ∗
    "HLat" ∷ Memb.own lat_ptr x.(Lat) DfracDiscarded ∗
    "Bound" ∷ ptr ↦[WQResp::"Bound"]□ #bound_ptr ∗
    "HBound" ∷ NonMemb.own bound_ptr x.(Bound) DfracDiscarded ∗
    "Err" ∷ ptr ↦[WQResp::"Err"]□ #x.(Err).

End defs.

End WQResp.

Module mapper0Out.
Record t :=
  mk {
      latestVrfHash : list w8;
      latestVrfProof : list w8;
      boundVrfHash : list w8;
      boundVrfProof : list w8;
      mapVal : list w8;
      pkOpen : CommitOpen.t;
    }.

Section defs.
Context `{!heapGS Σ}.
Definition is_own ptr x : iProp Σ :=
  ∃ (latestVrfHash_sl latestVrfProof_sl boundVrfHash_sl boundVrfProof_sl mapVal_sl : Slice.t)
    (pkOpen_ptr : loc),
  "#latestVrfHash" ∷ ptr ↦[mapper0Out::"latestVrfHash"]□ (slice_val latestVrfHash_sl) ∗
  "#latestVrfHash_sl" ∷ own_slice_small latestVrfHash_sl byteT DfracDiscarded x.(latestVrfHash) ∗
  "#latestVrfProof" ∷ ptr ↦[mapper0Out::"latestVrfProof"]□ (slice_val latestVrfProof_sl) ∗
  "#latestVrfProof_sl" ∷ own_slice_small latestVrfProof_sl byteT DfracDiscarded x.(latestVrfProof) ∗
  "#boundVrfHash" ∷ ptr ↦[mapper0Out::"boundVrfHash"]□ (slice_val boundVrfHash_sl) ∗
  "#boundVrfHash_sl" ∷ own_slice_small boundVrfHash_sl byteT DfracDiscarded x.(boundVrfHash) ∗
  "eboundVrfProof" ∷ ptr ↦[mapper0Out::"boundVrfProof"]□ (slice_val boundVrfProof_sl) ∗
  "#boundVrfProof_sl" ∷ own_slice_small boundVrfProof_sl byteT DfracDiscarded x.(boundVrfProof) ∗
  "#mapVal" ∷ ptr ↦[mapper0Out::"mapVal"]□ (slice_val mapVal_sl) ∗
  "#mapVal_sl" ∷ own_slice_small mapVal_sl byteT DfracDiscarded x.(mapVal) ∗
  "#pkOpen" ∷ ptr ↦[mapper0Out::"pkOpen"]□ #pkOpen_ptr ∗
  "#HpkOpen" ∷ CommitOpen.own pkOpen_ptr x.(pkOpen) DfracDiscarded.

End defs.
End mapper0Out.

Module userState.
Record t :=
  mk {
    numVers: w64;
    plainPk: list w8;
  }.

Section defs.
Context `{!heapGS Σ}.

Definition own ptr x d : iProp Σ :=
  ∃ plainPk_sl,
  "numVers" ∷ ptr ↦[userState :: "numVers"]{d} #x.(numVers) ∗
  "plainPk" ∷ ptr ↦[userState :: "plainPk"]{d} (slice_val plainPk_sl) ∗
  "#plainPk_sl" ∷ own_slice_small plainPk_sl byteT DfracDiscarded x.(plainPk).
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
Context `{!heapGS Σ}.

Definition is_own ptr x : iProp Σ :=
  ∃ (updates_ptr : loc) updates_phys dig_sl sig_sl,
  "#updates" ∷ ptr ↦[servEpochInfo :: "updates"]□ #updates_ptr ∗
  "#updates_map" ∷ own_map updates_ptr DfracDiscarded updates_phys ∗
  "#updates_sl" ∷ ([∗ map] sl;y ∈ updates_phys;x.(updates),
                     own_slice_small sl byteT DfracDiscarded
                       (MapValPre.encodesF $ MapValPre.mk y.1 y.2)) ∗
  "#dig" ∷ ptr ↦[servEpochInfo :: "dig"]□ (slice_val dig_sl) ∗
  "#dig_sl" ∷ own_slice_small dig_sl byteT DfracDiscarded x.(dig) ∗
  "#sig" ∷ ptr ↦[servEpochInfo :: "sig"]□ (slice_val sig_sl) ∗
  "#sig_sl" ∷ own_slice_small sig_sl byteT DfracDiscarded x.(sig).

Global Instance pers ptr x : Persistent (is_own ptr x) := _.
End defs.

End servEpochInfo.

Module Server.
Record t :=
  mk {
      keyMap : gmap (list w8) (list w8);
      userInfo : gmap w64 userState.t;
      epochHist : list servEpochInfo.t;
  }.

Global Instance : Settable _ :=
  settable! mk <keyMap; userInfo; epochHist>.

Section defs.
Context `{!heapGS Σ}.
Definition own_phys ptr q s : iProp Σ :=
  ∃ epochHist_sl (userInfo_ptr keyMap_ptr : loc) userInfo_phys epochHist_ptrs,
  "epochHist" ∷ ptr ↦[Server :: "epochHist"]{DfracOwn q} (slice_val epochHist_sl) ∗
  "userInfo" ∷ ptr ↦[Server :: "userInfo"] #userInfo_ptr ∗
  "keyMap" ∷ ptr ↦[Server :: "keyMap"] #keyMap_ptr ∗

  "HkeyMap" ∷ own_Tree keyMap_ptr s.(keyMap) (DfracOwn q) ∗
  "HuserInfo_map" ∷ own_map userInfo_ptr (DfracOwn q) userInfo_phys ∗
  "HuserInfo_own" ∷ ([∗ map] l;x ∈ userInfo_phys; s.(userInfo), userState.own l x (DfracOwn q)) ∗
  "HepochHist_sl" ∷ own_slice epochHist_sl ptrT (DfracOwn q) epochHist_ptrs ∗
  "#HepochHist_is" ∷ ([∗ list] l;x ∈ epochHist_ptrs; s.(epochHist), servEpochInfo.is_own l x).

Lemma split q1 q2 ptr s :
  own_phys ptr (q1 + q2) s -∗
  own_phys ptr q1 s ∗
  own_phys ptr q2 s.
Proof.
  iNamed 1. iFrame.
  iDestruct "HkeyMap" as "[? ?]".
  iDestruct "epochHist" as "[? ?]". iFrame.
  iDestruct "HepochHist_sl" as "[? ?]".
  (* FIXME: fractional own_map, userState.own, own_slice *)
Admitted.

Lemma combine q1 q2 ptr s1 s2 :
  own_phys ptr q1 s1 -∗
  own_phys ptr q2 s2 -∗
  ⌜ s1 = s2 ⌝ ∗
  own_phys ptr (q1 + q2) s1.
Proof.
  iNamedSuffix 1 "1". iNamedSuffix 1 "2". iFrame.
Admitted.

End defs.
End Server.

Section proof.
Context `{!heapGS Σ, !pavG Σ}.

Record Server_names :=
  {
    auditor_gn : gname;
    ver_gn : gname;
    sig_pk : list w8;
    vrf_pk : list w8;
    commitSecret : list w8;
  }.

Implicit Types γ : Server_names.

Definition own_num_vers γ (uid : w64) (num_vers : w64) : iProp Σ :=
  uid ↪[γ.(ver_gn)] num_vers.

Definition encode_uid_ver uid_ver :=
  (MapLabelPre.encodesF $ MapLabelPre.mk uid_ver.1 uid_ver.2).

(* Abstraction relation between the map in the merkle tree (which has hidden
   labels and pks) and a map from (uid,ver) pairs to (epoch,pk). *)
Definition is_map_relation γ (mₗ : gmap (list w8) (list w8))
  (mₕ : gmap (uid_ty * ver_ty) (epoch_ty * pk_ty)) : iProp Σ :=
  (* A (uid_ver, epoch_pk) pair is in the abstract map iff a corresponding
     hidden element is in the physical map *)
  □(∀ uid_ver,
      match mₕ !! uid_ver with
      | Some epoch_pk =>
          (∃ label rand commit,
              is_vrf_out γ.(vrf_pk) (encode_uid_ver uid_ver) label ∗
              is_hash (γ.(commitSecret) ++ label) rand ∗
              is_hash (CommitOpen.encodesF (CommitOpen.mk epoch_pk.2 rand)) commit ∗
              ⌜ mₗ !! label = Some (MapValPre.encodesF $ MapValPre.mk epoch_pk.1 commit) ⌝)
      | None =>
          ∀ label, is_vrf_out γ.(vrf_pk) (encode_uid_ver uid_ver) label -∗
                   ⌜ mₗ !! label = None ⌝
    end
    ).

Instance is_map_relation_pers γ mₗ mₕ : Persistent (is_map_relation γ mₗ mₕ) := _.

Definition gauge_eq (m1 m2 : gmap w64 w64) :=
  ∀ k, default (W64 0) (m1 !! k) = default (W64 0) (m2 !! k).

Definition own_Server_nvers γ q st : iProp Σ :=
  ∃ numVersMap,
  "Hnvers" ∷ ghost_map_auth γ.(ver_gn) q numVersMap ∗
  "%Hgauge" ∷ ⌜ gauge_eq numVersMap (userState.numVers <$> st.(Server.userInfo)) ⌝
.

Definition own_Server_hist γ q st : iProp Σ :=
  ∃ gs,
  (* Copied from auditor.v *)
  "Hauditor" ∷ mono_list_auth_own γ.(auditor_gn) q gs ∗
  (* Technically could rely on [is_sig] and [is_sigpred] to conclude this. *)
  "#Hinv_gs" ∷ audit_gs_inv gs ∗

  "%HkeyMap_ghost" ∷ ⌜ map_lower (default ∅ (last gs.*1)) st.(Server.keyMap) ⌝ ∗
  "%Hdigs_gs" ∷ ⌜ gs.*2 = servEpochInfo.dig <$> st.(Server.epochHist) ⌝ ∗

  "%HepochHistNoOverflow" ∷ ⌜ length st.(Server.epochHist) = uint.nat (length st.(Server.epochHist)) ⌝.

(** Invariants and cryptographic knowledge related to mutable Server state. *)
Definition is_Server_crypto γ st : iProp Σ :=
  ∃ openKeyMap last_info,

  (* logically maintain the digest *)
  "#Hdig" ∷ is_merkle_map st.(Server.keyMap) last_info.(servEpochInfo.dig) ∗

  (* abstract away the cryptographically private aspect of keyMap *)
  "#HkeyMap" ∷ is_map_relation γ st.(Server.keyMap) openKeyMap ∗
  "%HkeyMapLatest" ∷ (⌜ ∀ uid,
                        match st.(Server.userInfo) !! uid with
                        | Some (userState.mk numVers pk) =>
                            snd <$> openKeyMap !! (uid, (word.sub numVers (W64 1))) = Some pk ∧
                            (∀ ver, (uid, ver) ∈ dom openKeyMap ↔ uint.nat ver < uint.nat numVers)
                        | None => (∀ ver, (uid, ver) ∉ dom openKeyMap)
                        end ⌝
    ) ∗

   (* Everything in epochHist is signed; could make this a crypto property of [servEpochInfo]. *)
  "#HepochHist" ∷
    □(∀ epoch info,
        ⌜ st.(Server.epochHist) !! (uint.nat epoch) = Some info ⌝ →
        is_sig γ.(sig_pk) (PreSigDig.encodesF $ PreSigDig.mk epoch info.(servEpochInfo.dig))
          info.(servEpochInfo.sig)
    ) ∗

  (* The current keyMap is computed from applying updates *)
  "%HepochHistUpdates" ∷ (⌜ st.(Server.keyMap) =
                          (λ v, MapValPre.encodesF (MapValPre.mk v.1 v.2)) <$>
                            (foldl (λ a b, union b a) (∅ : gmap _ _)
                               (servEpochInfo.updates <$> st.(Server.epochHist)))
                            ⌝) ∗

  "%HepochHistLast" ∷ ⌜ last st.(Server.epochHist) = Some last_info ⌝
.

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

(** Proposition guarded by RWMutex. *)
Definition own_Server γ s q : iProp Σ :=
  ∃ (st : Server.t),
    "Hphys" ∷ Server.own_phys s (q/2) st ∗
    "#Hcrypto" ∷ is_Server_crypto γ st ∗
    "Hghost" ∷ own_Server_hist γ q st ∗
    "Hnvers" ∷ own_Server_nvers γ q st.

Definition is_epoch_lb γ (epoch : w64) : iProp Σ :=
  ∃ (gs : list (gmap (list w8) (w64 * list w8) * list w8)),
    mono_list_lb_own γ.(auditor_gn) gs ∗ ⌜ uint.nat epoch + 1 ≤ length gs ⌝.

Definition wq_post γ req (nVers cli_next_ep : w64) Φ : iProp Σ :=
  (∀ (resp ptr_sigdig : loc) sigdig (ptr_lat : loc) lat (ptr_bound : loc) bound label commit,
     let new_next_ep := word.add sigdig.(SigDig.Epoch) (W64 1) in
     ("Dig" ∷ resp ↦[WQResp::"Dig"] #ptr_sigdig ∗
      "Lat" ∷ resp ↦[WQResp::"Lat"] #ptr_lat ∗
      "Bound" ∷ resp ↦[WQResp::"Bound"] #ptr_bound ∗
      "Err" ∷ resp ↦[WQResp::"Err"] #false ∗
      "Hvers" ∷ own_num_vers γ req.(WQReq.Uid) (word.add nVers (W64 1)) ∗

      "%Heq_ep" ∷ ⌜ sigdig.(SigDig.Epoch) = lat.(Memb.EpochAdded) ⌝ ∗
      "%Heq_pk" ∷ ⌜ lat.(Memb.PkOpen).(CommitOpen.Val) = req.(WQReq.Pk) ⌝ ∗
      "#Hlb_ep" ∷ is_epoch_lb γ new_next_ep ∗
      "%Hlt_ep" ∷ ⌜ uint.Z cli_next_ep < uint.Z new_next_ep ⌝ ∗
      (* provable from new_next_ep = the w64 size of epochHist slice. *)
      "%Hnoof_ep" ∷ ⌜ uint.Z new_next_ep = (uint.Z sigdig.(SigDig.Epoch) + 1)%Z ⌝ ∗

      "#Hsigdig" ∷ SigDig.own ptr_sigdig sigdig DfracDiscarded ∗
      "#Hsig" ∷ is_sig γ.(sig_pk)
                           (PreSigDig.encodesF $ PreSigDig.mk sigdig.(SigDig.Epoch) sigdig.(SigDig.Dig))
                           sigdig.(SigDig.Sig) ∗

      "Hlat" ∷ Memb.own ptr_lat lat (DfracOwn 1) ∗
      "#Hwish_lat" ∷ wish_checkMemb γ.(vrf_pk) req.(WQReq.Uid) nVers
                                                     sigdig.(SigDig.Dig) lat label commit ∗

      "Hbound" ∷ NonMemb.own ptr_bound bound (DfracOwn 1) ∗
      "#Hwish_bound" ∷ wish_checkNonMemb γ.(vrf_pk) req.(WQReq.Uid) (word.add nVers (W64 1)) sigdig.(SigDig.Dig) bound
     )
     -∗ Φ resp
  ).

Definition wq_spec γ (req_ptr : loc) (Φ : loc → iProp Σ) : iProp Σ :=
  ∃ req,
    "#Req" ∷ WQReq.is_own req_ptr req ∗
    (∃ nVers cli_next_ep,
    "Hvers" ∷ own_num_vers γ req.(WQReq.Uid) nVers ∗
    "#Hlb_ep" ∷ is_epoch_lb γ cli_next_ep ∗
    "HΨ" ∷ wq_post γ req nVers cli_next_ep Φ).

(* FIXME: for workqG *)
Context `{!ghost_varG Σ unit}.
Definition is_Server γ s : iProp Σ :=
  ∃ commitSecret_sl (mu vrfSk_ptr workQ sigSk : loc),
  "#commitSecret" ∷ s ↦[Server :: "commitSecret"]□ (slice_val commitSecret_sl) ∗
  "#commitSecret_sl" ∷ own_slice_small commitSecret_sl byteT DfracDiscarded γ.(commitSecret) ∗
  "#mu" ∷ s ↦[Server :: "mu"]□ #mu ∗
  "#Hmu" ∷ is_rwlock nroot #mu (λ q, own_Server γ s q) ∗
  "#vrfSk" ∷ s ↦[Server :: "vrfSk"]□ #vrfSk_ptr ∗
  "#HvrfSk" ∷ is_vrf_sk vrfSk_ptr γ.(vrf_pk) ∗
  "#workQ" ∷ s ↦[Server :: "workQ"]□ #workQ ∗
  "#HworkQ" ∷ is_WorkQ workQ (wq_spec γ) ∗
  "sigSk" ∷ s ↦[Server::"sigSk"]□ #sigSk ∗
  "#HsigSk" ∷ is_sig_sk sigSk γ.(sig_pk) (sigpred γ.(auditor_gn)) ∗
  "_" ∷ True.

Lemma wp_getDig γ st epochHist_sl epochHist_ptrs q :
  let info := last st.(Server.epochHist) in
  {{{
        "HepochHist_sl" ∷ own_slice epochHist_sl ptrT (DfracOwn q) epochHist_ptrs ∗
        "#HepochHist_own" ∷ ([∗ list] l;x ∈ epochHist_ptrs; st.(Server.epochHist), servEpochInfo.is_own l x) ∗
        "Hcrypto" ∷ is_Server_crypto γ st
  }}}
    getDig (slice_val epochHist_sl)
  {{{
      (sigdig_ptr : loc), RET #sigdig_ptr;
        let sigdig := (SigDig.mk (W64 (length st.(Server.epochHist) - 1))
                                 (default [] (servEpochInfo.dig <$> info))
                                 (default [] (servEpochInfo.sig <$> info))) in
        "HepochHist_sl" ∷ own_slice epochHist_sl ptrT (DfracOwn q) epochHist_ptrs ∗
        "Hsigdig" ∷ SigDig.own sigdig_ptr sigdig DfracDiscarded (* because of the slices *) ∗
        "#Hsig" ∷ is_sig γ.(sig_pk) (PreSigDig.encodesF $ PreSigDig.mk sigdig.(SigDig.Epoch) sigdig.(SigDig.Dig))
          sigdig.(SigDig.Sig)
  }}}.
Proof.
  intros ?. subst info. iIntros (?) "Hpre HΦ". iNamed "Hpre".
  wp_rec. wp_apply wp_slice_len. iDestruct (own_slice_sz with "[$]") as %Hsz.
  wp_pures. iDestruct (own_slice_split_1 with "[$]") as "[Hsl ?]".
  iDestruct (big_sepL2_length with "[$]") as %Hlen_eq.
  iNamed "Hcrypto".
  rewrite HepochHistLast.
  rewrite last_lookup in HepochHistLast.
  opose proof (lookup_lt_Some _ _ _ HepochHistLast).
  iDestruct (big_sepL2_lookup_2_some with "[$]") as %[ptr Hlookup2]; [done|].

  wp_apply (wp_SliceGet with "[$Hsl]").
  { iPureIntro. replace (uint.nat _) with (Init.Nat.pred (length st.(Server.epochHist))) by word.
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
    (W64 (length st.(Server.epochHist) - 1)) by word.
  iFrame "∗#". iApply "HepochHist". iPureIntro. simpl.
  rewrite -HepochHistLast. f_equal. word.
Qed.

Lemma wp_compMapLabel (uid ver : w64) (sk_ptr : loc) pk :
  {{{ is_vrf_sk sk_ptr pk }}}
    compMapLabel #uid #ver #sk_ptr
  {{{
      out out_sl proof proof_sl, RET (slice_val out_sl, slice_val proof_sl);
      "Hout_sl" ∷ own_slice_small out_sl byteT (DfracOwn 1) out ∗
      "Hproof_sl" ∷ own_slice_small proof_sl byteT (DfracOwn 1) proof ∗
      "#Hvrf_out" ∷ is_vrf_out pk (enc_label_pre uid ver) out ∗
      "#Hvrf_proof" ∷ is_vrf_proof pk (enc_label_pre uid ver) proof
  }}}.
Proof.
  iIntros (?) "Hsk HΦ". wp_rec. wp_pures.
  wp_apply wp_allocStruct; [val_ty | ].
  iIntros (?) "Hl". iDestruct (struct_fields_split with "Hl") as "Hl".
  iNamed "Hl". wp_pures. wp_apply wp_NewSliceWithCap; [word | ].
  iIntros (?) "Hsl". wp_apply (MapLabelPre.wp_enc with "[$Hsl Uid Ver]").
  { instantiate (2:=ltac:(econstructor)). iFrame. }
  iIntros "*". iNamed 1. wp_pures.
  iDestruct (own_slice_to_small with "[$]") as "?".
  wp_apply (wp_VrfPrivateKey__Prove with "[$]").
  iIntros "*". iNamed 1. iApply "HΦ". rewrite replicate_0. iFrame "∗#".
  rewrite Henc. simpl. iFrame "#".
Qed.

Lemma wp_getHist γ st keyMap_ptr dq uid (numVers : w64) vrfSk :
  {{{
      "Htree" ∷ own_Tree keyMap_ptr st.(Server.keyMap) dq ∗
      "#HvrfSk" ∷ is_vrf_sk vrfSk γ.(vrf_pk) ∗
      "#Hcrypto" ∷ is_Server_crypto γ st ∗
      "%HnumVers" ∷ ⌜ numVers = default (W64 0) (userState.numVers <$> st.(Server.userInfo) !! uid) ⌝
  }}}
    getHist #keyMap_ptr #uid #numVers #vrfSk
  {{{
      hist hist_ptrs hist_sl, RET (slice_val hist_sl);
      "Htree" ∷ own_Tree keyMap_ptr st.(Server.keyMap) dq ∗
      "Hhist_sl" ∷ own_slice_small hist_sl ptrT (DfracOwn 1) hist_ptrs ∗
      "Hhist" ∷ ([∗ list] l; mh ∈ hist_ptrs; hist, MembHide.own l mh (DfracOwn 1)) ∗
      "%Hlen_hist" ∷ ⌜ length hist = pred (uint.nat numVers) ⌝ ∗
      "#Hwish_hist" ∷
        ([∗ list] ver ↦ x ∈ hist,
           ∃ label, wish_checkMembHide γ.(vrf_pk) uid (W64 ver)
                      (default [] (servEpochInfo.dig <$> last st.(Server.epochHist))) x label)
  }}}.
Proof.
  iIntros (?) "Hpre HΦ". iNamed "Hpre". subst. iNamed "Hcrypto".
  rewrite HepochHistLast /=.
  wp_rec. wp_pures. wp_if_destruct.
  { (* numVers = 0 *)
    rewrite Heqb.
    replace (slice.nil) with (slice_val Slice.nil) by done. iApply "HΦ".
    iFrame.
    iDestruct (own_slice_small_nil) as "$".
    { done. }
    instantiate (1:=[]).
    rewrite big_sepL2_nil.
    iSplitR; first done.
    iSplitR; first done.
    iModIntro. rewrite big_sepL_nil. done.
  }
  wp_pures.
  wp_apply wp_NewSliceWithCap.
  { word. }
  iIntros (?) "Hhist_sl".
  wp_apply wp_ref_to; [val_ty|].
  iIntros (hist_ptr) "hist_ptr". wp_pures.
  wp_apply wp_ref_to; [val_ty|].
  iIntros (ver_ptr) "ver_ptr". wp_pures.

  specialize (HkeyMapLatest uid).
  destruct lookup eqn:Hlookup2 in Heqb, HkeyMapLatest.
  2:{ exfalso. simpl in *. word. }
  destruct t as [numVers ?]. simpl in Heqb.
  destruct HkeyMapLatest as [HplainPk Hintree].

  iAssert (
      ∃ hist_sl hist (ver : w64) hist_ptrs,
        "hist_ptr" ∷ hist_ptr ↦[slice.T ptrT] (slice_val hist_sl) ∗
        "ver_ptr" ∷ ver_ptr ↦[uint64T] #ver ∗
        "Hhist_sl" ∷ own_slice hist_sl ptrT (DfracOwn 1) hist_ptrs ∗
        "Hhist" ∷ ([∗ list] l; mh ∈ hist_ptrs; hist, MembHide.own l mh (DfracOwn 1)) ∗
        "%Hlen_hist" ∷ ⌜ length hist = (uint.nat ver) ⌝ ∗
        "%Hver_le" ∷ ⌜ (uint.Z ver ≤ uint.Z numVers - 1) ⌝ ∗
        "#Hwish_hist" ∷
          □ ([∗ list] ver ↦ x ∈ hist,
              ∃ label, wish_checkMembHide γ.(vrf_pk) uid (W64 ver)
                                              (default [] (servEpochInfo.dig <$> last st.(Server.epochHist)))
                                              x label)
    )%I with "[Hhist_sl ver_ptr hist_ptr]" as "Hloop".
  {
    rewrite replicate_0.
    iFrame. iExists [].
    rewrite big_sepL2_nil. iSplit; first done.
    iSplit; first done. iSplit; first word. iModIntro. done.
  }
  wp_forBreak_cond.
  clear ptr.
  iNamed "Hloop".
  rewrite HepochHistLast /=.
  wp_load. wp_pures. rewrite Hlookup2 /=. wp_if_destruct.
  { (* run a loop iteration *)
    wp_pures. wp_load.
    wp_apply (wp_compMapLabel with "[$]").
    iIntros "*". iNamed 1.
    wp_pures.
    wp_apply (wp_Tree__Prove with "[$Htree $Hout_sl]").
    iIntros "*". iNamed 1. wp_pures.
    destruct in_tree.
    2:{
      iExFalso.
      specialize (Hintree ver) as [_ Hintree].
      specialize (Hintree ltac:(word)).
      rewrite elem_of_dom in Hintree.
      destruct Hintree as [epoch_pk Hintree].
      iSpecialize ("HkeyMap" $! (uid, ver)). rewrite Hintree.
      iDestruct "HkeyMap" as (???) "(#Hvrf & Hrand & Hcommit & %Hlookup)".
      iDestruct (is_vrf_out_det with "Hvrf Hvrf_out") as "%". subst.
      rewrite Hlook_elems in Hlookup. discriminate Hlookup.
    }
    wp_apply std_proof.wp_Assert; first done.
    wp_pures.
    wp_apply wp_allocStruct; [val_ty|].
    iIntros (mh_ptr) "Hmh".
    wp_load. wp_apply (wp_SliceAppend with "[$Hhist_sl]").
    rename hist_sl into old_hist_sl.
    iIntros (hist_sl) "Hhist_sl". wp_store.
    wp_load. wp_store.
    iPersist "Hsl_proof".
    iAssert (MembHide.own mh_ptr ltac:(econstructor) (DfracOwn 1)) with "[Hmh Hproof_sl]" as "Hmh".
    {
      iDestruct (struct_fields_split with "Hmh") as "H". iNamed "H".
      iFrame "∗#".
    }
    iDestruct (big_sepL2_snoc with "[$Hhist $Hmh]") as "Hhist".
    iLeft. iModIntro. iSplitR; first done.
    iFrame.
    iSplitR; first iPureIntro.
    { rewrite length_app. simpl. word. }
    iSplitR; first word.
    iDestruct (is_merkle_map_det with "His_dig Hdig") as %Heq. subst.
    iModIntro.
    rewrite big_sepL_app. iFrame "Hwish_hist".
    simpl. iSplitL; last done. iExists _. iFrame.
    unfold wish_checkMembHide. simpl.
    rewrite Nat.add_0_r.
    replace (W64 (length hist)) with ver by word.
    iFrame "#".
  }
  (* loop done. *)
  iRight. iModIntro. iSplitR; first done.
  wp_load. iApply "HΦ".
  iFrame. iDestruct (own_slice_to_small with "[$]") as "$".
  iSplitR; first word.
  by iFrame "#".
Qed.

Typeclasses Opaque is_map_relation.

Lemma wp_compCommitOpen secret_sl label_sl (secret label : list w8) dqs dql :
  {{{
        "Hsecret" ∷ own_slice_small secret_sl byteT dqs secret ∗
        "Hlabel" ∷ own_slice_small label_sl byteT dql label
  }}}
    compCommitOpen (slice_val secret_sl) (slice_val label_sl)
  {{{
      rand_sl (rand: list w8), RET (slice_val rand_sl);
      "Hrand_sl" ∷ own_slice_small rand_sl byteT (DfracOwn 1) rand ∗
      "Hsecret" ∷ own_slice_small secret_sl byteT dqs secret ∗
      "Hsl_label" ∷ own_slice_small label_sl byteT dql label ∗
      "#Hrand" ∷ is_hash (secret ++ label) rand
  }}}.
Proof.
  iIntros (?) "Hpre HΦ". iNamed "Hpre". wp_rec.
  wp_pures. wp_apply wp_NewSliceWithCap; [word |] .
  iIntros (?) "Hsl". wp_apply wp_ref_to; [val_ty|].
  iIntros. wp_pures. wp_load. wp_apply (wp_SliceAppendSlice with "[$Hsl $Hsecret]"); first done.
  iIntros (?) "[Hsl Hsecret]". wp_pures. wp_store. wp_load.
  wp_apply (wp_SliceAppendSlice with "[$Hsl $Hlabel]"); first done.
  iIntros (?) "[Hsl Hlabel]". wp_pures. wp_store. wp_load.
  iDestruct (own_slice_to_small with "Hsl") as "H".
  wp_apply (wp_Hash with "[$]"). iIntros "*". iNamed 1.
  iDestruct (own_slice_to_small with "Hsl_hash") as "Hsl_hash".
  iApply "HΦ". rewrite replicate_0. iFrame "∗#".
Qed.

Lemma wp_getLatest γ keyMap_ptr st dq uid vrfSk commitSecret_sl dqc pk_sl :
  let userState := (st.(Server.userInfo) !! uid) in
  {{{
      "Htree" ∷ own_Tree keyMap_ptr st.(Server.keyMap) dq ∗
      "#HvrfSk" ∷ is_vrf_sk vrfSk γ.(vrf_pk) ∗
      "HcommitSecret" ∷ own_slice_small commitSecret_sl byteT dqc γ.(commitSecret) ∗
      "#Hpk" ∷ own_slice_small pk_sl byteT DfracDiscarded (default [] $ userState.plainPk <$> userState) ∗
      "#Hcrypto" ∷ is_Server_crypto γ st
  }}}
    getLatest #keyMap_ptr #uid #(default (W64 0) (userState.numVers <$> userState))
    #vrfSk (slice_val commitSecret_sl) (slice_val pk_sl)
  {{{
        (isRegistered : bool) (latest_ptr : loc) latest, RET (#isRegistered, #latest_ptr);
        "Htree" ∷ own_Tree keyMap_ptr st.(Server.keyMap) dq ∗
        "Hlat" ∷ Memb.own latest_ptr latest (DfracOwn 1) ∗
        "%Heq_is_reg" ∷ ⌜ isRegistered = negb $ bool_decide ((default (W64 0) (userState.numVers <$> userState)) = (W64 0)) ⌝ ∗
        "#Hwish_lat" ∷ if negb isRegistered then True else
            ∃ label commit,
              wish_checkMemb γ.(vrf_pk) uid (word.sub
                                               (default (W64 0) (userState.numVers <$> userState))
                                               (W64 1))
                                 (default [] (servEpochInfo.dig <$> last st.(Server.epochHist)))
                                 latest label commit
  }}}.
Proof.
  intros ?. iIntros (?) "H HΦ". iNamed "H".
  wp_rec. wp_pures. wp_if_destruct.
  {
    wp_apply wp_allocStruct; [val_ty|].
    iIntros (?) "Hc". wp_apply wp_allocStruct; [val_ty|].
    iIntros (?) "Hm". wp_pures. iApply "HΦ".
    iDestruct (struct_fields_split with "Hc") as "H". iNamed "H".
    iDestruct (struct_fields_split with "Hm") as "H". iNamed "H".
    instantiate (1:=ltac:(econstructor)). simpl.
    iFrame. simpl. rewrite zero_slice_val. iFrame.
    instantiate (2:=ltac:(econstructor)). simpl.
    iDestruct (own_slice_small_nil) as "$"; [done|].
    iDestruct (own_slice_small_nil) as "$"; [done|].
    iPureIntro. rewrite bool_decide_true //.
  }
  wp_apply (wp_compMapLabel with "[$]").
  iIntros "*". iNamed 1.
  wp_pures. wp_apply (wp_Tree__Prove with "[$Htree $Hout_sl]").
  iIntros "*". iNamed 1. wp_pures.
  iNamed "Hcrypto".

  specialize (HkeyMapLatest uid).
  subst userState. destruct lookup eqn:Hlookup in HkeyMapLatest, Heqb.
  2:{ simpl in *. exfalso. word. }
  destruct t as [numVers plainPk]. simpl in *.
  iDestruct "HkeyMap" as "#HkeyMap".
  destruct HkeyMapLatest as [HkeyMapLatest _].
  destruct lookup eqn:Hlookup2 in HkeyMapLatest.
  2:{ simpl in *. exfalso. done. }
  destruct p. simpl in *. subst.
  unfold is_map_relation.
  iDestruct ("HkeyMap" $! (uid, _)) as "#HkeyMap2". setoid_rewrite Hlookup2.
  iDestruct "HkeyMap2" as (???) "(#Hlabel & #Hrand & #Hcommit & %)".
  rewrite Hlookup.
  iDestruct (is_vrf_out_det with "Hlabel Hvrf_out") as "%". subst.

  destruct in_tree.
  2:{ exfalso. naive_solver. }

  wp_apply std_proof.wp_Assert; [done | ].
  wp_pures.
  wp_apply (MapValPre.wp_dec with "[]").
  { iFrame "#". }
  iIntros "*". iNamed 1. wp_pures.
  iDestruct "Hgenie" as "[_ Hgenie]".
  rewrite Hlook_elems in H. simplify_eq.
  iDestruct (own_slice_small_sz with "Hsl_val") as %Hsz.
  iDestruct ("Hgenie" with "[]") as "%Heq".
  {
    simpl. iExists (enc_val _ _), _, [].
    iSplitL. 2:rewrite app_nil_r //.
    iPureIntro. unfold MapValPre.encodes.
    split; last done. simpl.
    unfold enc_val in Hsz. rewrite /= in Hsz.
    rewrite !length_app in Hsz.
    word.
  }
  iSpecialize ("Herr" with "[]").
  {
    simpl. instantiate (1:=[]).
    iSplitL. 2:rewrite app_nil_r //.
    iPureIntro. unfold MapValPre.encodes.
    split; last done. simpl.
    unfold enc_val in Hsz. rewrite /= in Hsz.
    rewrite !length_app in Hsz.
    word.
  }
  subst. wp_apply std_proof.wp_Assert; [done | ].
  wp_apply (wp_compCommitOpen with "[$HcommitSecret $Hsl_label]").
  iIntros "*". iRename "Hrand" into "Hrand2". iNamed 1.
  wp_pures. wp_apply wp_allocStruct; [val_ty | ].
  iIntros (open_ptr) "Hopen".
  wp_pures. iNamed "Herr". iNamed "Hown_obj".
  wp_loadField. wp_apply wp_allocStruct; [val_ty | ].
  iIntros (m_ptr) "Hm". wp_pures.
  iApply "HΦ".
  iDestruct (struct_fields_split with "Hm") as "H". iNamed "H".
  iDestruct (struct_fields_split with "Hopen") as "H". iNamed "H".
  instantiate (1:=ltac:(econstructor)). simpl.
  iFrame. simpl. instantiate (2:=ltac:(econstructor)). simpl.
  iFrame. iFrame "Hpk". iPersist "Hsl_proof".
  iFrame "Hsl_proof". iModIntro.
  iDestruct (is_merkle_map_det with "His_dig Hdig") as %Heq. subst.
  iDestruct (is_hash_det with "Hrand Hrand2") as %Heq. subst.
  rewrite HepochHistLast /=. iFrame "#". iPureIntro. rewrite bool_decide_false //.
Qed.

Lemma wp_getBound γ st keyMap_ptr (uid : w64) vrfSk dq :
  {{{
      "Htree" ∷ own_Tree keyMap_ptr st.(Server.keyMap) dq ∗
      "#HvrfSk" ∷ is_vrf_sk vrfSk γ.(vrf_pk) ∗
      "#Hcrypto" ∷ is_Server_crypto γ st
  }}}
    getBound #keyMap_ptr #uid #(default (W64 0) (userState.numVers <$> (st.(Server.userInfo) !! uid))) #vrfSk
  {{{
      (bound_ptr : loc) bound, RET #bound_ptr;
        "Htree" ∷ own_Tree keyMap_ptr st.(Server.keyMap) dq ∗
        "Hbound" ∷ NonMemb.own bound_ptr bound (DfracOwn 1) ∗
        "#Hwish_bound" ∷
          wish_checkNonMemb γ.(vrf_pk) uid
            (default (W64 0) (userState.numVers <$> (st.(Server.userInfo) !! uid)))
            (default [] (servEpochInfo.dig <$> last st.(Server.epochHist)))
            bound
  }}}.
Proof.
  iIntros (?) "Hpre HΦ". iNamed "Hpre". wp_rec. wp_pures.
  wp_apply (wp_compMapLabel with "[$]").
  iIntros "*". iNamed 1.
  wp_pures. wp_apply (wp_Tree__Prove with "[$Htree $Hout_sl]").
  iIntros "*". iNamed 1. wp_pures.
  destruct in_tree.
  {
    iExFalso. iNamed "Hcrypto".
    unfold is_map_relation. iDestruct "HkeyMap" as "#HkeyMap".
    specialize (HkeyMapLatest uid).
    destruct lookup eqn:Hlookup in HkeyMapLatest.
    - destruct t as [??]. rewrite Hlookup. simpl.
      iSpecialize ("HkeyMap" $! (uid, numVers) None with "[]").
      {
        iPureIntro. destruct HkeyMapLatest as [_ HkeyMapLatest].
        specialize (HkeyMapLatest numVers) as [HkeyMapLatest _].
        apply not_elem_of_dom_1.
        intros H. apply HkeyMapLatest in H. lia.
      }
      iDestruct ("HkeyMap" with "Hvrf_out") as %Hnone.
      naive_solver.
    - rewrite Hlookup /=. iSpecialize ("HkeyMap" $! (uid, W64 0) None with "[]").
      { iPureIntro. by apply not_elem_of_dom_1. }
      iDestruct ("HkeyMap" with "Hvrf_out") as %Hnone.
      naive_solver.
  }
  iPersist "Hsl_proof".
  wp_apply std_proof.wp_Assert; [done|].
  wp_pures. wp_apply wp_allocStruct; [val_ty|]. iIntros (?) "Hnm".
  iApply "HΦ". iDestruct (struct_fields_split with "Hnm") as "H". iNamed "H".
  iFrame. instantiate (1:=ltac:(econstructor)). simpl. iFrame "∗ Hsl_proof".
  iNamed "Hcrypto".
  iDestruct (is_merkle_map_det with "His_dig Hdig") as %Heq. subst.
  rewrite HepochHistLast /=. iFrame "#".
Qed.

Lemma ghost_latest_epoch γ st cli_ep q :
  let latest_epoch := (W64 (length st.(Server.epochHist) - 1)) in
  is_epoch_lb γ cli_ep ∗
  own_Server_hist γ q st
  -∗
  "#Hlb_ep" ∷ is_epoch_lb γ latest_epoch ∗
  "%Hlt_ep" ∷ ⌜ uint.Z cli_ep ≤ uint.Z latest_epoch ⌝.
Proof.
  intros ?. iIntros "((% & Hlb & %) & Hghost)".
  iNamed "Hghost".
  (* FIXME: combine gives instances for mono_list_auth *)
  iDestruct (mono_list_auth_lb_valid with "Hauditor Hlb") as %[_ Hprefix].
  iClear "Hlb".
  iDestruct (mono_list_lb_own_get with "Hauditor") as "#Hlb".
  iFrame "#". iPureIntro.
  apply prefix_length in Hprefix. subst latest_epoch.
  apply (f_equal length) in Hdigs_gs. rewrite !length_fmap in Hdigs_gs.
  word.
Qed.

Lemma wp_Server__Get γ ptr uid cli_ep :
  {{{
    "#Hserv" ∷ is_Server γ ptr ∗
    "#Hlb_ep" ∷ is_epoch_lb γ cli_ep
  }}}
  Server__Get #ptr #uid
  {{{
    ptr_sigdig sigdig sl_hist ptr2_hist hist
    is_reg ptr_lat lat ptr_bound bound (nVers : w64),
    RET (#ptr_sigdig, slice_val sl_hist, #is_reg, #ptr_lat, #ptr_bound);
    "#Hlb_ep" ∷ is_epoch_lb γ sigdig.(SigDig.Epoch) ∗
    "%Hlt_ep" ∷ ⌜ uint.Z cli_ep ≤ uint.Z sigdig.(SigDig.Epoch) ⌝ ∗
    "#Hsigdig" ∷ SigDig.own ptr_sigdig sigdig DfracDiscarded ∗
    "#Hsig" ∷ is_sig γ.(sig_pk)
      (PreSigDig.encodesF $ PreSigDig.mk sigdig.(SigDig.Epoch) sigdig.(SigDig.Dig))
      sigdig.(SigDig.Sig) ∗
    "%Hlen_hist" ∷ ⌜ length hist = pred (uint.nat nVers) ⌝ ∗
    "Hhist" ∷ ([∗ list] l;x ∈ ptr2_hist;hist,
      MembHide.own l x (DfracOwn 1)) ∗
    "Hsl_hist" ∷ own_slice_small sl_hist ptrT (DfracOwn 1) ptr2_hist ∗
    "#Hwish_hist" ∷ ([∗ list] ver ↦ x ∈ hist,
      ∃ label,
      wish_checkMembHide γ.(vrf_pk) uid (W64 ver)
        sigdig.(SigDig.Dig) x label) ∗
    "Hlat" ∷ Memb.own ptr_lat lat (DfracOwn 1) ∗
    "%Heq_is_reg" ∷ ⌜ is_reg = negb $ bool_decide (nVers = (W64 0)) ⌝ ∗
    "#Hwish_lat" ∷ (if negb is_reg then True else
      ∃ label commit,
      wish_checkMemb γ.(vrf_pk) uid (word.sub nVers (W64 1))
        sigdig.(SigDig.Dig) lat label commit) ∗
    "Hbound" ∷ NonMemb.own ptr_bound bound (DfracOwn 1) ∗
    "#Hwish_bound" ∷ wish_checkNonMemb γ.(vrf_pk) uid nVers sigdig.(SigDig.Dig) bound
  }}}.
Proof.
  iIntros (?) "Hpre HΦ". iNamed "Hpre". iNamed "Hserv".
  wp_rec. wp_pures. wp_loadField. wp_apply (read_wp_Mutex__Lock with "[$]").
  iNamed 1. wp_pures.
  iNamedSuffix "Hphys" "_own".
  wp_loadField. wp_apply (wp_MapGet with "[$]"). iIntros "%userState_ptr %ok [%Hlookup H1_own]".
  wp_pures. wp_apply wp_ref_of_zero; [done | ]. iIntros "%numVers_ptr numVers".
  wp_pures. wp_apply wp_ref_of_zero; [done | ]. iIntros "%plainPk plainPk".
  wp_pures.
  wp_bind (if: _ then _ else _)%E.
  wp_apply (wp_wand _ _ _ (λ _,
                             ∃ plainPk_sl,
                               let userState := (st.(Server.userInfo) !! uid) in
                               "numVers" ∷ numVers_ptr ↦[uint64T] #(default (W64 0) (userState.numVers <$> userState)) ∗
                               "plainPk" ∷ plainPk ↦[slice.T byteT] (slice_val plainPk_sl) ∗
                               "#plainPk_sl" ∷ own_slice_small plainPk_sl byteT DfracDiscarded (default [] (userState.plainPk <$> userState)) ∗
                               _
              )%I
             with "[-]").
  {
    rewrite zero_slice_val.
    Unshelve.
    2:{ clear dependent ok. shelve. } (* XXX: make sure the evar doesn't depend on [ok] *)
    destruct ok.
    - apply map_get_true in Hlookup.
      iDestruct (big_sepM2_lookup_l_some with "[$]") as "%H".
      { eassumption. }
      destruct H as [userState Hlookup2].
      iDestruct (big_sepM2_lookup_acc with "[$]") as "[Huinfo Huinfo_own]"; [eassumption.. | ].
      iNamedSuffix "Huinfo" "_uinfo".
      iDestruct (struct_field_pointsto_not_null with "numVers_uinfo") as %Hnot_null; [done.. | ].
      rewrite bool_decide_false //. 2: naive_solver.
      wp_pures. wp_loadField. wp_store. wp_loadField. wp_store.
      iCombineNamed "*_uinfo" as "Huinfo".
      iSpecialize ("Huinfo_own" with "[Huinfo]").
      { iNamed "Huinfo". iFrame "∗#". }
      rewrite Hlookup2 /=. iFrame "∗#". iModIntro.
      iNamedAccu.
    - apply map_get_false in Hlookup as [Hlookup ?]. subst.
      rewrite bool_decide_true //. wp_pures.
      iDestruct (big_sepM2_lookup_l_none with "HuserInfo_own_own") as %->.
      { done. } iFrame. simpl. iModIntro. iDestruct (own_slice_small_nil) as "$". done.
  }
  iIntros (?). iNamed 1.
  wp_pures. clear v.
  wp_loadField. wp_apply (wp_getDig with "[$HepochHist_sl_own]").
  { iFrame "#%". }
  iIntros "*". iNamed 1. iRename "HepochHist_sl" into "HepochHist_sl_own".
  wp_pures. wp_loadField. wp_load. wp_loadField.
  wp_apply (wp_getHist with "[$HkeyMap_own]").
  { iFrame "#". done. }
  iIntros "*". iNamed 1.
  wp_pures. wp_load. wp_loadField. wp_loadField. wp_load. wp_loadField.
  wp_apply (wp_getLatest with "[$Htree]").
  { iFrame "#". }
  iIntros "*". iNamed 1.
  wp_pures. wp_loadField. wp_load. wp_loadField.
  wp_apply (wp_getBound with "[$Htree]").
  { iFrame "#". }
  iIntros "*". iNamed 1. wp_pures.
  wp_loadField.

  iDestruct (ghost_latest_epoch with "[$]") as "#H".
  iClear "Hlb_ep". iNamed "H".

  iRename "Htree" into "Htree_own".
  iCombineNamed "*_own" as "Hown".
  wp_apply (read_wp_Mutex__Unlock with "[$Hmu Hown Hghost Hnvers]").
  { iNamed "Hown". iFrame "∗#". }
  wp_pures.
  iApply "HΦ".
  instantiate (2:=ltac:(econstructor)). simpl.
  iFrame "∗#%". done.
Qed.

Lemma wp_Server__Put γ ptr uid nVers sl_pk (pk : list w8) cli_next_ep :
  {{{
    "#Hserv" ∷ is_Server γ ptr ∗
    "Hvers" ∷ own_num_vers γ uid nVers ∗
    "#Hsl_pk" ∷ own_slice_small sl_pk byteT DfracDiscarded pk ∗
    "#Hlb_ep" ∷ is_epoch_lb γ cli_next_ep
  }}}
  Server__Put #ptr #uid (slice_val sl_pk)
  {{{
    ptr_sigdig sigdig ptr_lat lat ptr_bound bound label commit,
    RET (#ptr_sigdig, #ptr_lat, #ptr_bound, #false);
    let new_next_ep := word.add sigdig.(SigDig.Epoch) (W64 1) in
    "Hvers" ∷ own_num_vers γ uid (word.add nVers (W64 1)) ∗

    "%Heq_ep" ∷ ⌜ sigdig.(SigDig.Epoch) = lat.(Memb.EpochAdded) ⌝ ∗
    "%Heq_pk" ∷ ⌜ pk = lat.(Memb.PkOpen).(CommitOpen.Val) ⌝ ∗
    "#Hlb_ep" ∷ is_epoch_lb γ new_next_ep ∗
    "%Hlt_ep" ∷ ⌜ uint.Z cli_next_ep < uint.Z new_next_ep ⌝ ∗
    (* provable from new_next_ep = the w64 size of epochHist slice. *)
    "%Hnoof_ep" ∷ ⌜ uint.Z new_next_ep = (uint.Z sigdig.(SigDig.Epoch) + 1)%Z ⌝ ∗

    "#Hsigdig" ∷ SigDig.own ptr_sigdig sigdig DfracDiscarded ∗
    "#Hsig" ∷ is_sig γ.(sig_pk)
      (PreSigDig.encodesF $ PreSigDig.mk sigdig.(SigDig.Epoch) sigdig.(SigDig.Dig))
      sigdig.(SigDig.Sig) ∗

    "Hlat" ∷ Memb.own ptr_lat lat (DfracOwn 1) ∗
    "#Hwish_lat" ∷ wish_checkMemb γ.(vrf_pk) uid nVers
      sigdig.(SigDig.Dig) lat label commit ∗

    "Hbound" ∷ NonMemb.own ptr_bound bound (DfracOwn 1) ∗
    "#Hwish_bound" ∷ wish_checkNonMemb γ.(vrf_pk)
      uid (word.add nVers (W64 1)) sigdig.(SigDig.Dig) bound
  }}}.
Proof.
  iIntros (?) "Hpre HΦ". iNamed "Hpre". wp_rec. wp_pures.
  wp_apply wp_allocStruct; [val_ty|]. iIntros (req) "Hreq".
  iNamed "Hserv". wp_loadField.
  iMod (struct_pointsto_persist with "Hreq") as "#Hreq".
  iDestruct (struct_fields_split with "Hreq") as "H". iNamed "H".
  wp_apply (wp_WorkQ__Do with "[$]").
  repeat iExists _. instantiate (1:=ltac:(econstructor)). simpl.
  iFrame "Uid Pk Hvers Hsl_pk Hlb_ep". iClear "Hlb_ep".
  iApply to_named. unfold wq_post. iIntros "*". iNamed 1. wp_pures. wp_loadField.
  wp_loadField. wp_loadField. wp_loadField. wp_pures.
  iApply "HΦ". iFrame "∗#%". done.
Qed.

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

Definition is_mapper0Out_crypto γ st req mo : iProp Σ :=
  let latestVer := (default (W64 0) (userState.numVers <$> (st.(Server.userInfo) !! req.(WQReq.Uid)))) in
  let boundVer := (word.add latestVer (W64 1)) in
  ∃ commit,
  "#HlatestVrfHash" ∷ is_vrf_out γ.(vrf_pk) (enc_label_pre req.(WQReq.Uid) latestVer) mo.(mapper0Out.latestVrfHash) ∗
  "#HlatestVrfProof" ∷ is_vrf_proof γ.(vrf_pk) (enc_label_pre req.(WQReq.Uid) latestVer) mo.(mapper0Out.latestVrfProof) ∗
  "#HboundVrfHash" ∷ is_vrf_out γ.(vrf_pk) (enc_label_pre req.(WQReq.Uid) boundVer) mo.(mapper0Out.boundVrfHash) ∗
  "#HboundVrfProof" ∷ is_vrf_proof γ.(vrf_pk) (enc_label_pre req.(WQReq.Uid) boundVer) mo.(mapper0Out.boundVrfProof) ∗
  "#Hrand" ∷ is_hash (γ.(commitSecret) ++ mo.(mapper0Out.latestVrfHash)) mo.(mapper0Out.pkOpen).(CommitOpen.Rand) ∗
  "#Hcommit" ∷ is_hash (CommitOpen.encodesF mo.(mapper0Out.pkOpen)) commit ∗
  "%HmapVal" ∷ ⌜ mo.(mapper0Out.mapVal) = enc_val (W64 $ length st.(Server.epochHist)) commit ⌝ ∗
  "%Hpk" ∷ ⌜ mo.(mapper0Out.pkOpen).(CommitOpen.Val) = req.(WQReq.Pk) ⌝
.

Lemma wp_Server__mapper0 γ s st q (in' out : loc) req :
  {{{
    "#His" ∷ is_Server γ s ∗
    "Hphys" ∷ Server.own_phys s q st ∗
    "#Req" ∷ WQReq.is_own in' req ∗
    "out" ∷ out ↦[struct.t mapper0Out] zero_val (struct.t mapper0Out)
  }}}
    Server__mapper0 #s #in' #out
  {{{
      mo, RET #();
        "Hphys" ∷ Server.own_phys s q st ∗
        "#out" ∷ mapper0Out.is_own out mo ∗
        "#out_crypto" ∷ is_mapper0Out_crypto γ st req mo
  }}}.
Proof.
  iIntros (?) "Hpre HΦ". iNamed "Hpre". wp_rec. wp_pures.
  (* XXX: destructing now because [struct.t mapper0Out] gets unfolded at some point. *)
  iDestruct (struct_fields_split with "out") as "H". iNamed "H". simpl.
  iNamedSuffix "Hphys" "_phys". iNamed "Req". wp_loadField. wp_loadField.
  wp_apply (wp_MapGet with "[$]"). iIntros "* [%Hlookup HuserInfo_map_phys]".
  wp_pures. wp_apply wp_ref_of_zero; [done|]. iIntros (numVers_ptr) "numVers".
  wp_pures.
  wp_bind (If _ _ _).
  wp_apply (wp_wand _ _ _ (λ _,
                             "numVers" ∷ numVers_ptr ↦[uint64T]
                               #(default (W64 0) (userState.numVers <$> (st.(Server.userInfo) !!
                                                                              req.(WQReq.Uid)))) ∗
                             _
              )%I with "[-]").
  {
    destruct ok.
    - apply map_get_true in Hlookup.
      iDestruct (big_sepM2_lookup_l_some with "HuserInfo_own_phys") as %[uinfo Hlookup2].
      { done. }
      iDestruct (big_sepM2_lookup_acc with "HuserInfo_own_phys") as "[H HuserInfo_own_phys]"; [done..|].
      iNamedPrefix "H" "uinfo.".
      iDestruct (struct_field_pointsto_not_null with "uinfo.numVers") as "%"; [done..|].
      rewrite bool_decide_false //. 2: naive_solver. wp_pures.
      wp_loadField. wp_store. rewrite Hlookup2. simpl.
      iFrame. iModIntro.
      (* FIXME: why does "uinfo.*" not work? Probably not included in the allowed character list. *)
      iCombineNamed "uinfo*" as "Huinfo".
      iSpecialize ("HuserInfo_own_phys" with "[Huinfo]").
      { iNamed "Huinfo". iFrame "∗#". } iClear "uinfo.plainPk_sl".
      Unshelve.
      2:{ clear v0 ok numVers_ptr. shelve. }
      iNamedAccu.
    - apply map_get_false in Hlookup as [Hlookup ->].
      rewrite bool_decide_true //. wp_pures.
      iDestruct (big_sepM2_lookup_l_none with "HuserInfo_own_phys") as %Hlookup2.
      { done. }
      rewrite Hlookup2.
      iModIntro. iFrame.
  }
  iIntros (v'). iNamed 1. wp_pures. clear v'.
  iNamed "His". wp_loadField. wp_load. wp_loadField.
  wp_apply (wp_compMapLabel with "[$]").
  iIntros "*". iNamedSuffix 1 "_lat".
  wp_pures. wp_loadField. wp_load. wp_loadField.
  wp_apply (wp_compMapLabel with "[$]").
  iIntros "*". iNamedSuffix 1 "_bound". wp_pures.
  wp_loadField. wp_apply wp_slice_len. wp_pures. wp_loadField.
  iDestruct (own_slice_sz with "HepochHist_sl_phys") as %H.
  iDestruct (big_sepL2_length with "HepochHist_is_phys") as %Hlen.
  wp_apply (wp_compCommitOpen with "[Hout_sl_lat]").
  { iFrame "∗#". }
  iIntros "*". iNamed 1. wp_pures. wp_loadField. wp_apply wp_allocStruct; [val_ty|].
  iIntros (open_ptr) "Hopen". wp_pures.
  iPersist "Hopen". iPersist "Hrand_sl".
  wp_apply (wp_compMapVal with "[Hopen Pk_sl Hrand_sl]").
  { iDestruct (struct_fields_split with "Hopen") as "H". iNamed "H".
    iFrame "#". instantiate (1:=ltac:(econstructor)). iFrame "#". }
  iIntros "*". iNamed 1. wp_pures.
  wp_storeField. wp_storeField. wp_storeField. wp_storeField. wp_storeField.
  wp_storeField. iPersist "Hsl_label".
  iPersist "Hproof_sl_lat". iPersist "Hproof_sl_bound". iPersist "Hout_sl_bound".
  iPersist "Hsl_map_val".
  iMod (struct_field_pointsto_persist with "pkOpen") as "#pkOpen".
  iMod (struct_field_pointsto_persist with "mapVal") as "#mapVal".
  iMod (struct_field_pointsto_persist with "boundVrfProof") as "#boundVrfProof".
  iMod (struct_field_pointsto_persist with "boundVrfHash") as "#boundVrfHash".
  iMod (struct_field_pointsto_persist with "latestVrfProof") as "#latestVrfProof".
  iMod (struct_field_pointsto_persist with "latestVrfHash") as "#latestVrfHash".
  iApply "HΦ". iModIntro. iCombineNamed "*_phys" as "Hphys". iSplitL "Hphys".
  { iNamed "Hphys". iFrame "∗#". }
  iClear "Hsecret".
  iSplitL.
  { iFrame "#". instantiate (1:=ltac:(econstructor)). simpl. iFrame "∗#". }
  iFrame "#". simpl. iPureIntro. split; last done. f_equal. f_equal. word.
Qed.

Lemma ghost_nvers_put γ st uid label numVers plainPk mapval upd userInfo :
  own_num_vers γ uid numVers -∗
  own_Server_nvers γ 1
    (st <| Server.keyMap := upd ∪ st.(Server.keyMap) |> <| Server.userInfo := userInfo |>)
  ==∗
  ⌜ default (W64 0) (userState.numVers <$> (userInfo !! uid)) = numVers ⌝ ∗
  own_num_vers γ uid (word.add numVers (W64 1)) ∗
  own_Server_nvers γ 1
    (st <| Server.keyMap := (<[label:=mapval]> upd) ∪ st.(Server.keyMap) |>
        <| Server.userInfo := <[uid:=userState.mk (word.add numVers (W64 1)) plainPk]> userInfo |>).
Proof.
  iIntros "Hn". iNamed 1. simpl.
  iCombine "Hn Hnvers" gives %Hlookup.
  pose proof (Hgauge uid) as Heq. rewrite Hlookup /= in Heq.
  subst. rewrite lookup_fmap.
  iMod (ghost_map_update with "[$] [$]") as "[Hnvers $]".
  iFrame "∗%". iPureIntro. split; first done. simpl.
  intros uid'. destruct (decide (uid = uid')).
  { subst. rewrite lookup_fmap !lookup_insert //. }
  { rewrite lookup_fmap !lookup_insert_ne //. specialize (Hgauge uid').
    rewrite lookup_fmap in Hgauge. done. }
Qed.

Lemma ghost_nvers_agree γ st uid numVers :
  own_num_vers γ uid numVers -∗
  own_Server_nvers γ 1 st -∗
  ⌜ numVers = default (W64 0) (userState.numVers <$> (st.(Server.userInfo) !! uid)) ⌝.
Proof.
  iIntros "Hn". iNamed 1. simpl.
  iCombine "Hn Hnvers" gives %Hlookup.
  pose proof (Hgauge uid) as Heq. rewrite Hlookup /= in Heq.
  subst. rewrite lookup_fmap //.
Qed.

(* FIXME: is there already a lemma like this? *)
Lemma big_sepL_iter {PROP : bi} {A : Type} R (Φ Ψ : nat → A → PROP) (l : list A) :
  R -∗
  ([∗ list] k↦x ∈ l, Φ k x) -∗
  ([∗ list] k↦x ∈ l, R -∗ Φ k x -∗ R ∗ Ψ k x) -∗
  R ∗ ([∗ list] k↦x ∈ l, Ψ k x).
Proof.
  iIntros "HR H1 Hwand".
  iInduction l as [|] using rev_ind.
  { rewrite big_sepL_nil. by iFrame. }
  rewrite !big_sepL_snoc. iDestruct "H1" as "[H1 Ha]". iDestruct "Hwand" as "[Hwand Hb]".
  iDestruct ("IHl" with "[$] [$] [$]") as "[HR H]".
  iDestruct ("Hb" with "[$] [$]") as "[? ?]". iFrame.
Qed.

Lemma big_sepL_forall_1 {PROP : bi} {A : Type} (Φ : nat → A → PROP) (l : list A) :
  □(∀ (k : nat) (x : A), ⌜l !! k = Some x⌝ → Φ k x) -∗ ([∗ list] k↦x ∈ l, Φ k x).
Proof.
  iIntros "#H". iInduction l as [|] using rev_ind.
  { rewrite big_sepL_nil //. }
  iSpecialize ("IHl" with "[]").
  { iIntros "!# * %". iApply "H". iPureIntro. rewrite lookup_app_l //.
    eapply lookup_lt_Some. done. }
  rewrite big_sepL_app. iFrame "IHl".
  rewrite big_sepL_singleton. iApply "H". iPureIntro.
  rewrite lookup_app_r; last lia.
  replace (_ : nat) with (0)%nat by lia. done.
Qed.

Lemma map_lower_union X Y X' Y' :
  map_lower X Y →
  map_lower X' Y' →
  map_lower (X' ∪ X) (Y' ∪ Y).
Proof.
  intros H H'.
  simpl. unfold map_lower in *.
  unfold map_Forall2 in *.
  intros uid. specialize (H uid). specialize (H' uid).
  rewrite lookup_union. destruct (Y' !! uid).
  + rewrite union_Some_l lookup_fmap.
    inversion H'. subst x. rename H1 into Hlookup.
    symmetry in Hlookup. rewrite lookup_fmap_Some in Hlookup. destruct Hlookup as (? & <- & Hlookup).
    erewrite lookup_union_Some_l; last done. simpl. by constructor.
  + rewrite left_id. inversion H'. rename H0 into Hlookup.
    symmetry in Hlookup. rewrite lookup_fmap fmap_None in Hlookup.
    rewrite lookup_fmap lookup_union_r //. rewrite lookup_fmap in H. done.
Qed.

Lemma map_lower_disj X Y X' Y' :
  map_lower X Y →
  map_lower X' Y' →
  Y ##ₘ Y' →
  X ##ₘ X'.
Proof.
Admitted.

Lemma ghost_hist_update upd upd_phys userInfo γ st dig :
  let presigdig := {| PreSigDig.Epoch := (W64 $ length st.(Server.epochHist)); PreSigDig.Dig := dig |} in
  map_lower upd upd_phys →
  map_Forall (λ _ v, v.1 = W64 (length st.(Server.epochHist))) upd →
  upd_phys ##ₘ st.(Server.keyMap) →
  (length st.(Server.epochHist) + 1)%nat = uint.nat (W64 (length st.(Server.epochHist) + 1)%nat) →
  is_merkle_map (upd_phys ∪ st.(Server.keyMap)) dig -∗
  own_Server_hist γ 1 st ==∗
  (∀ enc, ⌜ PreSigDig.encodes enc presigdig ⌝ -∗ (sigpred γ.(auditor_gn) enc)) ∗
  (∀ sig,
     let st' :=
       (st <| Server.keyMap := upd_phys ∪ st.(Server.keyMap) |>
           <| Server.userInfo := userInfo |>
           <| Server.epochHist := st.(Server.epochHist) ++ [servEpochInfo.mk upd dig sig] |>
       ) in
     own_Server_hist γ 1 st').
Proof.
  intros ? Hupd Hep Hdisj Hoverflow. iIntros "#Hdig". iNamed 1.
  iMod (mono_list_auth_own_update (gs ++ [(upd ∪ (default ∅ (last gs.*1)), dig)]) with "Hauditor") as "[Hauth #Hlb]".
  { by apply prefix_app_r. }
  iModIntro.
  iDestruct (audit_gs_snoc _ upd _ dig with "[$] [$]") as "#H".
  { by eapply map_lower_disj. }
  { by apply map_lower_union. }
  { replace (length gs) with (length st.(Server.epochHist)); first done.
    apply (f_equal length) in Hdigs_gs as Hlength.
    rewrite !length_fmap in Hlength. word. }
  iClear "Hinv_gs".
  iSplitR.
  {
    iIntros "* %Henc". unfold sigpred. iFrame "#%".
    subst presigdig. simpl.
    replace (uint.nat (W64 _)) with (length gs).
    { rewrite lookup_app_r // Nat.sub_diag //=. iPureIntro. by eexists. }
    apply (f_equal length) in Hdigs_gs as Hlength.
    rewrite !length_fmap in Hlength. word.
  }
  iIntros (?). iFrame "∗#%". simpl.
  iSplitL.
  { rewrite (fmap_last _ (gs ++ _)) last_snoc.
    iPureIntro. by apply map_lower_union. }
  rewrite !fmap_app Hdigs_gs /=. iSplitR; first done.
  rewrite length_app /=. iPureIntro. word.
Qed.

(* updates: gmap (list w8) (w64 * list w8); *)
Lemma wp_updEpochHist s γ st upd_ptr upd_sl upd userInfo openKeyMap :
  let upd_phys := (λ x, enc_val x.1 x.2) <$> upd in
  let st' := (st <| Server.keyMap := upd_phys ∪ st.(Server.keyMap) |> <| Server.userInfo := userInfo |>) in
  {{{
      "#His_srv" ∷ is_Server γ s ∗
      "#Hcrypto" ∷ is_Server_crypto γ st ∗
      "Hghost" ∷ own_Server_hist γ 1 st ∗
      "Hnvers" ∷ own_Server_nvers γ 1 st' ∗
      "Hphys" ∷ Server.own_phys s 1 st' ∗
      "upd" ∷ own_map upd_ptr (DfracOwn 1) upd_sl ∗
      "#Hupd" ∷ ([∗ map] u_sl; u ∈ upd_sl; upd, own_slice_small u_sl byteT DfracDiscarded (enc_val u.1 u.2)) ∗

      "#HopenKeyMap" ∷ is_map_relation γ st'.(Server.keyMap) openKeyMap ∗
      "%HkeyMapLatest" ∷ (⌜ ∀ uid,
                            match st'.(Server.userInfo) !! uid with
                            | Some (userState.mk numVers pk) =>
                                snd <$> openKeyMap !! (uid, (word.sub numVers (W64 1))) = Some pk ∧
                                (∀ ver, (uid, ver) ∈ dom openKeyMap ↔ uint.nat ver < uint.nat numVers)
                            | None => (∀ ver, (uid, ver) ∉ dom openKeyMap)
                            end ⌝)

  }}}
    Server__updEpochHist #s #upd_ptr
  {{{
        RET #(); own_Server γ s 1 ∗ (∃ st', Server.own_phys s (1/2) st')
  }}}.
Proof.
  intros ??. subst upd_phys. iIntros (?) "Hpre HΦ". iNamed "Hpre". wp_rec.
  iNamed "His_srv". iNamed "Hphys".
  wp_pures. wp_loadField. wp_pures. wp_loadField.
  wp_apply (wp_Tree__Digest with "[$HkeyMap]").
  iIntros (dig_sl dig). iNamed 1. wp_pures. wp_loadField. wp_apply wp_slice_len.
  iDestruct (own_slice_sz with "HepochHist_sl") as %Hsz. wp_pures.
  wp_apply wp_allocStruct; [val_ty|]. iIntros (preSig_ptr) "preSig".
  wp_pures.
  wp_apply wp_NewSliceWithCap; [word|]. iIntros (?) "preSigByt_sl".
  wp_apply (PreSigDig.wp_enc with "[preSig preSigByt_sl]").
  { iFrame. iDestruct (struct_fields_split with "preSig") as "H". iNamed "H".
    instantiate (2:=ltac:(econstructor)). iFrame "∗#". }
  iIntros (preSigByt_sl enc). iNamed 1. wp_pures.
  iMod (own_map_persist with "upd") as "#upd".
  iMod (ghost_hist_update _ userInfo with "[$] Hghost") as "Hghost".
  iDestruct (own_slice_to_small with "Hsl_b") as "Hsl".
  rewrite replicate_0 app_nil_l.
  iDestruct (big_sepL2_length with "HepochHist_is") as %Hlength.
  rewrite /st' /= in Hlength.
  iSpecialize ("Hghost" $! enc with "[%]").
  { replace (W64 (length _)) with (epochHist_sl.(Slice.sz)) by word. done. }
  iDestruct "Hghost" as "(#Hsigpred & Hghost)".
  wp_apply (wp_SigPrivateKey__Sign with "[$HsigSk $Hsl $Hsigpred]").
  iIntros "*". iNamed 1. iSpecialize ("Hghost" with "[$]").
  wp_pures. wp_apply wp_allocStruct; [val_ty|].
  iIntros (newInfo_ptr) "newInfo". wp_pures. wp_loadField.
  wp_apply (wp_SliceAppend with "[$HepochHist_sl]").
  iIntros (epochHist_sl') "HepochHist_sl". wp_storeField.
  iApply "HΦ". iPersist "newInfo".
  iDestruct (struct_fields_split with "newInfo") as "H". iNamed "H".
  iPersist "Hsl_sig". iDestruct "HepochHist_is" as "-#H".
  iDestruct (big_sepL2_snoc with "[$H]") as "#HepochHist_is".
  { instantiate (1:=ltac:(econstructor)). iFrame "updates sig dig #". }
  iClear "H".
  iAssert (Server.own_phys s 1 ltac:(econstructor)) with "[-Hghost Hnvers]" as "Hphys".
  { rewrite /Server.own_phys /=. iFrame "∗#". }
  iEval (rewrite -Qp.half_half) in "Hphys".
  iDestruct (Server.split with "Hphys") as "[$ $]".
  iFrame "∗#". simpl. iExists {| servEpochInfo.updates := upd; servEpochInfo.dig := dig; servEpochInfo.sig := sig |}.
  simpl. iFrame "#%". rewrite last_snoc.
  iNamed "Hcrypto".
  repeat iSplitR; last done.
  - iIntros "!# !# * %Hlookup".
    rewrite lookup_app in Hlookup.
    destruct lookup eqn:? in Hlookup.
    { iApply "HepochHist". iPureIntro. naive_solver. }
    apply list_lookup_singleton_Some in Hlookup as [? H]. subst.
    simpl. destruct Henc as [? ?]. subst.
    replace (epoch) with epochHist_sl.(Slice.sz).
    2:{ apply lookup_ge_None_1 in Heqo. word. }
    iFrame "#".
  - iPureIntro.
    rewrite fmap_app foldl_snoc HepochHistUpdates /=.
    rewrite map_fmap_union. done.
Qed.

Context `{!waitgroupG Σ}.
Lemma wp_Server__Worker γ s st :
  {{{
        "#His_srv" ∷ is_Server γ s ∗
        "Hown" ∷ Server.own_phys s (1/2) st
  }}}
    Server__Worker #s
  {{{
       RET #(); (∃ st', Server.own_phys s (1/2) st')
  }}}.
Proof.
  iIntros (?) "Hpre HΦ". iNamed "Hpre". wp_rec.
  iAssert _ with "His_srv" as "H". iNamed "H".
  wp_loadField. wp_apply (wp_WorkQ__Get with "[$]").
  iIntros "* [work Hwork]". wp_pures.
  wp_apply (wp_NewMap w64 bool). iIntros (uidSet_ptr) "uidSet".
  wp_pures. iDestruct (own_slice_small_sz with "work") as %Hwork_sz.
  eset (prop :=
         (λ (w : loc),
            ∃ (req_ptr resp : loc) Ψ γtok req nVers cli_next_ep,
              "resp" ∷ resp ↦[struct.t WQResp] _ ∗
              "#Resp" ∷ w ↦[Work::"Resp"]□ #resp ∗
              "#Req" ∷ w ↦[Work::"Req"]□ #req_ptr ∗
              "#HReq" ∷ WQReq.is_own req_ptr req ∗
              "Hvers" ∷ own_num_vers γ req.(WQReq.Uid) nVers ∗
              "#Hlb_ep" ∷ is_epoch_lb γ cli_next_ep ∗
              "HΨ" ∷ wq_post γ req nVers cli_next_ep Ψ ∗
              "#His_work" ∷ is_Work w γtok Ψ)%I

         ).
  Opaque w64.
  wp_apply (wp_forSlice
              (λ i,
                 ∃ (uidSet : gmap w64 bool),
                 "Hwork" ∷ ([∗ list] w ∈ (drop (uint.nat i) work), ∃ req : loc, own_Work w req (wq_spec γ)) ∗
                 "uidSet" ∷ own_map uidSet_ptr (DfracOwn 1) uidSet ∗
                 "HuidSet" ∷ (([∗ set] uid ∈ dom uidSet, ∃ n, own_num_vers γ uid n) ∧
                              ([∗ list] w ∈ (take (uint.nat i) work), prop w))
              )%I
             with
             "[] [uidSet Hwork $work]"
           ).
  (* FIXME: there are multiple ways of establishing eqdec, countable, etc. *)
  Transparent w64.
  {
    subst prop.
    clear Φ. iIntros "* % !# [Hpre [%Hlt %Hlookup]] HΦ". wp_pures.
    iNamed "Hpre". erewrite drop_S; last done.
    iDestruct "Hwork" as "[Hw Hwork]". iNamed "Hw".
    wp_apply wp_allocStruct; [val_ty|]. iIntros (resp) "Hresp".
    wp_storeField. wp_loadField.
    iRename "Req" into "Req'".
    iNamed "Hspec". iNamed "Req".
    wp_loadField. wp_pures. wp_apply (wp_MapGet with "[$]").
    iIntros "* [%Huid_lookup uidSet]". wp_pures. destruct ok.
    { (* impossible given the precondition *)
      iExFalso. apply map_get_true in Huid_lookup.
      iNamed "Hspec". iLeft in "HuidSet".
      iDestruct (big_sepS_elem_of _ _ _ with "HuidSet") as (?) "Hbad".
      { by eapply elem_of_dom_2. }
      iCombine "Hbad Hvers" gives %Hbad. exfalso.
      naive_solver.
    }
    apply map_get_false in Huid_lookup as [Huid_lookup ->].
    wp_pures.
    iMod (struct_field_pointsto_persist with "Resp") as "#Resp".
    wp_apply (wp_MapInsert with "[$]"); first done.
    iIntros "uidSet".
    iApply "HΦ". iFrame.
    replace (uint.nat (word.add i (W64 1))) with (S (uint.nat i)) by word.
    iFrame. iSplit.
    - (* uidSet *) unfold typed_map.map_insert. iNamed "Hspec".
      iLeft in "HuidSet". rewrite dom_insert_L.
      rewrite big_sepS_union.
      2:{ rewrite -not_elem_of_dom in Huid_lookup. set_solver. }
      rewrite big_sepS_singleton. iFrame.
    - iRight in "HuidSet".
      erewrite take_S_r; last done.
      rewrite big_sepL_app. iFrame "HuidSet". rewrite big_sepL_singleton.
      iNamed "Hspec". iFrame "∗#".
  }
  {
    iFrame. rewrite dom_empty_L big_sepS_empty take_0 big_sepL_nil //.
  }
  iIntros "[H work]".
  iNamed "H". iRight in "HuidSet". iRename "HuidSet" into "Hprops". iClear "Hwork".
  rewrite -> take_ge by word.
  wp_pures. wp_apply wp_slice_len. wp_pures. wp_apply wp_NewSlice.
  iIntros (outs0_sl) "outs0". wp_pures. iDestruct (own_slice_to_small with "outs0") as "outs0".

  (* allocate outs0 *)
  wp_pures.
  wp_apply wp_ref_of_zero; [done|].
  iIntros (i_ptr) "i". wp_pures.
  iAssert (
      ∃ outs0 (i : w64),
      "i" ∷ i_ptr ↦[uint64T] #i ∗
      "%Hi" ∷ ⌜ uint.nat i ≤ length work ⌝ ∗
      "outs0" ∷ own_slice_small outs0_sl ptrT (DfracOwn 1) (outs0 ++ (replicate (length work - uint.nat i) null)) ∗
      "%Houts0" ∷ ⌜ length outs0 = uint.nat i ⌝ ∗
      "Houts0" ∷ ([∗ list] out ∈ outs0, out ↦[struct.t mapper0Out] (zero_val (struct.t mapper0Out)))
    )%I with "[i outs0]" as "H".
  { iFrame. iExists []. replace (uint.nat _) with (length work) by word.
    rewrite Nat.sub_0_r. iSplitR; first word. iFrame.
    rewrite big_sepL_nil /=. done. }

  wp_forBreak_cond.
  iNamed "H".
  wp_load. wp_apply wp_slice_len. wp_pures. wp_if_destruct.
  { (* continue loop *)
    wp_pures.
    wp_apply wp_allocStruct; [val_ty|].
    iIntros (out0_ptr) "out0". wp_pures.
    wp_load. wp_apply (wp_SliceSet (V:=loc) with "[outs0]").
    { iFrame. iPureIntro.
      apply lookup_lt_is_Some. rewrite length_app length_replicate.
      word. }
    iIntros "outs0".
    wp_pures. wp_load. wp_store. iLeft. iSplitR; first done.
    rewrite insert_app_r_alt; last word. rewrite Houts0. rewrite Nat.sub_diag.
    rewrite insert_replicate_lt; last word. rewrite replicate_0. rewrite app_nil_l.
    change (?x :: ?y) with ([x] ++ y).
    rewrite app_assoc.
    iDestruct (big_sepL_snoc _ _ out0_ptr with "[$Houts0 $out0]") as "H".
    iFrame "∗". simpl. iSplitR; first word. iSplitL; last len.
    iModIntro. iApply to_named. iExactEq "outs0". f_equal. f_equal. f_equal.
    word.
  }
  (* done with loop *)
  iModIntro. iRight. iSplitR; first done.
  wp_pures.
  replace (uint.nat i) with (length work) in Houts0 |- * by word.
  rewrite Nat.sub_diag replicate_0 app_nil_r.
  set (wfrac := ((1/2)/ pos_to_Qp (Pos.of_nat (1 + length work)))%Qp).
  eset (waitP:=
          (λ (i : w64),
             Server.own_phys s wfrac st ∗
             (∃ w out0 mo (req_ptr : loc) req,
                 "%Hw" ∷ ⌜ work !! (uint.nat i) = Some w ⌝ ∗
                 "#Req" ∷ w ↦[Work::"Req"]□ #req_ptr ∗
                 "#HReq" ∷ WQReq.is_own req_ptr req ∗
                 "%Hout0" ∷ ⌜ outs0 !! (uint.nat i) = Some out0 ⌝ ∗
                 "#out0" ∷ mapper0Out.is_own out0 mo ∗
                 "#out0_crypto" ∷ is_mapper0Out_crypto γ st req mo)
          )%I).

  wp_apply (wp_NewWaitGroup nroot waitP). iIntros (wg γwg) "Hwg".
  iDestruct (own_WaitGroup_to_is_WaitGroup with "[$]") as "#His_wg".
  wp_pures. wp_store. clear dependent i.

  wp_pures.
  iAssert (∃ (i : w64),
              "i" ∷ i_ptr ↦[uint64T] #i ∗
              "%Hi" ∷ ⌜ uint.Z i ≤ length work ⌝ ∗
              "Hprops" ∷ ([∗ list] w ∈ work, prop w) ∗
              "Houts0" ∷ ([∗ list] out ∈ drop (uint.nat i) outs0, out ↦[struct.t mapper0Out] zero_val (struct.t mapper0Out)) ∗
              "Hwg" ∷ own_WaitGroup nroot wg γwg i waitP ∗
              "Hphys" ∷ Server.own_phys s (pos_to_Qp (Pos.of_nat (1 + length work - uint.nat i)) * wfrac) st ∗
              "_" ∷ True
          )%I with "[i Hprops Hwg Houts0 Hown]" as "H".
  { iFrame "i". rewrite drop_0 /wfrac Nat.sub_0_r Qp.mul_div_r. iFrame. word. }
  wp_forBreak_cond.
  iNamed "H".
  wp_load. wp_apply wp_slice_len. wp_pures. wp_if_destruct.
  { (* not done with loop *)
    wp_pures. wp_load.
    opose proof (list_lookup_lt work (uint.nat i) ltac:(word)) as [w Hlookup].
    wp_apply (wp_SliceGet with "[$work]"); first done.
    iIntros "work". wp_pures.
    iDestruct (big_sepL_lookup_acc with "Hprops") as "[Hprop Hprops]".
    { done. }
    iNamedSuffix "Hprop" "_prop".
    wp_loadField. wp_pures.
    iDestruct (struct_fields_split with "resp_prop") as "H". iNamedSuffix "H" "_prop".
    wp_loadField. wp_pures.
    iCombineNamed "*_prop" as "Hprop".
    iSpecialize ("Hprops" with "[Hprop]").
    { iNamed "Hprop". iFrame "∗#". iApply struct_fields_split. iFrame. done. }
    wp_load. wp_apply (wp_SliceGet with "[$work]"); first done.
    iIntros "work". wp_loadField. wp_pures.
    opose proof (list_lookup_lt outs0 (uint.nat i) ltac:(word)) as [out0 Ho_lookup].
    wp_load. wp_apply (wp_SliceGet with "[$outs0]"); first done.
    iIntros "outs0". wp_pures.
    wp_apply (wp_WaitGroup__Add with "[$]").
    { word. }
    iIntros "[Hwg Hwg_tok]". wp_pures.
    replace (pos_to_Qp (Pos.of_nat _) * wfrac)%Qp with
      (wfrac + (pos_to_Qp (Pos.of_nat (1 + length work - uint.nat (word.add i (W64 1)))) * wfrac))%Qp.
    2:{
      replace (uint.nat (word.add _ _)) with (uint.nat i + 1)%nat by word.
      rewrite Nat.sub_add_distr.
      replace (1 + _ - _ - 1)%nat with (length work - uint.nat i)%nat by lia.
      rewrite <- Nat.add_sub_assoc by lia.
      rewrite -> Nat2Pos.inj_add by word.
      rewrite -pos_to_Qp_add.
      change (Pos.of_nat 1) with 1%positive.
      rewrite Qp.mul_add_distr_r left_id //.
    }
    iDestruct (Server.split with "Hphys") as "[Hphys2 Hphys]".
    erewrite -> (drop_S _ _ (uint.nat i)); last done.
    iDestruct "Houts0" as "[Hout0 Houts0]".
    wp_apply (wp_fork with "[Hwg_tok Hphys2 Hout0]").
    {
      iNext. wp_apply (wp_Server__mapper0 with "[-Hwg_tok]").
      { iFrame "∗#". }
      iIntros "*". iNamed 1. wp_pures. wp_apply (wp_WaitGroup__Done with "[-]"); last done.
      iFrame "His_wg". iFrame "∗#%".
    }
    wp_pures. wp_load. wp_store. iLeft. iSplitR; first done.
    iModIntro. iFrame.
    iSplitR; first word.
    replace (uint.nat (word.add i _)) with (S (uint.nat i)) by word.
    iFrame.
  }
  iModIntro. iRight. iSplitR; first done.
  wp_apply (wp_WaitGroup__Wait with "[$]").
  wp_pures. replace (uint.nat i) with (length work) by word.
  iIntros "HwaitP". wp_pures. wp_loadField. wp_apply (write_wp_Mutex__Lock with "[$]").
  iIntros "[Hlocked Hown2]". wp_pures. wp_apply (wp_NewMap byte_string Slice.t).
  iIntros (upd_ptr) "upd". wp_pures. wp_store. clear dependent i.
  (* Time *) wp_pures. (* quite slow. *)
  iClear "His_wg". unfold waitP.
  iDestruct (big_sepS_impl with "HwaitP []") as "HwaitP".
  {
    instantiate (1:=λ x, ((⌜ length work ≤ uint.nat x ⌝ ∨ Server.own_phys s wfrac st) ∗
                          (⌜ length work ≤ uint.nat x ⌝ ∨ _))%I).
    iIntros "!# * % H".
    iDestruct "H" as "[%|H]".
    { iSplitR; by iLeft. }
    iDestruct "H" as "[$ H]".
    iRight. iExact "H".
  }
  iDestruct (big_sepS_sep with "HwaitP") as "[Hphys2 #HwaitP]".
  replace (1 + length work - length work)%nat with 1%nat by word.
  rewrite left_id.

  (* FIXME: lemma for combining server ownership into 1%Qp. *)
  iAssert (
      "Hghost" ∷ own_Server_hist γ 1%Qp st ∗
      "Hnvers" ∷ own_Server_nvers γ 1%Qp st ∗
      "Hphys" ∷ Server.own_phys s 1%Qp st ∗
      "#Hcrypto" ∷ is_Server_crypto γ st
    )%I with
    "[Hphys Hown2 Hphys2]" as "H".
  {
    iClear "#".
    set (n:=(length work)) in *.
    subst wfrac.
    clear -n. generalize dependent n. intros.
    admit.
  }
  iNamed "H".

  iClear "Houts0 uidSet".
  subst prop.
  eset (prop :=
         (λ (w : loc),
            ∃ (req_ptr resp : loc) Ψ γtok req nVers cli_next_ep,
              "resp" ∷ resp ↦[struct.t WQResp] _ ∗
              "#Resp" ∷ w ↦[Work::"Resp"]□ #resp ∗
              "#Req" ∷ w ↦[Work::"Req"]□ #req_ptr ∗
              "#HReq" ∷ WQReq.is_own req_ptr req ∗
              "Hvers" ∷ own_num_vers γ req.(WQReq.Uid) nVers ∗
              "#Hlb_ep" ∷ is_epoch_lb γ cli_next_ep ∗
              "HΨ" ∷ wq_post γ req nVers cli_next_ep Ψ ∗
              "#His_work" ∷ is_Work w γtok Ψ ∗
              "%HnVers" ∷ ⌜ nVers = default (W64 0) (userState.numVers <$> st.(Server.userInfo) !! req.(WQReq.Uid)) ⌝
         )%I).

  eset (prop' :=
         (λ (w : loc),
            ∃ (req_ptr resp : loc) Ψ γtok req nVers cli_next_ep,
              "resp" ∷ resp ↦[struct.t WQResp] _ ∗
              "#Resp" ∷ w ↦[Work::"Resp"]□ #resp ∗
              "#Req" ∷ w ↦[Work::"Req"]□ #req_ptr ∗
              "#HReq" ∷ WQReq.is_own req_ptr req ∗
              "Hvers" ∷ own_num_vers γ req.(WQReq.Uid) (word.add nVers (W64 1))∗
              "#Hlb_ep" ∷ is_epoch_lb γ cli_next_ep ∗
              "HΨ" ∷ wq_post γ req nVers cli_next_ep Ψ ∗
              "#His_work" ∷ is_Work w γtok Ψ ∗
              "%HnVers" ∷ ⌜ nVers = default (W64 0) (userState.numVers <$> st.(Server.userInfo) !! req.(WQReq.Uid)) ⌝
         )%I).

  iDestruct (big_sepL_iter _ _ (λ _ x, prop x) with "Hnvers Hprops []") as "[Hnvers Hprops]".
  {
    iApply big_sepL_forall_1. iIntros "!# * Hw Hnvers". iNamed 1.
    iDestruct (ghost_nvers_agree with "[$] [$]") as %Hagree. iFrame "∗#%".
  }
  iAssert (
      ∃ (i : w64) upd_sl upd_pks openKeyMap userInfo,
      let st' := (st <| Server.keyMap := upd ∪ st.(Server.keyMap) |> <| Server.userInfo := userInfo |>) in
      "i" ∷ i_ptr ↦[uint64T] #i ∗
      "upd" ∷ own_map upd_ptr (DfracOwn 1) upd_sl ∗
      "#Hupd" ∷ ([∗ map] u_sl; u ∈ upd_sl; upd, own_slice_small u_sl byteT DfracDiscarded u) ∗
      "Hphys" ∷ Server.own_phys s 1 st' ∗
      "Hnvers" ∷ own_Server_nvers γ 1 st' ∗
      "Hprops" ∷ ([∗ list] w ∈ drop (uint.nat i) work, prop w) ∗
      "Hprops'" ∷ ([∗ list] w ∈ take (uint.nat i) work, prop' w) ∗
      "#HopenKeyMap" ∷ is_map_relation γ st'.(Server.keyMap) openKeyMap ∗
      "%HkeyMapLatest" ∷ (⌜ ∀ uid,
                            match st'.(Server.userInfo) !! uid with
                            | Some (userState.mk numVers pk) =>
                                snd <$> openKeyMap !! (uid, (word.sub numVers (W64 1))) = Some pk ∧
                                (∀ ver, (uid, ver) ∈ dom openKeyMap ↔ uint.nat ver < uint.nat numVers)
                            | None => (∀ ver, (uid, ver) ∉ dom openKeyMap)
                            end ⌝)
    )%I with "[i upd Hphys Hnvers Hprops]" as "H".
  { iFrame "i". rewrite drop_0 take_0. iExists ∅, ∅. rewrite left_id.
    iNamed "Hcrypto". iFrame "∗#%". simpl. rewrite big_sepM2_empty //. }
  wp_forBreak_cond.
  iNamed "H".
  wp_load. wp_apply wp_slice_len. wp_if_destruct.
  {
    wp_pures. wp_load.
    opose proof (list_lookup_lt work (uint.nat i) ltac:(word)) as [w Hlookup].
    wp_apply (wp_SliceGet with "[$work]"); first done. iIntros "work".
    erewrite drop_S; last done. iDestruct "Hprops" as "[Hprop Hprops]".
    iNamedSuffix "Hprop" "_prop". wp_loadField. wp_pures.
    iDestruct (struct_fields_split with "resp_prop") as "H". iNamedSuffix "H" "_prop".
    wp_loadField. wp_pures. wp_load.
    wp_apply (wp_SliceGet with "[$work]"); first done. iIntros "work".
    wp_loadField. wp_pures. wp_load.
    opose proof (list_lookup_lt outs0 (uint.nat i) ltac:(word)) as [out0 Ho_lookup].
    wp_apply (wp_SliceGet with "[$outs0]"); first done. iIntros "outs0".
    wp_pures.
    iDestruct (big_sepS_elem_of _ _ i with "HwaitP") as "H".
    { set_solver. }
    iDestruct "H" as "[%Hbad|H]".
    { exfalso. word. }
    iNamed "H".
    replace (out1) with (out0) by naive_solver.
    replace (w0) with (w) by naive_solver. clear dependent w0 out1.
    iDestruct (struct_field_pointsto_agree with "Req_prop Req") as %Heq.
    replace req_ptr0 with req_ptr by naive_solver.
    iDestruct (WQReq.inj with "HReq HReq_prop") as %->.
    clear dependent req_ptr0. iClear "HReq".
    iNamed "out0".
    wp_loadField. wp_pures. wp_loadField. iNamed "Hphys". wp_loadField.
    wp_apply (wp_Tree__Put with "[$HkeyMap]").
    { iFrame "#". }
    iIntros "*". iNamed 1. wp_pures.
    iNamed "out0_crypto".
    iDestruct (is_vrf_out_len with "HlatestVrfHash") as %Hlen.
    iSpecialize ("Herr" with "[//]"). iNamed "Herr".
    iRight in "Hgenie". iSpecialize ("Hgenie" with "[//]"). iDestruct "Hgenie" as %->.
    wp_apply std_proof.wp_Assert; [done|]. wp_pures.
    wp_loadField. wp_apply wp_StringFromBytes.
    { iFrame "#". }
    iIntros "_". wp_apply (wp_MapInsert byte_string Slice.t with "[$upd]").
    { done. }
    iIntros "upd". wp_pures. iNamed "HReq_prop".
    wp_loadField. wp_loadField. wp_apply (wp_MapGet with "[$HuserInfo_map]").
    iIntros "* [%Hulookup HuserInfo_map]". wp_pures. wp_apply wp_ref_to; [val_ty|].
    iIntros (user_ptr) "user". wp_pures. wp_load.
    set (st' := (st <| Server.keyMap := upd ∪ st.(Server.keyMap) |> <| Server.userInfo := userInfo |>)) in *.
    wp_bind (if: _ then _ else _)%E.
    set (post:=(
                 ∃ (user : loc),
                   "user" ∷ user_ptr ↦[ptrT] #user ∗
                   "Huser" ∷ userState.own user (default (userState.mk (W64 0) []) (st'.(Server.userInfo) !! req.(WQReq.Uid))) (DfracOwn 1) ∗
                   "HuserInfo_own" ∷ ([∗ map] l;x ∈ delete req.(WQReq.Uid) userInfo_phys;delete req.(WQReq.Uid) st'.(Server.userInfo),
                                        userState.own l x (DfracOwn 1))
               )%I).

    wp_apply (wp_wand _ _ _ (λ _, post) with "[user HuserInfo_own]").
    {
      destruct ok.
      - apply map_get_true in Hulookup.
        iDestruct (big_sepM2_lookup_l_some with "[$]") as "%H".
        { eassumption. }
        destruct H as [userState Hlookup2].
        iDestruct (big_sepM2_delete with "HuserInfo_own") as "[Huinfo HuserInfo_own]"; [eassumption.. | ].
        wp_if_destruct.
        + (* impossible *)
          iNamedSuffix "Huinfo" "_uinfo".
          iDestruct (struct_field_pointsto_not_null with "numVers_uinfo") as %Hnot_null; done.
        + iFrame. rewrite /= in Hlookup2. rewrite Hlookup2. by iFrame.
      - apply map_get_false in Hulookup as [Hulookup ?]. subst. rewrite bool_decide_true //.
        iDestruct (big_sepM2_lookup_l_none with "HuserInfo_own") as %Hlookup2; [eassumption|].
        wp_pures. wp_apply wp_allocStruct; [val_ty|]. iIntros (u) "u".
        iDestruct (struct_fields_split with "u") as "H". iNamed "H".
        wp_store. iFrame. rewrite !delete_notin //. iFrame.
        rewrite zero_slice_val. rewrite Hlookup2. simpl. iFrame.
        iDestruct own_slice_small_nil as "$"; done.
    }
    iIntros (?) "Hpost". iNamed "Hpost". clear post. iNamedSuffix "Huser" "_uinfo".
    wp_pures. wp_pures. wp_load.
    wp_loadField. wp_load. wp_storeField.
    wp_loadField. wp_load. wp_storeField.
    wp_load. wp_loadField. wp_loadField. wp_apply (wp_MapInsert with "HuserInfo_map").
    { done. } iIntros "HuserInfo_map". wp_pures. wp_load. wp_store.
    iLeft. iSplitR; first done. unfold typed_map.map_insert.
    iDestruct (big_sepM2_insert_2 _ _ _
                 mo.(mapper0Out.latestVrfHash) _ mo.(mapper0Out.mapVal) with "[] Hupd") as "Hupd2".
    { simpl. iFrame "#". }
    iFrame "HΦ work outs0 Hlocked".
    iMod (ghost_nvers_put with "Hvers_prop Hnvers") as "(%HnversEq & Hvers_prop & Hnvers)".
    iCombineNamed "*_prop" as "Hprop'".
    iDestruct (big_sepL_snoc with "[$Hprops' Hprop']") as "Hprops'".
    2: rewrite -take_S_r //.
    1:{
      iNamed "Hprop'". iFrame "∗#%". instantiate (1:=(zero_val (struct.t WQResp))).
      iApply struct_fields_split. iFrame. done.
    }
    iFrame "∗#". instantiate (1:=req.(WQReq.Pk)). simpl.
    rewrite insert_union_l.
    replace (uint.nat (word.add _ _)) with (S (uint.nat i)) by word.
    iFrame. iExists _. iModIntro.
    iCombineNamed "*_uinfo" as "Huinfo".
    iSplitL "HuserInfo_own Huinfo".
    { iApply to_named.
      iDestruct (big_sepM2_insert _ _ _ req.(WQReq.Uid) with "[$HuserInfo_own Huinfo]") as "H".
      { apply lookup_delete. }
      { apply lookup_delete. }
      {
        iNamed "Huinfo". iFrame. simpl.
        instantiate (1:=ltac:(econstructor)). simpl.
        eauto with iFrame.
      }
      rewrite !insert_delete_insert. simpl.
      subst. iFrame. iExactEq "H".
      f_equal. f_equal. f_equal. f_equal. simpl.
      rewrite -HnversEq.
      by destruct lookup in |- *.
    }
    instantiate (1:=<[(req.(WQReq.Uid), nVers) := (_, _)]>openKeyMap).
    iSplitR.
    {
      unfold is_map_relation. clear Hlookup.
      iIntros "!# *".
      destruct uid_ver as [uid ver].
      destruct (decide (uid = req.(WQReq.Uid) ∧ ver = nVers)) as [[? ?]|].
      - subst uid ver nVers. rewrite lookup_insert. iFrame "#".
        simpl. iPureIntro. rewrite -insert_union_l lookup_insert. simpl.
        rewrite HmapVal. f_equal.
      - rewrite lookup_insert_ne; last naive_solver.
        iSpecialize ("HopenKeyMap" $! (uid, ver)).
        iDestruct "HopenKeyMap" as "#H".
        destruct (openKeyMap !! _) eqn:Hlookup.
        + iDestruct "H" as (???) "($ & $ & $ & %H)".
          destruct (decide (label = mo.(mapper0Out.latestVrfHash))).
          * iExFalso. subst. iDestruct "HlatestVrfHash" as "-#Hbad".
            iDestruct (is_vrf_out_inj with "Hbad [$]") as "%Heq".
            exfalso. rewrite /encode_uid_ver /= in Heq.
            eassert (MapLabelPre.mk uid _ = MapLabelPre.mk req.(WQReq.Uid) _) as [=->].
            { eapply MapLabelPre.inj; done. }
            naive_solver.
          * rewrite -insert_union_l lookup_insert_ne //.
        + iIntros (?) "#Hbad". iSpecialize ("H" with "[$]").
          destruct (decide (label = mo.(mapper0Out.latestVrfHash))).
          * subst. iDestruct (is_vrf_out_inj with "Hbad HlatestVrfHash") as "%Heq".
            exfalso. rewrite /encode_uid_ver /= in Heq.
            eassert (MapLabelPre.mk uid _ = MapLabelPre.mk req.(WQReq.Uid) _) as [=->].
            { eapply MapLabelPre.inj; done. }
            naive_solver.
          * rewrite -insert_union_l lookup_insert_ne //.
    }
    iPureIntro.
    assert (uint.nat nVers < uint.nat (word.add nVers (W64 1))) as HnoOverflow.
    { admit. } (* FIXME: nver overflow *)
    intros uid. specialize (HkeyMapLatest uid).
    destruct (decide (uid = req.(WQReq.Uid))).
    - subst uid. rewrite lookup_insert.
      replace (word.sub _ _) with (nVers) by word.
      rewrite lookup_insert /=. rewrite -Hpk. split; first done.
      rewrite /st' /= in HkeyMapLatest.
      intros ver. rewrite dom_insert.
      rewrite elem_of_union. rewrite elem_of_singleton.
      destruct (userInfo !! req.(WQReq.Uid)).
      + destruct t. simpl in *. subst numVers.
        destruct (decide (ver = nVers)).
        *  subst ver. split.
          { intros _. word. }
          intros ?. by left.
        * destruct HkeyMapLatest as [_ HkeyMapLatest].
          split.
          { intros [Hbad|?]; first naive_solver. apply HkeyMapLatest in H. word. }
          intros ?.
          right. apply HkeyMapLatest. word.
      + simpl in HnversEq. subst. rewrite -HnversEq.
        replace (uint.nat (word.add _ _)) with 1%nat by word.
        destruct (decide (ver = (W64 0))).
        * subst ver. split; first done.
          intros _. by left.
        * split.
          { intros ?. destruct H as [Hbad|?]; first naive_solver.
            apply HkeyMapLatest in H. word. }
          intros ?. word.
    - rewrite lookup_insert_ne //. clear Hlookup.
      rewrite /st' /= in HkeyMapLatest.
      destruct (userInfo !! uid) eqn:Hlookup.
      + destruct t. rewrite lookup_insert_ne //; last naive_solver.
        split; first naive_solver. intros ver. destruct HkeyMapLatest as [_ HkeyMapLatest].
        rewrite dom_insert elem_of_union. split.
        * intros ?. apply HkeyMapLatest. set_solver.
        * intros ?. right. apply HkeyMapLatest. done.
      + intros ?. set_solver.
  }
  iModIntro. iRight. iSplitR; first done.
  wp_pures. iNamedSuffix "His_srv" "_srv".
Admitted.

End proof.
