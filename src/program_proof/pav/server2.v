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
Context `{!heapGS Σ}.

Definition own ptr x d : iProp Σ :=
  ∃ plainPk_sl,
  "numVers" ∷ ptr ↦[userState :: "numVers"]{d} #x.(numVers) ∗
  "plainPk" ∷ ptr ↦[userState :: "plainPk"]{d} (slice_val plainPk_sl) ∗
  "plainPk_sl" ∷ own_slice_small plainPk_sl byteT DfracDiscarded x.(plainPk).
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
End defs.
End Server.

(* FIXME: remove *)
Section auditor_defs.
Context `{!heapGS Σ, !pavG Σ}.
Definition audit_epoch_post (γauditor : gname) (seen_dig : list w8) : iProp Σ.
Admitted.

End auditor_defs.

Section proof.
Context `{!heapGS Σ, !pavG Σ}.

Record Server_names :=
  {
    auditor_gn : gname;
    sig_pk : list w8;
    vrf_pk : list w8;
    commitSecret : list w8;
    epoch_gn : gname;
  }.

Implicit Types γ : Server_names.

Definition encode_uid_ver uid_ver :=
  (MapLabelPre.encodesF $ MapLabelPre.mk uid_ver.1 uid_ver.2).

Definition encode_pk γ pk :=
  (CommitOpen.encodesF $ CommitOpen.mk pk γ.(commitSecret)).

(* Abstraction relation between the map in the merkle tree (which has hidden
   labels and pks) and a map from (uid,ver) pairs to (epoch,pk). *)
Definition is_map_relation γ (mₗ : gmap (list w8) (list w8))
  (mₕ : gmap (uid_ty * ver_ty) (epoch_ty * pk_ty)) : iProp Σ :=
  (* A (uid_er, epoch_pk) pair is in the abstract map iff a corresponding
     hidden element is in the physical map *)
  □(∀ uid_ver epoch_pk,
     ⌜ mₕ !! uid_ver = Some epoch_pk ⌝ ∗-∗
     ∃ label commit,
       is_vrf_out γ.(vrf_pk) (encode_uid_ver uid_ver) label ∗
       is_hash (encode_pk γ epoch_pk.2) commit ∗
       ⌜ mₗ !! label = Some (MapValPre.encodesF $ MapValPre.mk epoch_pk.1 commit) ⌝).

Context `{!epoch_versioned_mapG Σ}.

(* TODO: server should own [numVers] auth to ensure cryptographic correctness. *)

(* TODO: separate invariant for "ghost auditor" inside of server. *)

(** Ghost ownership, invariants, and cryptographic knowledge related to mutable Server state. *)
Definition own_Server_ghost γ st : iProp Σ :=
  ∃ openKeyMap,
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
                            (foldl union (∅ : gmap _ _)
                               (servEpochInfo.updates <$> st.(Server.epochHist)))
                            ⌝) ∗

  "%HepochHistLast" ∷ ⌜ is_Some (last st.(Server.epochHist)) ⌝
.

(** Proposition guarded by RWMutex. *)
Definition own_Server γ s q : iProp Σ :=
  ∃ (st : Server.t),
    "Hphys" ∷ Server.own_phys s (q/2) st ∗
    "Hghost" ∷ own_Server_ghost γ st.

Definition is_Server γ s : iProp Σ :=
  ∃ commitSecret_sl (mu vrfSk_ptr : loc),
  "#commitSecret" ∷ s ↦[Server :: "commitSecret"]□ (slice_val commitSecret_sl) ∗
  "#commitSecret_sl" ∷ own_slice_small commitSecret_sl byteT DfracDiscarded γ.(commitSecret) ∗
  "#mu" ∷ s ↦[Server :: "mu"]□ #mu ∗
  "#Hmu" ∷ is_rwlock nroot #mu (λ q, own_Server γ s (q / 2)) ∗
  "#vrfSk" ∷ s ↦[Server :: "vrfSk"]□ #vrfSk_ptr ∗
  "#HvrfSk" ∷ is_vrf_sk vrfSk_ptr γ.(vrf_pk) ∗
  "_" ∷ True
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

Lemma wp_Server__Get γ ptr uid cli_ep :
  {{{
    "#Hserv" ∷ is_Server γ ptr ∗
    "#Hlb_ep" ∷ mono_nat_lb_own γ.(epoch_gn) cli_ep
  }}}
  Server__Get #ptr #uid
  {{{
    ptr_sigdig sigdig sl_hist ptr2_hist hist
    is_reg ptr_lat lat ptr_bound bound (nVers : w64),
    RET (#ptr_sigdig, slice_val sl_hist, #ptr_lat, #ptr_bound);
    "#Hlb_ep" ∷ mono_nat_lb_own γ.(epoch_gn) (uint.nat sigdig.(SigDig.Epoch)) ∗
    "%Hlt_ep" ∷ ⌜ Z.of_nat cli_ep ≤ uint.Z sigdig.(SigDig.Epoch) ⌝ ∗
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
  iNamed "Hghost".
  destruct HepochHistLast as [? HepochHistLast].
  wp_loadField. wp_apply (wp_getDig with "[$]").
  { done. }
  iIntros (?) "[H2_own #?]". wp_pures.
  wp_loadField. wp_load. wp_loadField.

  (* TODO: wp_getHist *)
Admitted.

Lemma wp_getHist γ keyMap keyMap_ptr uid (numVers : w64) vrfSk :
  {{{
      own_Tree keyMap_ptr keyMap (DfracOwn 1)
  }}}
    getHist #keyMap_ptr #uid #numVers #vrfSk
  {{{
      hist hist_ptrs hist_sl, RET (slice_val hist_sl);
      "Hhist_sl" ∷ own_slice_small hist_sl ptrT (DfracOwn 1) hist_ptrs ∗
      "Hhist" ∷ ([∗ list] l; mh ∈ hist_ptrs; hist, MembHide.own l mh (DfracOwn 1)) ∗
      "%Hlen_hist" ∷ ⌜ length hist = pred (uint.nat numVers) ⌝ ∗
      "#Hwish_hist" ∷
        (∀ dig, is_merkle_map keyMap dig -∗
                ([∗ list] ver ↦ x ∈ hist,
                   ∃ label, wish_checkMembHide γ.(vrf_pk) uid (W64 ver) dig x label))
  }}}.
Proof.
  iIntros (?) "Hpre HΦ".
  wp_rec. wp_pures. wp_if_destruct.
  { (* numVers = 0 *)
    replace (slice.nil) with (slice_val Slice.nil) by done. iApply "HΦ".
    iDestruct (own_slice_small_nil) as "$".
    { done. }
    instantiate (1:=[]).
    rewrite big_sepL2_nil.
    iSplitR; first done.
    iSplitR; first done.
    iModIntro. iIntros (?) "?". done.
  }
  wp_pures.
  wp_apply wp_NewSliceWithCap.
  { word. }
  iIntros (?) "Hhist_sl".
  wp_apply wp_ref_to; [val_ty|].
  iIntros (hist_ptr) "hist_ptr". wp_pures.
  wp_apply wp_ref_to; [val_ty|].
  iIntros (ver_ptr) "ver_ptr". wp_pures.

  iAssert (
      ∃ hist_sl hist (ver : w64) hist_ptrs,
        "hist_ptr" ∷ hist_ptr ↦[slice.T ptrT] (slice_val hist_sl) ∗
        "ver_ptr" ∷ ver_ptr ↦[uint64T] #ver ∗
        "Hhist_sl" ∷ own_slice hist_sl ptrT (DfracOwn 1) hist ∗
        "Hhist" ∷ ([∗ list] l; mh ∈ hist_ptrs; hist, MembHide.own l mh (DfracOwn 1)) ∗
        "%Hlen_hist" ∷ ⌜ length hist = (uint.nat ver) ⌝ ∗
        "#Hwish_hist" ∷
          (∀ dig, is_merkle_map keyMap dig -∗
                  ([∗ list] ver ↦ x ∈ hist,
                     ∃ label, wish_checkMembHide γ.(vrf_pk) uid (W64 ver) dig x label))
    )%I with "[Hhist_sl ver_ptr hist_ptr]" as "Hloop".
  {
    rewrite replicate_0.
    iFrame. iExists [], []. iFrame.
    rewrite big_sepL2_nil. iSplit; first done.
    iSplit; first done. iIntros (?) "?". done.
  }
  wp_apply wp_forUpto.
  Search For.
  Locate "for:".
  wp_forBreak_cond.
Qed.

End proof.
