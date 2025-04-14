From New.experiments Require Import glob.
From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.pav Require Import kt.

From Perennial.program_proof.pav Require Import core cryptoffi cryptoutil serde merkle auditor.
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

Section proof.
Context `{!heapGS Σ, !pavG Σ}.

Record Server_names :=
  {
    auditor_gn : gname;
    sig_pk : list w8;
    vrf_pk : list w8;
    commitSecret : list w8;
  }.

Implicit Types γ : Server_names.

Definition encode_uid_ver uid_ver :=
  (MapLabelPre.encodesF $ MapLabelPre.mk uid_ver.1 uid_ver.2).

(* Abstraction relation between the map in the merkle tree (which has hidden
   labels and pks) and a map from (uid,ver) pairs to (epoch,pk). *)
Definition is_map_relation γ (mₗ : gmap (list w8) (list w8))
  (mₕ : gmap (uid_ty * ver_ty) (epoch_ty * pk_ty)) : iProp Σ :=
  (* A (uid_ver, epoch_pk) pair is in the abstract map iff a corresponding
     hidden element is in the physical map *)
  □(∀ uid_ver o_epoch_pk,
      ⌜ mₕ !! uid_ver = o_epoch_pk ⌝ -∗
      ∃ label,
        is_vrf_out γ.(vrf_pk) (encode_uid_ver uid_ver) label ∗
        match o_epoch_pk with
        | Some epoch_pk =>
            (∃ rand commit,
                is_hash (γ.(commitSecret) ++ label) rand ∗
                is_hash (CommitOpen.encodesF (CommitOpen.mk epoch_pk.2 rand)) commit ∗
                ⌜ mₗ !! label = Some (MapValPre.encodesF $ MapValPre.mk epoch_pk.1 commit) ⌝)
        | None => ⌜ mₗ !! label = None ⌝
        end
    ).


Instance is_map_relation_pers γ mₗ mₕ : Persistent (is_map_relation γ mₗ mₕ) := _.

Context `{!epoch_versioned_mapG Σ}.


Definition own_Server_ghost γ st : iProp Σ :=
  ∃ gs, (* TODO: rename to something better than [gs]. *)
  (* Copied from auditor.v *)
  "Hauditor" ∷ mono_list_auth_own γ.(auditor_gn) 1 gs ∗
  "#Hinv_gs" ∷ gs_inv gs ∗
  "%HkeyMap_ghost" ∷ ⌜ st.(Server.keyMap) = lower_map (default ∅ (last gs.*1)) ⌝ ∗
  "%Hdigs_gs" ∷ ⌜ gs.*2 = servEpochInfo.dig <$> st.(Server.epochHist) ⌝ ∗

  "%HepochHistNoOverflow" ∷ ⌜ length st.(Server.epochHist) = uint.nat (length st.(Server.epochHist)) ⌝
  (* TODO: server should own [numVers] auth to ensure cryptographic correctness. *)
.

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
                            (foldl union (∅ : gmap _ _)
                               (servEpochInfo.updates <$> st.(Server.epochHist)))
                            ⌝) ∗

  "%HepochHistLast" ∷ ⌜ last st.(Server.epochHist) = Some last_info ⌝
.

(** Proposition guarded by RWMutex. *)
Definition own_Server γ s q : iProp Σ :=
  ∃ (st : Server.t),
    "Hphys" ∷ Server.own_phys s (q/2) st ∗
    "#Hcrypto" ∷ is_Server_crypto γ st ∗
    "Hghost" ∷ own_Server_ghost γ st.

Definition is_Server γ s : iProp Σ :=
  ∃ commitSecret_sl (mu vrfSk_ptr : loc),
  "#commitSecret" ∷ s ↦[Server :: "commitSecret"]□ (slice_val commitSecret_sl) ∗
  "#commitSecret_sl" ∷ own_slice_small commitSecret_sl byteT DfracDiscarded γ.(commitSecret) ∗
  "#mu" ∷ s ↦[Server :: "mu"]□ #mu ∗
  "#Hmu" ∷ is_rwlock nroot #mu (λ q, own_Server γ s (q / 2)) ∗
  "#vrfSk" ∷ s ↦[Server :: "vrfSk"]□ #vrfSk_ptr ∗
  "#HvrfSk" ∷ is_vrf_sk vrfSk_ptr γ.(vrf_pk) ∗
  "_" ∷ True.

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
      own_slice_small out_sl byteT (DfracOwn 1) out ∗
      own_slice_small proof_sl byteT (DfracOwn 1) proof ∗
      is_vrf_out pk (enc_label_pre uid ver) out ∗
      is_vrf_proof pk (enc_label_pre uid ver) proof
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
    iIntros "* (Hout_sl & Hproof_sl & #Hvrf_out & #Hvrf_proof)".
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
      iSpecialize ("HkeyMap" $! (uid, ver) (Some epoch_pk)).
      iDestruct ("HkeyMap" with "[//]") as (?) "(#Hvrf & (% & % & Hrand & Hcommit & %Hlookup))".
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
  {{{ commit_sl (commit : list w8), RET (slice_val commit_sl);
      own_slice_small commit_sl byteT (DfracOwn 1) commit ∗
      own_slice_small secret_sl byteT dqs secret ∗
      own_slice_small label_sl byteT dql label ∗
      is_hash (secret ++ label) commit
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
  iIntros "* (Hout_sl & Hproof_sl & #Hvrf_out & #Hvrf_proof)".
  wp_pures. wp_apply (wp_Tree__Prove with "[$Htree $Hout_sl]").
  iIntros "*". iNamed 1. wp_pures.
  iNamed "Hcrypto".

  specialize (HkeyMapLatest uid).
  subst userState. destruct lookup eqn:Hlookup in HkeyMapLatest, Heqb.
  2:{ simpl in *. exfalso. word. }
  destruct t as [numVers plainPk]. simpl in *.
  unfold is_map_relation. iDestruct "HkeyMap" as "#HkeyMap".
  destruct HkeyMapLatest as [HkeyMapLatest _].
  destruct lookup eqn:Hlookup2 in HkeyMapLatest.
  2:{ simpl in *. exfalso. done. }
  destruct p. simpl in *. subst.
  iDestruct ("HkeyMap" $! (uid, _) _) as "HkeyMap2".
  iSpecialize ("HkeyMap2" with "[//]").
  iDestruct "HkeyMap2" as (?) "(#Hlabel & (% & % & #Hrand & #Hcommit & %))".
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
  iIntros "* (Hcommit_sl & HcommitSecret & Hsl_label & #Hhash)".
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
  iDestruct (is_hash_det with "Hrand Hhash") as %Heq. subst.
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
  iIntros "* (Hout_sl & Hproof_sl & #Hvrf_out & #Hvrf_proof)".
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
      iDestruct "HkeyMap" as (?) "(Hvrf & %Hnone)".
      iDestruct (is_vrf_out_det with "Hvrf Hvrf_out") as %Heq. subst. exfalso.
      naive_solver.
    - rewrite Hlookup /=. iSpecialize ("HkeyMap" $! (uid, W64 0) None with "[]").
      { iPureIntro. by apply not_elem_of_dom_1. }
      iDestruct "HkeyMap" as (?) "(Hvrf & %Hnone)".
      iDestruct (is_vrf_out_det with "Hvrf Hvrf_out") as %Heq. subst. exfalso.
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

Definition is_epoch_lb γ (epoch : w64) : iProp Σ :=
  ∃ (gs : list (gmap (list w8) (w64 * list w8) * list w8)),
    mono_list_lb_own γ.(auditor_gn) gs ∗ ⌜ uint.nat epoch + 1 ≤ length gs ⌝.

Lemma ghost_latest_epoch γ st cli_ep :
  let latest_epoch := (W64 (length st.(Server.epochHist) - 1)) in
  is_epoch_lb γ cli_ep ∗
  own_Server_ghost γ st
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
  wp_apply (read_wp_Mutex__Unlock with "[$Hmu Hown Hghost]").
  { iNamed "Hown". iFrame "∗#". }
  wp_pures.
  iApply "HΦ".
  instantiate (2:=ltac:(econstructor)). simpl.
  iFrame "∗#%". done.
Qed.

End proof.
