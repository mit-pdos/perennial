From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.pav Require Import kt.

From Perennial.program_proof.pav Require Import chain misc cryptoffi merkle evidence invs rpc.
From Perennial.program_proof Require Import std_proof.
From iris.unstable.base_logic Require Import mono_list.
From stdpp Require Import gmap.
From Perennial.base_logic Require Import ghost_map.
From RecordUpdate Require Import RecordSet.

Module epochInfo.
Record t :=
  mk {
    keyMap: gmap (list w8) (list w8);
    prevLink: list w8;
    dig: list w8;
    link: list w8;
    linkSig: list w8;
  }.
End epochInfo.

Section epochInfo_defs.
Context `{!heapGS Σ, pavG Σ}.

Definition own_epochInfo ptr obj : iProp Σ :=
  ∃ ptr_map sl_prevLink sl_dig sl_link sl_linkSig d0 d1 d2 d3,
  "Hown_map" ∷ own_merkle ptr_map obj.(epochInfo.keyMap) ∗
  "Hsl_prevLink" ∷ own_slice_small sl_prevLink byteT d0 obj.(epochInfo.prevLink) ∗
  "Hsl_dig" ∷ own_slice_small sl_dig byteT d1 obj.(epochInfo.dig) ∗
  "Hsl_link" ∷ own_slice_small sl_link byteT d2 obj.(epochInfo.link) ∗
  "Hsl_linkSig" ∷ own_slice_small sl_linkSig byteT d3 obj.(epochInfo.linkSig) ∗

  "Hptr_map" ∷ ptr ↦[epochInfo :: "keyMap"] #ptr_map ∗
  "Hptr_prevLink" ∷ ptr ↦[epochInfo :: "prevLink"] (slice_val sl_prevLink) ∗
  "Hptr_dig" ∷ ptr ↦[epochInfo :: "dig"] (slice_val sl_dig) ∗
  "Hptr_link" ∷ ptr ↦[epochInfo :: "link"] (slice_val sl_link) ∗
  "Hptr_linkSig" ∷ ptr ↦[epochInfo :: "linkSig"] (slice_val sl_linkSig).

Definition is_epochInfo pk epoch γmap obj : iProp Σ :=
  "#Hmap" ∷ ghost_map_auth_pers γmap obj.(epochInfo.keyMap) ∗
  "#Hdig" ∷ is_dig obj.(epochInfo.keyMap) obj.(epochInfo.dig) ∗
  "#Hln" ∷ is_link epoch obj.(epochInfo.prevLink) obj.(epochInfo.dig)
    obj.(epochInfo.link) ∗
  "#Hsig" ∷ is_sig pk (servSepLink.encodesF (servSepLink.mk obj.(epochInfo.link)))
    obj.(epochInfo.linkSig).
End epochInfo_defs.

Module epochChain.
Record t :=
  mk {
    epochs: list epochInfo.t;
  }.
End epochChain.

Section epochChain_defs.
Context `{!heapGS Σ, !pavG Σ}.

#[export] Instance etaEpochChain : Settable _ := settable! epochChain.mk <epochChain.epochs>.

Definition own_epochChain ptr obj : iProp Σ :=
  ∃ sl_epochs ptr_epochs,
  "Hsl_epochs" ∷ own_slice_small sl_epochs ptrT (DfracOwn 1) ptr_epochs ∗
  "Hptr_epochs" ∷ ptr ↦[epochChain :: "epochs"] (slice_val sl_epochs) ∗
  "Hown_all_epochs" ∷ ([∗ list] ptr_epoch;epoch ∈ ptr_epochs;obj.(epochChain.epochs),
    own_epochInfo ptr_epoch epoch).

Definition is_epochChain pk γmaps obj : iProp Σ :=
  "#His_all_epochs" ∷ ([∗ list] k ↦ γmap;info ∈ γmaps;obj.(epochChain.epochs),
    is_epochInfo pk k γmap info) ∗
  "#His_chain" ∷ is_chain_all (epochInfo.dig <$> obj.(epochChain.epochs))
    (epochInfo.link <$> obj.(epochChain.epochs)).

Lemma wp_epochChain_put ptr_chain chain ptr_new_map new_map sl_sk pk γ γmaps γnew_map :
  {{{
    "Hown_chain" ∷ own_epochChain ptr_chain chain ∗
    "#His_chain" ∷ is_epochChain pk γmaps chain ∗
    "Hown_new_map" ∷ own_merkle ptr_new_map new_map ∗
    "Hown_sk" ∷ own_sk sl_sk pk (serv_sigpred γ) ∗
    "#Hview_new_map" ∷ ghost_map_auth_pers γnew_map new_map
  }}}
  epochChain__put #ptr_chain #ptr_new_map (slice_val sl_sk)
  {{{
    new_info, RET #();
    (* TODO: update notation conflicts with grove_prelude. *)
    let new_chain := set epochChain.epochs (λ x, x ++ [new_info]) chain in
    "%Htr_witness" ∷ ⌜ new_info.(epochInfo.keyMap) = new_map ⌝ ∗
    "Hown_chain" ∷ own_epochChain ptr_chain new_chain ∗
    "#is_chain" ∷ is_epochChain pk (γmaps ++ [γnew_map]) new_chain ∗
    "Hown_sk" ∷ own_sk sl_sk pk (serv_sigpred γ)
  }}}.
Proof. Admitted.
End epochChain_defs.

Module server.
Record t :=
  mk {
    mu: loc;
    γ: gname;
    sl_sk: Slice.t;
    pk: list w8;
  }.
End server.

Section server_defs.
Context `{!heapGS Σ, !pavG Σ}.

Definition own_server ptr obj : iProp Σ :=
  ∃ ptr_updates (updates : gmap (list w8) (list w8)) sl_updates ptr_chain γmaps γupdates chain,
  (* ghost state, the other half owned by global_inv. *)
  "Hγmaps" ∷ mono_list_auth_own obj.(server.γ) (1/2) (γmaps ++ [γupdates]) ∗
  (* need ghost_map_auth for next mpa bc we're continuously updating it.
  for older trees, epoch chain has ghost_map_auth_pers. *)
  "Hview_updates" ∷ ghost_map_auth γupdates (1/2) updates ∗

  "Hown_sk" ∷ own_sk obj.(server.sl_sk) obj.(server.pk) (serv_sigpred obj.(server.γ)) ∗

  "Hown_chain" ∷ own_epochChain ptr_chain chain ∗
  "%Hlen_nz_chain" ∷ ⌜ length chain.(epochChain.epochs) > 0 ⌝ ∗
  "#His_epochChain" ∷ is_epochChain obj.(server.pk) γmaps chain ∗
  "Hptr_chain" ∷ ptr ↦[server :: "chain"] #ptr_chain ∗

  (* exists (idS, sl_v) map that owns the respective (id, v) map. *)
  "#Hsl_updates" ∷ ([∗ map] id ↦ sl_v;v ∈ (kmap string_to_bytes sl_updates);updates,
    "Hsl_v" ∷ own_slice_small sl_v byteT DfracDiscarded v ∗
    "%Hlen_id" ∷ ⌜ length id = hash_len ⌝ ) ∗
  "Hown_updates" ∷ own_map ptr_updates (DfracOwn 1) sl_updates ∗
  "Hupdates" ∷ ptr ↦[server :: "updates"] #ptr_updates.

Definition is_server ptr obj : iProp Σ :=
  "#Hptr_mu" ∷ ptr ↦[server :: "mu"]□ #obj.(server.mu) ∗
  "#HmuR" ∷ is_lock nroot #obj.(server.mu) (own_server ptr obj) ∗
  "#Hinv" ∷ inv nroot (global_inv obj.(server.γ)) ∗
  "#Hptr_sk" ∷ ptr ↦[server :: "sk"]□ (slice_val obj.(server.sl_sk)).
End server_defs.

Section misc.
Context `{!heapGS Σ, !pavG Σ}.
Definition is_servPutReply pk id val (obj : servPutReply.t) : iProp Σ :=
  (if negb obj.(servPutReply.error) then
    ∃ link,
    "#Hlink" ∷ is_link (word.sub obj.(servPutReply.putEpoch) (W64 1))
      obj.(servPutReply.prevLink) obj.(servPutReply.dig) link ∗
    "#His_linkSig" ∷ is_sig pk (servSepLink.encodesF (servSepLink.mk link))
      obj.(servPutReply.linkSig) ∗
    "#His_putSig" ∷ is_sig pk
      (servSepPut.encodesF (servSepPut.mk obj.(servPutReply.putEpoch) id val))
      obj.(servPutReply.putSig)
  else True)%I.
End misc.

Section proofs.
Context `{!heapGS Σ, !pavG Σ}.

Lemma wp_server_put ptr_serv obj_serv sl_id sl_val (id val : list w8) d0 d1 :
  {{{
    "His_serv" ∷ is_server ptr_serv obj_serv ∗
    "Hid" ∷ own_slice_small sl_id byteT d0 id ∗
    "Hval" ∷ own_slice_small sl_val byteT d1 val
  }}}
  server__put #ptr_serv (slice_val sl_id) (slice_val sl_val)
  {{{
    ptr_reply reply, RET #ptr_reply;
    "Hown_reply" ∷ servPutReply.own ptr_reply reply ∗
    "#His_reply" ∷ is_servPutReply obj_serv.(server.pk) id val reply
  }}}.
Proof.
  rewrite /server__put.
  iIntros (Φ) "H HΦ". iNamed "H". iNamed "His_serv".

  wp_loadField.
  wp_apply (wp_Mutex__Lock with "[$HmuR]").
  iIntros "[Hlocked Hown_serv]". iNamed "Hown_serv".

  (* error val. *)
  wp_apply wp_allocStruct; [val_ty|]. iIntros (?) "Hptr_errReply".
  iDestruct (struct_fields_split with "Hptr_errReply") as "H".
  iNamed "H". iClear "putEpoch prevLink dig linkSig putSig".
  wp_storeField.
  set (errReply := servPutReply.mk 0 [] [] [] [] true).
  iAssert (servPutReply.own _ errReply) with "[$error //]" as "Hown_errReply".
  iAssert (is_servPutReply obj_serv.(server.pk) id val errReply) with "[//]" as "#His_errReply".

  (* check id len. *)
  wp_apply wp_slice_len. wp_if_destruct.
  { wp_loadField. wp_apply (wp_Mutex__Unlock with "[-HΦ Hown_errReply]").
    { iFrame "HmuR Hlocked ∗#%". }
    wp_pures. iApply "HΦ". by iFrame. }

  (* check if id was already updated. if not, update. *)
  wp_apply (wp_StringFromBytes with "[$Hid]"). iIntros "Hid". wp_loadField.
  wp_apply (wp_MapGet with "[$Hown_updates]").
  iIntros (? ok) "[%Hmap_get Hown_updates]". destruct ok.
  { wp_loadField. wp_apply (wp_Mutex__Unlock with "[-HΦ Hown_errReply]").
    { iFrame "HmuR Hlocked ∗#%". }
    wp_pures. iApply "HΦ". by iFrame. }
  wp_loadField.
  wp_apply (wp_MapInsert_to_val with "[$Hown_updates]"). iIntros "Hown_updates".

  (* prepare put promise. *)
  iNamed "Hown_chain". do 2 wp_loadField. wp_apply wp_slice_len.
  wp_apply wp_allocStruct; [val_ty|].
  iIntros (?) "Hptr_sepPut".
  iMod (own_slice_small_persist with "Hval") as "#Hval".
  iDestruct (own_slice_small_sz with "Hid") as %Hlen_sz_id.
  wp_apply (servSepPut.wp_encode (servSepPut.mk _ _ _) with "[Hptr_sepPut Hid]").
  { iDestruct (struct_fields_split with "Hptr_sepPut") as "H". iNamed "H".
    rewrite /servSepPut.own /=. iFrame "epoch id val ∗#". }
  iIntros (??). iNamedSuffix 1 "_sepPut".
  replace (word.add (word.sub sl_epochs.(Slice.sz) (W64 1)) (W64 1)) with
    (sl_epochs.(Slice.sz)) in * by ring.
  wp_loadField.
  (* load chain lengths. *)
  iNamed "His_epochChain".
  iDestruct (big_sepL2_length with "His_all_epochs") as %Hlen_γmaps_chain.
  iDestruct (own_slice_small_sz with "Hsl_epochs") as %Hlen_sl_epochs.
  iDestruct (big_sepL2_length with "Hown_all_epochs") as %Hlen_ptrs_chain.

  (* get resources for put sigpred. *)
  (* 1. mono_list_idx_own γupdates. *)
  iDestruct (mono_list_idx_own_get (uint.nat sl_epochs.(Slice.sz)) γupdates with
    "[Hγmaps]") as "#Hidx_γupdates".
  2: iApply (mono_list_lb_own_get with "Hγmaps").
  { apply lookup_snoc_Some. eauto with lia. }
  (* open global_inv. *)
  wp_apply ncfupd_wp.
  iInv "Hinv" as "> H" "Hclose".
  iDestruct "H" as (? key_maps) "H". iNamedSuffix "H" "_inv".
  (* 2.1. get ghost_map_auth updates in full. *)
  iDestruct (mono_list_auth_own_agree with "Hγmaps Hγmaps_inv") as %[_ <-].
  iDestruct (big_sepL2_length with "Hmaps_inv") as %Hlen0.
  rewrite length_app in Hlen0.
  list_simplifier.
  opose proof (list_snoc_exists key_maps _) as (old_maps & updates_inv & ->); [lia|].
  iDestruct (big_sepL2_snoc with "Hmaps_inv") as "[Hmaps_inv Hview_updates_inv]".
  iDestruct (ghost_map_auth_agree with "Hview_updates Hview_updates_inv") as %<-.
  iCombine "Hview_updates Hview_updates_inv" as "Hview_updates".
  (* 2.2. add new entry to ghost_map. *)
  apply map_get_false in Hmap_get as [Hmap_get _].
  rewrite -(lookup_kmap string_to_bytes) in Hmap_get.
  iDestruct (big_sepM2_lookup_l_none with "Hsl_updates") as "%Hmap_get1"; [done|].
  iMod (ghost_map_insert_persist _ val with "Hview_updates") as
    "[[Hview_updates Hview_updates_inv] #Hwitness]"; [done|].
  (* rewrite after ghost map insert so it has expanded form.
    this helps when we later want to do a big sep insert with the expanded form.
    TODO: this all arises bc we can't rewrite under a big sep map insert. *)
  rewrite bytes_to_string_to_bytes in Hmap_get, Hmap_get1.
  iDestruct (big_sepL2_snoc with "[$Hmaps_inv $Hview_updates_inv]") as "Hmaps_inv".
  iMod ("Hclose" with "[$Hγmaps_inv $Hmaps_inv]") as "_".

  (* sign put promise. *)
  iIntros "!>".
  wp_apply (wp_Sign with "[$Hown_sk $Hsl_enc_sepPut]").
  { iFrame "Hinv". iRight.
    iEval (rewrite (bytes_to_string_to_bytes id)) in "Hwitness". iFrame "%#". }
  iIntros (??). iNamedSuffix 1 "_putSig".

  (* extract link resources from chain and return. *)
  do 2 wp_loadField.
  evar (x : w64). wp_bind (SliceGet _ _ #?x).
  opose proof (proj2 (lookup_lt_is_Some ptr_epochs (uint.nat x)) _) as [? Hlook0];
    subst x; [word|].
  wp_apply (wp_SliceGet with "[$Hsl_epochs //]"). iIntros "Hsl_epochs".
  iDestruct (big_sepL2_lookup_1_some with "Hown_all_epochs") as %[chain_epoch Hidx_chain]; [done|].
  iDestruct (big_sepL2_lookup_acc with "Hown_all_epochs") as "[Hown_epoch Hsep_epochs]"; [done..|].
  iNamed "Hown_epoch".
  iMod (own_slice_small_persist with "Hsl_prevLink") as "#Hsl_prevLink".
  iMod (own_slice_small_persist with "Hsl_dig") as "#Hsl_dig".
  iMod (own_slice_small_persist with "Hsl_linkSig") as "#Hsl_linkSig".
  do 3 wp_loadField.
  iDestruct ("Hsep_epochs" with "[$Hptr_map $Hptr_prevLink $Hptr_dig $Hptr_link
    $Hptr_linkSig $Hsl_link $Hown_map]") as "Hsep_epochs"; [iFrame "#"|].
  (* update server store of updated slices. *)
  (* write id in expanded form so that we can move it inside the kmap. *)
  iDestruct (big_sepM2_insert_2 _ _ _ (string_to_bytes (bytes_to_string id))
    with "[] Hsl_updates") as "{Hsl_updates} Hsl_updates".
  { iFrame "Hval". rewrite Heqb in Hlen_sz_id. iPureIntro.
    rewrite bytes_to_string_to_bytes. word. }
  iEval (rewrite -kmap_insert) in "Hsl_updates". wp_loadField.
  (* release lock. *)
  wp_apply (wp_Mutex__Unlock with "[-HΦ Hobj_sepPut Hmsg_putSig Hsl_sig_putSig]").
  { (* TODO: some props above would be cleaner if we could rewrite under the insert here. *)
    iFrame "Hlocked HmuR ∗#%". }
  wp_apply wp_allocStruct; [val_ty|]. iIntros (?) "Hown_putReply".
  iDestruct (struct_fields_split with "Hown_putReply") as "H"; iNamed "H".
  replace (word.add (word.sub sl_epochs.(Slice.sz) (W64 1)) (W64 1)) with
    (sl_epochs.(Slice.sz)) in * by ring.
  iApply "HΦ". instantiate (1:=servPutReply.mk _ _ _ _ _ _).
  rewrite /servPutReply.own /=.
  (* get link validity props from epochChain. *)
  iDestruct (big_sepL2_lookup_2_some with "His_all_epochs") as %[γmap Hidx_γmap]; [done|].
  iDestruct (big_sepL2_lookup with "His_all_epochs") as "H"; [done..|].
  iNamedSuffix "H" "_all". iEval (rewrite w64_to_nat_id) in "Hln_all".
  rewrite /servSepPut.encodes in Henc_sepPut. subst. iFrame "∗#".
Qed.

Lemma wp_applyUpdates ptr_currMap currMap (updates : gmap _ (list w8)) ptr_updates sl_updates d0 :
  {{{
    "Hown_currMap" ∷ own_merkle ptr_currMap currMap ∗
    "#Hsl_updates" ∷ ([∗ map] id ↦ sl_v; v ∈ (kmap string_to_bytes sl_updates); updates,
      "#Hsl_v" ∷ own_slice_small sl_v byteT DfracDiscarded v ∗
      "%Hlen_id" ∷ ⌜ length id = hash_len ⌝) ∗
    "Hown_updates" ∷ own_map ptr_updates d0 sl_updates
  }}}
  applyUpdates #ptr_currMap #ptr_updates
  {{{
    ptr_nextMap, RET #ptr_nextMap;
    "Hown_currMap" ∷ own_merkle ptr_currMap currMap ∗
    "Hown_updates" ∷ own_map ptr_updates d0 sl_updates ∗
    "Hown_nextMap" ∷ own_merkle ptr_nextMap (updates ∪ currMap)
  }}}.
Proof.
  rewrite /applyUpdates.
  iIntros (Φ) "H HΦ". iNamed "H".
  wp_apply (wp_Tree_DeepCopy with "Hown_currMap").
  iIntros (ptr_nextMap). iNamed 1.
  iRename "Htree" into "Hown_currMap". iRename "HnewTree" into "Hown_nextMap".
  set (loopInv := λ (_ sl_mdone : gmap string Slice.t),
    (∃ mdone,
    let sl_mdone' := (kmap string_to_bytes sl_mdone) : gmap (list w8) Slice.t in
    (* these first two properties 'characterize' the following:
    [Definition map_filter_keyset m S :
      filter (λ '(k,_), k ∈ S) m.]
    using the characterization instead of the implementation makes it easier
    to work with. no rewriting under filter preds. *)
    "%Hdom" ∷ ⌜ dom mdone = dom sl_mdone' ⌝ ∗
    "%Hsubset" ∷ ⌜ mdone ⊆ updates ⌝ ∗
    "Hown_nextMap" ∷ own_merkle ptr_nextMap (mdone ∪ currMap))%I).
  wp_apply (wp_MapIter_3 _ _ _ _ _ loopInv with "[$Hown_updates] [Hown_nextMap]");
    subst loopInv.
  { iExists ∅. rewrite map_empty_union. iFrame. iPureIntro; split.
    - rewrite kmap_empty. set_solver.
    - apply map_empty_subseteq. }
  { iIntros (idS sl_v sl_mtodo sl_mdone Φ0) "!> [H1 %H2] HΦ0".
      iNamed "H1". destruct H2 as (Hunion & Hdom1 & Hlook0).
    wp_apply wp_StringToBytes. iIntros (sl_idS) "H".
    iDestruct (own_slice_to_small with "H") as "Hsl_idS".
    apply (lookup_union_Some_l _ sl_mdone) in Hlook0. rewrite -Hunion in Hlook0.
    rewrite -(lookup_kmap string_to_bytes) in Hlook0.
    iDestruct (big_sepM2_lookup_l with "Hsl_updates") as (v) "[%Hlook1 H]";
      [done|]. iNamed "H".
    wp_apply (wp_Tree_Put with "[$Hown_nextMap $Hsl_idS $Hsl_v]").
    iIntros "*". iNamed 1.
    pose proof (Hvalid_id Hlen_id) as ->. iNamed "Herr".
    wp_apply wp_Assert_true. iApply "HΦ0".
    iExists (<[string_to_bytes idS:=v]>mdone).
    rewrite -insert_union_l. iFrame. iPureIntro. split.
    - rewrite kmap_insert. set_solver.
    - by apply insert_subseteq_l. }
  iIntros "[Hown_updates H]". iNamed "H". wp_pures. iApply "HΦ".
  iDestruct (big_sepM2_dom with "Hsl_updates") as %Hdom1.
  assert (mdone = updates) as ->.
  { apply subseteq_dom_eq; set_solver. }
  by iFrame.
Qed.

Lemma wp_server_updateEpoch ptr_serv obj_serv :
  {{{
    "His_serv" ∷ is_server ptr_serv obj_serv
  }}}
  server__updateEpoch #ptr_serv
  {{{
    RET #(); True
  }}}.
Proof.
  rewrite /server__updateEpoch.
  iIntros (Φ) "H HΦ". iNamed "H". iNamed "His_serv". wp_loadField.
  wp_apply (wp_Mutex__Lock with "[$HmuR]").
  iIntros "[Hlocked Hown_serv]". iNamed "Hown_serv".

  (* index epochChain. *)
  iNamed "Hown_chain".
  do 2 wp_loadField.
  wp_apply wp_slice_len.
  do 2 wp_loadField.
  iDestruct (own_slice_small_sz with "Hsl_epochs") as %Hlen_sl_ptr_epochs.
  iDestruct (big_sepL2_length with "Hown_all_epochs") as %Hlen_ptr_epochs_chain.
  evar (x : w64).
  wp_bind (SliceGet _ _ #?x).
  opose proof (proj2 (lookup_lt_is_Some ptr_epochs (uint.nat x)) _) as [ptr_epoch Hidx_ptr_epoch];
    subst x; [word|].
  wp_apply (wp_SliceGet with "[$Hsl_epochs //]"). iIntros "Hsl_epochs".
  iDestruct (big_sepL2_lookup_1_some with "Hown_all_epochs") as
    %[epoch_info Hidx_epoch_info]; [done|].
  iDestruct (big_sepL2_lookup_acc with "Hown_all_epochs") as
    "[Hown_epoch Hown_all_epochs]"; [done..|]. iNamed "Hown_epoch".
  do 2 wp_loadField.
  wp_apply (wp_applyUpdates with "[$Hown_map $Hown_updates $Hsl_updates]").
  iIntros (ptr_nextMap). iNamed 1. do 2 wp_loadField.
  iDestruct ("Hown_all_epochs" with
    "[$Hsl_prevLink $Hsl_dig $Hsl_link $Hsl_linkSig $Hptr_map $Hptr_prevLink $Hptr_dig
    $Hptr_link $Hptr_linkSig $Hown_currMap]") as "Hown_epochs".

  (* ghost_map_auth needs to match nextMap. *)
  wp_apply ncfupd_wp.
  iInv "Hinv" as "> H" "Hclose". iNamedSuffix "H" "_inv".
  iDestruct (mono_list_auth_own_agree with "Hγmaps Hγmaps_inv") as %[_ <-].
  iDestruct (big_sepL2_length with "Hmaps_inv") as %Hlen0.
  rewrite length_app in Hlen0. list_simplifier.
  opose proof (list_snoc_exists key_maps _) as (old_maps & updates0 & ->); [lia|].
  (* we could do this with insert / delete, but snoc makes it easier to
  unify the ghost state when closing the inv.
  just pop the last off and push it back on. *)
  iDestruct (big_sepL2_snoc with "Hmaps_inv") as "[Hmaps_inv Hview_updates_inv]".
  iDestruct (ghost_map_auth_agree with "Hview_updates Hview_updates_inv") as %<-.
  iCombine "Hview_updates Hview_updates_inv" as "Hview_updates".
  iMod (ghost_map_apply_on epoch_info.(epochInfo.keyMap) with "Hview_updates") as
    "[[Hview_updates Hview_updates_inv] _]".
  iDestruct (big_sepL2_snoc with "[$Hmaps_inv $Hview_updates_inv]") as "Hmaps_inv".
  (* also, make a new ghost_map since we're opening up a new epoch. *)
  iMod ghost_map_alloc_empty as (γempty) "[Hauth_empty Hauth_empty_inv]".
  iDestruct (big_sepL2_snoc with "[$Hmaps_inv $Hauth_empty_inv]") as "Hmaps_inv".
  iCombine "Hγmaps Hγmaps_inv" as "Hγmaps".
  iMod (mono_list_auth_own_update_app [∅] with "Hγmaps") as "[[Hγmaps Hγmaps_inv] #Hmono_lb]".
  iMod ("Hclose" with "[$Hγmaps_inv $Hmaps_inv]") as "_".
  iIntros "!>".

  (* epochChain.put. *)
  iMod (ghost_map_auth_persist with "Hview_updates") as "#Hview_nextMap".
  wp_apply (wp_epochChain_put with "[$Hown_epochs $Hown_nextMap $Hown_sk
    $Hsl_epochs $Hptr_epochs]"); [iFrame "#"|].
  iClear "His_epochChain". iIntros (?). iNamed 1.
  wp_apply wp_NewMap. iIntros (?) "Hown_new_updates".
  wp_storeField. wp_loadField. wp_apply (wp_Mutex__Unlock with "[-HΦ]").
  { iFrame "HmuR Hlocked ∗#%". iSplit.
    - iPureIntro. rewrite length_app. lia.
    - eauto. }
  wp_pures. by iApply "HΦ".
Qed.

End proofs.
