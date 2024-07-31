From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.pav Require Import ktmerkle.

From Perennial.program_proof.pav Require Import common cryptoffi merkle evidence invs rpc.
From Perennial.program_proof Require Import std_proof.
From iris.unstable.base_logic Require Import mono_list.
From stdpp Require Import gmap.
From Perennial.base_logic Require Import ghost_map.

Module epochInfo.

Record t :=
  mk {
    tree: gmap (list w8) (list w8);
    prevLink: list w8;
    dig: list w8;
    link: list w8;
    linkSig: list w8;
  }.

Section defs.
Context `{!heapGS Σ, !pavG Σ}.

Definition own ptr obj : iProp Σ :=
  ∃ ptr_tr sl_prevLink sl_dig sl_link sl_linkSig d0 d1 d2 d3,
  "Htr" ∷ own_Tree ptr_tr obj.(tree) ∗
  "Hsl_prevLink" ∷ own_slice_small sl_prevLink byteT d0 obj.(prevLink) ∗
  "Hsl_dig" ∷ own_slice_small sl_dig byteT d1 obj.(dig) ∗
  "Hsl_link" ∷ own_slice_small sl_link byteT d2 obj.(link) ∗
  "Hsl_linkSig" ∷ own_slice_small sl_linkSig byteT d3 obj.(linkSig) ∗

  "Hptr_tr" ∷ ptr ↦[epochInfo :: "tree"] #ptr_tr ∗
  "Hptr_prevLink" ∷ ptr ↦[epochInfo :: "prevLink"] (slice_val sl_prevLink) ∗
  "Hptr_dig" ∷ ptr ↦[epochInfo :: "dig"] (slice_val sl_dig) ∗
  "Hptr_link" ∷ ptr ↦[epochInfo :: "link"] (slice_val sl_link) ∗
  "Hptr_linkSig" ∷ ptr ↦[epochInfo :: "linkSig"] (slice_val sl_linkSig).

Definition valid pk epoch γtree obj : iProp Σ :=
  "#Hghost_view" ∷ ghost_map_auth_pers γtree obj.(tree) ∗
  "#Htree_dig" ∷ is_tree_dig obj.(tree) obj.(dig) ∗
  "#Hbind" ∷ is_hash (chainSepSome.encodesF (chainSepSome.mk epoch obj.(prevLink) obj.(dig))) obj.(link) ∗
  "#Hvalid_sig" ∷ is_sig pk (servSepLink.encodesF (servSepLink.mk obj.(link))) obj.(linkSig).

End defs.
End epochInfo.

Module epochChain.

Record t :=
  mk {
    epochs: list epochInfo.t;
  }.

Section defs.
Context `{!heapGS Σ, !pavG Σ}.

Definition own ptr obj : iProp Σ :=
  ∃ sl_epochs ptr_epochs,
  "Hsl_epochs" ∷ own_slice_small sl_epochs ptrT (DfracOwn 1) ptr_epochs ∗
  "Hptr_epochs" ∷ ptr ↦[epochChain :: "epochs"] (slice_val sl_epochs) ∗
  "Hsep_epochs" ∷ ([∗ list] ptr_epoch; epoch ∈ ptr_epochs; obj.(epochs),
    epochInfo.own ptr_epoch epoch).

Definition valid pk γtrees obj : iProp Σ :=
  "#Hvalid_sep_chain" ∷ ([∗ list] k ↦ γtree; info ∈ γtrees; obj.(epochs),
    epochInfo.valid pk k γtree info) ∗
  "#Hbinds_chain" ∷ binds (epochInfo.dig <$> obj.(epochs)) (epochInfo.link <$> obj.(epochs)).

Definition wp_put ptr_chain chain ptr_tree tree sl_sk pk γ γtrees γtree :
  {{{
    "Hown_chain" ∷ own ptr_chain chain ∗
    "#Hvalid_chain" ∷ valid pk γtrees chain ∗
    "Hown_tree" ∷ own_Tree ptr_tree tree ∗
    "Hown_sk" ∷ own_sk sl_sk pk (serv_sigpred γ) ∗
    "#Hpers_updates" ∷ ghost_map_auth_pers γtree tree
  }}}
  epochChain__put #ptr_chain #ptr_tree (slice_val sl_sk)
  {{{
    new_info, RET #();
    let new_chain := mk (chain.(epochs) ++ [new_info]) in
    "%Htr_witness" ∷ ⌜ new_info.(epochInfo.tree) = tree ⌝ ∗
    "Hown_chain" ∷ own ptr_chain new_chain ∗
    "#Hvalid_chain" ∷ valid pk (γtrees ++ [γtree]) new_chain ∗
    "Hown_sk" ∷ own_sk sl_sk pk (serv_sigpred γ)
  }}}.
Proof. Admitted.

End defs.
End epochChain.

Module server.

Record t :=
  mk {
    mu: loc;
    γ: gname;
    sl_sk: Slice.t;
    pk: list w8;
  }.

Section defs.
Context `{!heapGS Σ, !pavG Σ}.

Definition own ptr obj : iProp Σ :=
  ∃ ptr_updates (updates : gmap (list w8) (list w8)) sl_updates ptr_chain γtrees γupdates chain,
  (* ghost state, the other half owned by global_inv. *)
  "HmonoTrees" ∷ mono_list_auth_own obj.(γ) (1/2) (γtrees ++ [γupdates]) ∗
  (* need ghost_map_auth for next tr bc we're continuously updating it.
  for older trees, epoch chain has ghost_map_auth_pers. *)
  "Hupdates_view" ∷ ghost_map_auth γupdates (1/2) updates ∗

  "Hown_sk" ∷ own_sk obj.(sl_sk) obj.(pk) (serv_sigpred obj.(γ)) ∗

  "Hown_chain" ∷ epochChain.own ptr_chain chain ∗
  "%Hlen_nz_chain" ∷ ⌜ length chain.(epochChain.epochs) > 0 ⌝ ∗
  "#Hvalid_chain" ∷ epochChain.valid obj.(pk) γtrees chain ∗
  "Hptr_chain" ∷ ptr ↦[server :: "chain"] #ptr_chain ∗

  (* exists (idS, sl_v) map that owns the respective (id, v) map. *)
  "#Hsl_updates" ∷ ([∗ map] id ↦ sl_v; v ∈ (kmap string_to_bytes sl_updates); updates,
    "Hsl_v" ∷ own_slice_small sl_v byteT DfracDiscarded v ∗
    "%Hlen_id" ∷ ⌜ length id = hash_len ⌝ ) ∗
  "Hown_updates" ∷ own_map ptr_updates (DfracOwn 1) sl_updates ∗
  "Hupdates" ∷ ptr ↦[server :: "updates"] #ptr_updates.

Definition valid ptr obj : iProp Σ :=
  "#Hptr_mu" ∷ ptr ↦[server :: "mu"]□ #obj.(mu) ∗
  "#HmuR" ∷ is_lock nroot #obj.(mu) (own ptr obj) ∗
  "#Hinv" ∷ inv nroot (global_inv obj.(γ)) ∗
  "#ptr_Hsk" ∷ ptr ↦[server :: "sk"]□ (slice_val obj.(sl_sk)).
End defs.
End server.

Section misc.
Context `{!heapGS Σ, !pavG Σ}.
Definition servPutReply_valid pk id val (obj : servPutReply.t) : iProp Σ :=
  (if negb obj.(servPutReply.error) then
    ∃ link,
    "#Hlink" ∷ is_hash
      (chainSepSome.encodesF (chainSepSome.mk
        (word.sub obj.(servPutReply.putEpoch) (W64 1))
        obj.(servPutReply.prevLink)
        obj.(servPutReply.dig)))
      link ∗
    "#Hvalid_linkSig" ∷ is_sig pk
      (servSepLink.encodesF (servSepLink.mk link))
      obj.(servPutReply.linkSig) ∗
    "#Hvalid_putSig" ∷ is_sig pk
      (servSepPut.encodesF (servSepPut.mk obj.(servPutReply.putEpoch) id val))
      obj.(servPutReply.putSig)
  else True)%I.
End misc.

Section proofs.
Context `{!heapGS Σ, !pavG Σ}.

Lemma sep_auth_agree γtrees trees0 trees1 :
  ([∗ list] γtr;tr ∈ γtrees;trees0, ghost_map_auth γtr (1/2) tr) -∗
  ([∗ list] γtr;tr ∈ γtrees;trees1, ghost_map_auth γtr (1/2) tr) -∗
  ⌜trees0 = trees1⌝.
Proof.
  iIntros "Hsep0 Hsep1".
  unfold_leibniz; setoid_rewrite list_equiv_lookup; fold_leibniz.
  iDestruct (big_sepL2_length with "Hsep0") as %Hlen0.
  iDestruct (big_sepL2_length with "Hsep1") as %Hlen1.
  iIntros (i).
  destruct (decide (i < length γtrees)) as [Hbound | Hbound].
  {
    apply lookup_lt_is_Some in Hbound as [x0 Hlook0].
    iDestruct (big_sepL2_lookup_1_some with "Hsep0") as %[x1 Hlook1]; [done|].
    iDestruct (big_sepL2_lookup_1_some with "Hsep1") as %[x2 Hlook2]; [done|].
    iDestruct (big_sepL2_lookup with "Hsep0") as "Hauth0"; [done..|].
    iDestruct (big_sepL2_lookup with "Hsep1") as "Hauth1"; [done..|].
    iDestruct (ghost_map_auth_agree with "Hauth0 Hauth1") as %->.
    rewrite Hlook1 Hlook2.
    done.
  }
  {
    assert (trees0 !! i = None) as ->.
    { apply lookup_ge_None; lia. }
    assert (trees1 !! i = None) as ->.
    { apply lookup_ge_None; lia. }
    done.
  }
Qed.

(*
Lemma wp_server_put ptr_serv obj_serv sl_id sl_val (id val : list w8) d0 d1 :
  {{{
    "Hserv" ∷ server.valid ptr_serv obj_serv ∗
    "Hid" ∷ own_slice_small sl_id byteT d0 id ∗
    "Hval" ∷ own_slice_small sl_val byteT d1 val
  }}}
  server__put #ptr_serv (slice_val sl_id) (slice_val sl_val)
  {{{
    ptr_reply reply, RET #ptr_reply;
    "Hown_reply" ∷ servPutReply.own ptr_reply reply ∗
    "#Hvalid_reply" ∷ servPutReply_valid obj_serv.(server.pk) id val reply
  }}}.
Proof.
  rewrite /server__put.
  iIntros (Φ) "H HΦ"; iNamed "H"; iNamed "Hserv".

  wp_loadField.
  wp_apply (acquire_spec with "[$HmuR]"); iIntros "[Hlocked Hown_serv]"; iNamed "Hown_serv".

  (* error val. *)
  wp_apply wp_allocStruct; [val_ty|];
    iIntros (ptr_errReply) "Hptr_errReply".
  iDestruct (struct_fields_split with "Hptr_errReply") as "H";
    iNamed "H"; iClear "putEpoch prevLink dig linkSig putSig".
  wp_storeField.
  set (errReply := servPutReply.mk 0 [] [] [] [] true).
  iAssert (servPutReply.own ptr_errReply errReply) with "[$error //]" as "Hown_errReply".
  iAssert (servPutReply_valid obj_serv.(server.pk) id val errReply) with "[//]" as "#Hvalid_errReply".

  (* check id len. *)
  wp_apply wp_slice_len.
  wp_if_destruct.
  {
    wp_loadField.
    wp_apply (release_spec with "[-HΦ Hown_errReply]").
    1: iFrame "HmuR Hlocked"; iFrame "∗#%".
    wp_pures; iApply "HΦ"; by iFrame.
  }

  (* check if id was already updated. if not, update. *)
  wp_apply (wp_StringFromBytes with "[$Hid]"); iIntros "Hid".
  wp_loadField.
  wp_apply (wp_MapGet with "[$Hown_updates]");
    iIntros (? ok) "[%Hmap_get Hown_updates]".
  destruct ok.
  {
    wp_loadField.
    wp_apply (release_spec with "[-HΦ Hown_errReply]").
    1: iFrame "HmuR Hlocked"; iFrame "∗#%".
    wp_pures; iApply "HΦ"; by iFrame.
  }
  wp_loadField.
  wp_apply (wp_MapInsert_to_val with "[$Hown_updates]"); iIntros "Hown_updates".

  (* prepare put promise. *)
  wp_loadField.
  iNamed "Hown_chain".
  wp_loadField.
  wp_apply wp_slice_len.
  wp_apply wp_allocStruct; [val_ty|];
    iIntros (ptr_putPre_obj) "Hptr_putPre_obj".
  iMod (own_slice_small_persist with "Hval") as "#Hval".
  wp_apply (servSepPut.wp_encode with "[Hptr_putPre_obj Hid]").
  {
    iDestruct (struct_fields_split with "Hptr_putPre_obj") as "H"; iNamed "H".
    instantiate (1:=servSepPut.mk _ _ _).
    rewrite /servSepPut.own /=.
    iExists sl_id, sl_val; iFrame "∗#".
  }
  iIntros (sl_putPre putPre) "H"; iNamed "H";
    iRename "Hobj" into "Hptr_putPre";
    iRename "Hsl_enc" into "Hsl_putPre";
    move: Henc => Henc_putPre.
  replace (word.add (word.sub sl_epochs.(Slice.sz) (W64 1)) (W64 1)) with (sl_epochs.(Slice.sz)) in * by ring.
  wp_loadField.
  (* load chain lengths. *)
  iNamed "Hvalid_chain".
  iDestruct (big_sepL2_length with "Hvalid_sep_chain") as %Hlen_gammas_chain.
  iDestruct (own_slice_small_sz with "Hsl_epochs") as %Hlen_sl_epochs.
  iDestruct (big_sepL2_length with "Hsep_epochs") as %Hlen_ptr_epochs.

  (* get resources for put sigpred. *)
  (* get γtree mono_list_idx_own. *)
  iDestruct (mono_list_idx_own_get (uint.nat sl_epochs.(Slice.sz)) γupdates with "[HmonoTrees]") as "#Hidx_γupdates".
  2: iApply (mono_list_lb_own_get with "HmonoTrees").
  1: { apply lookup_snoc_Some; eauto with lia. }
  (* open global_inv. *)
  wp_apply ncfupd_wp.
  iRename "HmonoTrees" into "HmonoTrees0".
  iInv "Hinv" as "> H" "Hclose"; iNamed "H".
  (* get ghost_map_auth updates in full, so we can update and make put witness. *)
  iDestruct (mono_list_auth_own_agree with "HmonoTrees HmonoTrees0") as %[_ ->].
  iDestruct (big_sepL2_snoc with "Htree_views") as "[Htree_views Hupdates_view0]".
  iDestruct (ghost_map_auth_agree with "Hupdates_view0 Hupdates_view") as %->.
  iCombine "Hupdates_view Hupdates_view0" as "Hupdates_view".
  apply map_get_false in Hmap_get as [Hmap_get _].
  iDestruct (big_sepM2_lookup_l_none with "Hsl_updates") as "%Hmap_get1"; [done|].
  rewrite lookup_kmap in Hmap_get1.
  iMod (ghost_map_insert_persist _ val with "Hupdates_view") as "[[Hupdates_view0 Hupdates_view1] #Hwitness]"; [done|].
  iDestruct (big_sepL2_snoc with "[$Htree_views $Hupdates_view0]") as "Htree_views".
  iMod ("Hclose" with "[$HmonoTrees0 $Htree_views]") as "_"; [iFrame "#"|].
  iClear "Hdigs Hdigs_links".

  (* sign put promise. *)
  iModIntro.
  wp_apply (wp_Sign with "[$Hown_sk $Hsl_putPre]").
  1: iFrame "Hinv"; iRight; iFrame "%#".
  iIntros (sl_putSig putSig) "H"; iNamed "H";
    iRename "Hmsg" into "Hsl_putPre";
    iRename "Hsig" into "Hvalid_putSig";
    iRename "Hsl_sig" into "Hsl_putSig".

  (* extract resources from chain and return. *)
  wp_loadField.
  wp_loadField.
  pose proof (lookup_lt_is_Some ptr_epochs (uint.nat (word.sub sl_epochs.(Slice.sz) (W64 1)))) as [_ H];
    unshelve (epose proof (H _) as [ptr_epoch Hidx_ptr_epoch]);
    [word|]; clear H.
  wp_apply (wp_SliceGet with "[$Hsl_epochs //]"); iIntros "Hsl_epochs".
  iDestruct (big_sepL2_lookup_1_some with "Hsep_epochs") as %[chain_epoch Hidx_chain]; [done|].
  iDestruct (big_sepL2_lookup_acc with "Hsep_epochs") as "[Hown_epoch Hsep_epochs]"; [done..|].
  iNamed "Hown_epoch".
  iMod (own_slice_small_persist with "Hsl_prevLink") as "#Hsl_prevLink".
  iMod (own_slice_small_persist with "Hsl_dig") as "#Hsl_dig".
  iMod (own_slice_small_persist with "Hsl_linkSig") as "#Hsl_linkSig".
  wp_loadField.
  wp_loadField.
  wp_loadField.
  iDestruct ("Hsep_epochs" with "[$Htr $Hsl_link $Hptr_tr $Hptr_prevLink
    $Hptr_dig $Hptr_link $Hptr_linkSig]") as "Hsep_epochs"; [iFrame "#"|].
  iRename "Hsl_updates" into "H";
    iDestruct (big_sepM2_insert_2 _ _ _ (bytes_to_string id) with "[] H")
    as "Hsl_updates"; [iFrame "Hval"|]; iClear "H".
  iEval (rewrite -kmap_insert) in "Hsl_updates".
  wp_loadField.
  wp_apply (release_spec with "[-HΦ Hptr_putPre Hsl_putPre Hsl_putSig]").
  1: iFrame "Hlocked HmuR"; iFrame "∗#%".
  wp_apply wp_allocStruct; [val_ty|];
    iIntros (ptr_putReply) "Hptr_putReply".
  iDestruct (struct_fields_split with "Hptr_putReply") as "H"; iNamed "H".
  replace (word.add (word.sub sl_epochs.(Slice.sz) (W64 1)) (W64 1)) with (sl_epochs.(Slice.sz)) in * by ring.
  iApply "HΦ".
  iFrame.
  instantiate (1:=servPutReply.mk _ _ _ _ _ _).
  rewrite /servPutReply.own /=.
  iFrame "∗#".
  iDestruct (big_sepL2_lookup_2_some with "Hvalid_sep_chain") as %[γtree Hidx_γtree]; [done|].
  iDestruct (big_sepL2_lookup with "Hvalid_sep_chain") as "H"; [done..|]; iNamed "H".
  iEval (rewrite w64_to_nat_id) in "Hbind".
  rewrite /servSepPut.encodes in Henc_putPre; subst.
  iFrame "#".
Qed.
*)

Lemma wp_applyUpdates ptr_currTr currTr (updates : gmap _ (list w8)) ptr_updates sl_updates d0 :
  {{{
    "Hown_currTr" ∷ own_Tree ptr_currTr currTr ∗
    "#Hsl_updates" ∷ ([∗ map] id ↦ sl_v; v ∈ (kmap string_to_bytes sl_updates); updates,
      "#Hsl_v" ∷ own_slice_small sl_v byteT DfracDiscarded v ∗
      "%Hlen_id" ∷ ⌜ length id = hash_len ⌝) ∗
    "Hown_updates" ∷ own_map ptr_updates d0 sl_updates
  }}}
  applyUpdates #ptr_currTr #ptr_updates
  {{{
    ptr_nextTr, RET #ptr_nextTr;
    "Hown_currTr" ∷ own_Tree ptr_currTr currTr ∗
    "Hown_updates" ∷ own_map ptr_updates d0 sl_updates ∗
    "Hown_nextTr" ∷ own_Tree ptr_nextTr (updates ∪ currTr)
  }}}.
Proof.
  rewrite /applyUpdates.
  iIntros (Φ) "H HΦ"; iNamed "H".
  wp_apply (wp_Tree_DeepCopy with "Hown_currTr");
    iEval (rewrite /named); iIntros (ptr_nextTr) "[Hown_currTr Hown_nextTr]".
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
    "Hown_nextTr" ∷ own_Tree ptr_nextTr (mdone ∪ currTr))%I).
  wp_apply (wp_MapIter_3 _ _ _ _ _ loopInv with "[$Hown_updates] [Hown_nextTr]");
    rewrite /loopInv {loopInv}.
  {
    iExists ∅.
    rewrite map_empty_union; iFrame.
    iPureIntro; split.
    - rewrite kmap_empty. set_solver.
    - apply map_empty_subseteq.
  }
  {
    iIntros (idS sl_v sl_mtodo sl_mdone Φ0) "!> [H1 %H2] HΦ0";
      iNamed "H1"; destruct H2 as (Hunion & Hdom1 & Hlook0).
    wp_apply wp_StringToBytes; iIntros (sl_idS) "H";
      iDestruct (own_slice_to_small with "H") as "Hsl_idS".
    apply (lookup_union_Some_l _ sl_mdone) in Hlook0; rewrite -Hunion in Hlook0.
    rewrite -(lookup_kmap string_to_bytes) in Hlook0.
    iDestruct (big_sepM2_lookup_l with "Hsl_updates") as (v) "[%Hlook1 H]";
      [done|]; iNamed "H".
    wp_apply (wp_Tree_Put with "[$Hown_nextTr $Hsl_idS $Hsl_v]");
      iIntros "*"; iNamed 1.
    pose proof (Hvalid_id Hlen_id) as ->; simpl; iNamed "Herr".
    wp_apply wp_Assert_true.
    iApply "HΦ0".
    iExists (<[string_to_bytes idS:=v]>mdone).
    rewrite -insert_union_l; iFrame.
    iPureIntro; split.
    - rewrite kmap_insert. set_solver.
    - by apply insert_subseteq_l.
  }
  iIntros "[Hown_updates H]"; iNamed "H".
  wp_pures; iApply "HΦ".
  iDestruct (big_sepM2_dom with "Hsl_updates") as %Hdom1.
  assert (mdone = updates) as ->.
  { apply subseteq_dom_eq; set_solver. }
  by iFrame.
Qed.

Lemma wp_server_updateEpoch ptr_serv obj_serv :
  {{{
    "Hvalid_serv" ∷ server.valid ptr_serv obj_serv
  }}}
  server__updateEpoch #ptr_serv
  {{{
    RET #(); True
  }}}.
Proof.
  rewrite /server__updateEpoch.
  iIntros (Φ) "H HΦ"; iNamed "H"; iNamed "Hvalid_serv".
  wp_loadField.
  wp_apply (acquire_spec with "[$HmuR]"); iIntros "[Hlocked Hown_serv]"; iNamed "Hown_serv".

  (* index epochChain. *)
  wp_loadField.
  iNamed "Hown_chain".
  wp_loadField.
  wp_apply wp_slice_len.
  wp_loadField.
  wp_loadField.
  iDestruct (own_slice_small_sz with "Hsl_epochs") as %Hlen_sl_ptr_epochs.
  iDestruct (big_sepL2_length with "Hsep_epochs") as %Hlen_ptr_epochs_chain.
  pose proof (lookup_lt_is_Some ptr_epochs (uint.nat (word.sub sl_epochs.(Slice.sz) (W64 1)))) as [_ H];
    unshelve (epose proof (H _) as [ptr_epoch Hidx_ptr_epoch]);
    [word|]; clear H.
  wp_apply (wp_SliceGet with "[$Hsl_epochs //]"); iIntros "Hsl_epochs".
  iDestruct (big_sepL2_lookup_1_some with "Hsep_epochs") as %[epoch_info Hidx_epoch_info]; [done|].
  iDestruct (big_sepL2_lookup_acc with "Hsep_epochs") as "[Hown_epoch Hsep_epochs]";
    [done..|]; iNamed "Hown_epoch".
  wp_loadField.
  wp_loadField.
  wp_apply (wp_applyUpdates with "[$Htr $Hown_updates $Hsl_updates]");
    iIntros (ptr_nextTr); iNamed 1.
  wp_loadField.
  wp_loadField.
  iDestruct ("Hsep_epochs" with
    "[$Hsl_prevLink $Hsl_dig $Hsl_link $Hsl_linkSig $Hptr_tr $Hptr_prevLink $Hptr_dig
    $Hptr_link $Hptr_linkSig $Hown_currTr]") as "Hown_epochs".

  (* ghost_map_auth needs to match nextTr. *)
  wp_apply ncfupd_wp.
  iRename "HmonoTrees" into "HmonoTrees0".
  iInv "Hinv" as "> H" "Hclose"; iNamed "H".
  iDestruct (mono_list_auth_own_agree with "HmonoTrees HmonoTrees0") as %[_ ->].
  iDestruct (big_sepL2_length with "Htree_views") as %Hlen0.
  rewrite app_length in Hlen0.
  list_simplifier.
  unshelve (epose proof (list_snoc_exists trees _) as (old_trees & updates0 & ->)); [lia|].
  (* we could do this with insert / delete, but snoc makes it easier to
  unify the ghost state when closing the inv.
  just pop the last off and push it back on. *)
  iDestruct (big_sepL2_snoc with "Htree_views") as "[Htree_views Hupdates_view0]".
  iDestruct (ghost_map_auth_agree with "Hupdates_view0 Hupdates_view") as %->.
  iCombine "Hupdates_view Hupdates_view0" as "Hupdates_view".
  iMod (ghost_map_apply_on epoch_info.(epochInfo.tree) with "Hupdates_view") as "[[Hauth_nextTr0 Hauth_nextTr] _]".
  iDestruct (big_sepL2_snoc with "[$Htree_views $Hauth_nextTr0]") as "Htree_views".
  (* also, make a new ghost_map since we're opening up a new epoch. *)
  iMod ghost_map_alloc_empty as (γempty) "[Hauth_empty Hauth_empty0]".
  iDestruct (big_sepL2_snoc with "[$Htree_views $Hauth_empty0]") as "Htree_views".
  iCombine "HmonoTrees HmonoTrees0" as "HmonoTrees".
  iMod (mono_list_auth_own_update_app [∅] with "HmonoTrees") as "[[HmonoTrees0 HmonoTrees] #Hmono_lb]".
  iMod ("Hclose" with "[$HmonoTrees0 $Htree_views]") as "_".
  iIntros "!>".

  (* epochChain.put. *)
  iMod (ghost_map_auth_persist with "Hauth_nextTr") as "#Hpers_nextTr".
  wp_apply (epochChain.wp_put with
    "[$Hown_epochs $Hown_nextTr $Hown_sk $Hsl_epochs $Hptr_epochs]");
    [iFrame "#"|]; iClear "Hvalid_chain"; iIntros (new_info); iNamed 1.
  wp_apply wp_NewMap; iIntros (ptr_new_updates) "Hown_new_updates".
  wp_storeField.
  wp_loadField.
  wp_apply (release_spec with "[-HΦ]").
  {
    iFrame "HmuR Hlocked ∗#%".
    iSplit.
    - iPureIntro. rewrite app_length. lia.
    - eauto.
  }
  wp_pures. by iApply "HΦ".
Qed.

End proofs.
