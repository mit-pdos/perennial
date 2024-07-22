From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.pav Require Import ktmerkle.

From Perennial.program_proof.pav Require Import common cryptoffi merkle evidence.
From Perennial.program_proof Require Import std_proof.
From iris.unstable.base_logic Require Import mono_list.
From stdpp Require Import gmap.
From Perennial.base_logic Require Import ghost_map.

Module server.
Record t :=
  mk {
    mu: loc;
    hon: bool;
    γmonoLinks: gname;
    γmonoTrees: gname;
  }.

Section local_defs.
Context `{!heapGS Σ, !mono_listG (list w8) Σ, !mono_listG gname Σ, !ghost_mapG Σ (list w8) (list w8)}.

Definition own ptr obj : iProp Σ :=
∃ sk sl_ptr_trees ptr_trees trees ptr_updates (updates : gmap (list w8) (list w8)) map_sl_updates ptr_chain digs (links : list (list w8)) sl_linkSigs linkSigs γtrees,
  "Hsk" ∷ ptr ↦[server :: "sk"] (slice_val sk) ∗
  "Hown_sk" ∷ own_sk sk (serv_sigpred obj.(γmonoLinks) obj.(γmonoTrees)) obj.(hon) ∗
  "HlinkSigs" ∷ ptr ↦[server :: "linkSigs"] (slice_val sl_linkSigs) ∗
  "Hown_linkSigs" ∷ own_Slice2D sl_linkSigs (DfracOwn 1) linkSigs ∗

  (* hash chain. *)
  "Hown_chain" ∷ hashChain.own ptr_chain digs links ∗
  "Hchain" ∷ ptr ↦[server :: "chain"] #ptr_chain ∗
  "HmonoLinks" ∷ mono_list_auth_own obj.(γmonoLinks) (1/2) (drop 1 links) ∗

  (* latest updates. *)
  (* Exists map of slices that own the respective vals. *)
  "Hmap_sl_updates" ∷ ([∗ map] sl_bytes; bytes ∈ map_sl_updates; (kmap bytes_to_string updates),
    own_slice_small sl_bytes byteT (DfracOwn 1) bytes) ∗
  "Hown_updates" ∷ own_map ptr_updates (DfracOwn 1) map_sl_updates ∗
  "Hupdates" ∷ ptr ↦[server :: "updates"] #ptr_updates ∗

  (* merkle trees. *)
  "Htrees" ∷ ptr ↦[server :: "trees"] (slice_val sl_ptr_trees) ∗
  "Hsl_ptr_trees" ∷ own_slice_small sl_ptr_trees ptrT (DfracOwn 1) ptr_trees ∗
  "Hown_trees" ∷ ([∗ list] ptr_tr; tr ∈ ptr_trees; trees,
    own_Tree ptr_tr tr) ∗
  "HmonoTrees" ∷ mono_list_auth_own obj.(γmonoTrees) (1/2) γtrees ∗
  (* Need view for latest tr to give put promises.
     For other trees, views let us match up state with global inv. *)
  "Htree_views" ∷ ([∗ list] γtr; tr ∈ γtrees; (trees ++ [updates]),
    ghost_map_auth γtr (1/2) tr) ∗
  (* We could derive this from global_inv, but putting here reduces complexity. *)
  "#Hdigs" ∷ ([∗ list] tr; dig ∈ trees; digs, is_tree_dig tr dig).

Definition valid ptr obj : iProp Σ :=
  "#Hmu" ∷ ptr ↦[server :: "mu"]□ #obj.(mu) ∗
  "#HmuR" ∷ is_lock nroot #obj.(mu) (own ptr obj) ∗
  "#Hinv" ∷ inv nroot (global_inv obj.(γmonoLinks) obj.(γmonoTrees)).

End local_defs.
End server.

Section proofs.
Context `{!heapGS Σ, !mono_listG (list w8) Σ, !mono_listG gname Σ, !ghost_mapG Σ (list w8) (list w8)}.

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

Lemma wp_server_put ptr_serv obj_serv sl_id sl_val (id val : list w8) d0 d1 :
  {{{
    "Hserv" ∷ server.valid ptr_serv obj_serv ∗
    "Hid" ∷ own_slice_small sl_id byteT d0 id ∗
    "Hval" ∷ own_slice_small sl_val byteT d1 val
  }}}
  server__put #ptr_serv (slice_val sl_id) (slice_val sl_val)
  {{{
    ptr_reply reply, RET #ptr_reply;
    "Hreply" ∷ servPutReply.own ptr_reply reply obj_serv.(server.γmonoLinks) obj_serv.(server.γmonoTrees) id val
  }}}.
Proof.
  rewrite /server__put.
  iIntros (Φ) "H HΦ"; iNamed "H"; iNamed "Hserv".

  wp_loadField.
  wp_apply (acquire_spec with "[$HmuR]"); iIntros "[Hlocked Hown_serv]"; iNamed "Hown_serv".

  wp_apply wp_allocStruct; [val_ty|];
    iIntros (ptr_errReply) "Hptr_errReply".
  iDestruct (struct_fields_split with "Hptr_errReply") as "H"; iNamed "H".
  wp_storeField.
  iAssert (servPutReply.own ptr_errReply (servPutReply.mk 0 [] [] [] [] _) obj_serv.(server.γmonoLinks) obj_serv.(server.γmonoTrees) id val) with "[$error //]" as "HerrReply".

  (* check id len. *)
  wp_apply wp_slice_len.
  wp_if_destruct.
  {
    wp_loadField.
    (* TODO: debug why this iFrame takes so long. *)
    wp_apply (release_spec with "[-HΦ HerrReply]"); [iFrame "#∗#"|].
    wp_pures; by iApply "HΦ".
  }

  (* check if id was already updated. if not, update. *)
  wp_apply (wp_StringFromBytes with "[$Hid]"); iIntros "Hid".
  wp_loadField.
  wp_apply (wp_MapGet with "[$Hown_updates]");
    iIntros (? ok) "[%Hmap_get Hown_updates]".
  destruct ok.
  {
    wp_loadField.
    wp_apply (release_spec with "[-HΦ HerrReply]"); [iFrame "#∗#"|].
    wp_pures; by iApply "HΦ".
  }
  wp_loadField.
  wp_apply (wp_MapInsert_to_val with "[$Hown_updates]"); iIntros "Hown_updates".

  (* prepare put promise. *)
  wp_loadField.
  wp_apply wp_slice_len.
  wp_pures.
  wp_apply wp_allocStruct; [val_ty|];
    iIntros (ptr_putPre_obj) "Hptr_putPre_obj".
  wp_apply (servSepPut.wp_encode with "[Hptr_putPre_obj Hid Hval]").
  {
    iDestruct (struct_fields_split with "Hptr_putPre_obj") as "H"; iNamed "H".
    instantiate (1:=servSepPut.mk _ _ _).
    rewrite /servSepPut.own /=.
    iExists sl_id, sl_val; iFrame.
  }
  iIntros (sl_putPre putPre) "H"; iNamed "H";
    iRename "Hobj" into "Hptr_putPre";
    iRename "Hsl_enc" into "Hsl_putPre";
    move: Henc => Henc_putPre.
  replace (word.add (word.sub sl_ptr_trees.(Slice.sz) (W64 1)) (W64 1)) with (sl_ptr_trees.(Slice.sz)) in Henc_putPre by ring.

  (* get resources for put sigpred. *)
  (* get γtree mono_list_idx_own. *)
  iDestruct (own_slice_small_sz with "Hsl_ptr_trees") as %Hlen0.
  iDestruct (big_sepL2_length with "Hown_trees") as %Hlen1.
  iDestruct (big_sepL2_length with "Htree_views") as %Hlen2.
  rewrite app_length/= in Hlen2.
  assert (uint.nat sl_ptr_trees.(Slice.sz) < length γtrees) as Hinb by lia.
  apply lookup_lt_is_Some in Hinb as [γtree Hlook0].
  iDestruct (mono_list_idx_own_get with "[HmonoTrees]") as "#Hidx_γtree".
  2: iApply (mono_list_lb_own_get with "HmonoTrees").
  1: done.
  (* open invariant to get even more info. *)
  wp_apply ncfupd_wp.
  iRename "HmonoTrees" into "HmonoTrees0".
  iRename "Htree_views" into "Htree_views0".
  iInv "Hinv" as "> H" "Hclose".
  iEval (rewrite /global_inv) in "H".
  (* TODO: very weird...
     if we do `iNamed "H".` here with a conflicting hyp name,
     instead of error'ing out, our goal becomes False.
     this seems like bad behavior from iris_named_props. *)
  iRename "Hdigs" into "Hdigs0".
  iNamed "H".
  iDestruct (mono_list_auth_own_agree with "HmonoTrees HmonoTrees0") as %[_ ->].
  iDestruct (sep_auth_agree with "Htree_views Htree_views0") as %?; list_simplifier.
  (* get ghost map witness. *)
  assert ((trees ++ [updates]) !! uint.nat sl_ptr_trees.(Slice.sz) = Some updates) as Hlook1.
  { apply lookup_snoc_Some; eauto with lia. }
  iDestruct (big_sepL2_insert_acc with "Htree_views0") as "[Hmap_auth0 Hsep_close0]"; [done..|].
  iDestruct (big_sepL2_insert_acc with "Htree_views") as "[Hmap_auth1 Hsep_close1]"; [done..|].
  iCombine "Hmap_auth0 Hmap_auth1" as "Hmap_auth".
  apply map_get_false in Hmap_get as [Hmap_get _].
  iDestruct (big_sepM2_lookup_l_none with "Hmap_sl_updates") as "%Hmap_get1"; [done|].
  rewrite lookup_kmap in Hmap_get1.
  iMod (ghost_map_insert_persist _ val with "Hmap_auth") as "[[Hmap_auth0 Hmap_auth1] #Hwitness]"; [done|].
  (* make resources look pretty before closing invariant. *)
  iDestruct ("Hsep_close0" with "Hmap_auth0") as "Htree_views0".
  iDestruct ("Hsep_close1" with "Hmap_auth1") as "Htree_views1".
  pose proof (list_insert_id _ _ _ Hlook0) as H;
    iEval (rewrite H) in "Htree_views0 Htree_views1";
    clear H.
  assert (uint.nat sl_ptr_trees.(Slice.sz) = length trees + 0) as H by lia;
    iEval (rewrite H insert_app_r) in "Htree_views0 Htree_views1";
    list_simplifier; clear H.
  iMod ("Hclose" with "[$Hlinks $HmonoTrees $Htree_views1]") as "_"; [iFrame "%#"|].
  iClear "Hbinds Hdigs".

  (* sign put promise. *)
  iModIntro.
  wp_loadField.
  wp_apply (wp_Sign with "[$Hown_sk $Hsl_putPre]").
  {
    iRight.
    (* TODO: with iFrame "%", it's unfolding mono_list_idx_own,
       framing the lookup, and left with a mono_list_lb_own, which we don't have.
       maybe mono_list_idx_own should be more opaque? *)
    iFrame (Henc_putPre).
    iFrame "#".
  }
  iIntros (sl_putSig putSig) "H";
    iRename "Hsk" into "Hptr_sk";
    iNamed "H";
    iRename "Hmsg" into "Hsl_putPre";
    iRename "Hsig" into "HputSig".

  (* get all the other data to be returned. *)
  wp_loadField.
  wp_apply (hashChain.wp_getLink with "Hown_chain"); [admit|].
  iIntros (sl_prev2Link prev2Link) "H";
    iRename "Hchain" into "Hptr_chain";
    iNamed "H".
  remember (word.sub sl_ptr_trees.(Slice.sz) (W64 1)) as currEpoch.
  remember (word.sub currEpoch (W64 1)) as prevEpoch.
  assert (links !! uint.nat prevEpoch = Some prev2Link) as Hlook2 by admit.
  (* TODO: prove by showing in bounds in (drop 1 links) and extracting
     from mono_list_auth_own. *)
  iAssert ((⌜ uint.nat currEpoch > 0 ⌝ -∗ mono_list_idx_own obj_serv.(server.γmonoLinks) (uint.nat prevEpoch) prev2Link)%I) as "Hmono_prev2Link"; [admit|].

  wp_loadField.
  assert (∃ ptr_tree, ptr_trees !! uint.nat currEpoch = Some ptr_tree) as [ptr_tree Hlook3] by admit.
  wp_apply (wp_SliceGet with "[$Hsl_ptr_trees //]"); iIntros "Hsl_ptr_trees".
  iDestruct (big_sepL2_lookup_1_some with "Hown_trees") as %[tree Htree]; [done|].
  iDestruct (big_sepL2_lookup_acc with "Hown_trees") as "[Hown_tree Hown_trees_close]"; [done..|].
  wp_apply (wp_Tree_Digest with "Hown_tree");
    iIntros (sl_prevDig prevDig) "H"; iNamed "H".
  assert (digs !! uint.nat currEpoch = Some prevDig) as Hlook4 by admit.
  assert (∃ prevLink, links !! uint.nat currEpoch = Some prevLink) as [prevLink Hlook5] by admit.
  iAssert (is_hash (chainSepSome.encodesF (chainSepSome.mk currEpoch prev2Link prevDig)) prevLink) as "Hbind_prevLink"; [admit|].
  iAssert (mono_list_idx_own obj_serv.(server.γmonoLinks) (uint.nat currEpoch) prevLink) as "Hmono_prevLink"; [admit|].

  wp_loadField.
  iDestruct "Hown_linkSigs" as (linkSigs_dim0) "[HlinkSigs_dim0 Hown_linkSigs]".
  assert (∃ sl_linkSig, linkSigs_dim0 !! uint.nat currEpoch = Some sl_linkSig) as [sl_linkSig Hlook6] by admit.
  wp_apply (wp_SliceGet with "[$HlinkSigs_dim0]"); [done|];
    iIntros "HlinkSigs_dim0".

  (* return. *)
  wp_loadField.
  iDestruct ("Hown_trees_close" with "Htree") as "Hown_trees".
  iAssert (own_Slice2D sl_linkSigs (DfracOwn 1) linkSigs) with "[$Hown_linkSigs $HlinkSigs_dim0]" as "Hown_linkSigs".
  wp_apply (release_spec with "[Hlocked Hptr_sk HlinkSigs Hptr_chain HmonoLinks Hmap_sl_updates Hupdates Htrees HmonoTrees0 Hown_updates Htree_views0 Hsk Hchain Hsl_ptr_trees Hown_trees Hown_linkSigs]"); [admit|].
  wp_apply wp_allocStruct; [val_ty|];
    iIntros (ptr_putReply) "Hptr_putReply".
  iClear "putEpoch prev2Link prevDig linkSig putSig HerrReply".
  iDestruct (struct_fields_split with "Hptr_putReply") as "H"; iNamed "H".
  iApply "HΦ".
  instantiate (1:=servPutReply.mk _ _ _ _ _ _).
  rewrite /servPutReply.own /=.
  iExists prevLink, sl_prev2Link, sl_prevDig, sl_linkSig, sl_putSig.
  iFrame "∗#".
  (*
     first get mono_idx for prevLink.
     then just need to unify bindings and exhibit mono_idx.
   *)
Admitted.

Lemma wp_server_updateEpoch ptr_serv obj_serv :
  {{{
    "Hvalid_serv" ∷ server.valid ptr_serv obj_serv
  }}}
  server__updateEpoch #ptr_serv
  {{{
    RET #(); True
  }}}.
Proof. Admitted.

End proofs.
