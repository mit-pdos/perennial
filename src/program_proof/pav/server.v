From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.pav Require Import ktmerkle.

From Perennial.program_proof.pav Require Import common cryptoffi merkle evidence.
From Perennial.program_proof Require Import std_proof.
From iris.unstable.base_logic Require Import mono_list.
From stdpp Require Import gmap.
From Perennial.base_logic Require Import ghost_map.

Module hashChain.
Record t :=
  mk {
    links: list (list w8);
  }.

Section local_defs.
Context `{!heapGS Σ}.
Definition own ptr obj : iProp Σ :=
  ∃ h,
  chainSepNone.hashes_to h ∗
  own_Slice2D ptr (DfracOwn 1) (h :: obj.(links)).
End local_defs.
End hashChain.

Module server.
Record t :=
  mk {
    mu: loc;
    trees: list (gmap (list w8) (list w8));
    updates: gmap (list w8) (list w8);
    chain: hashChain.t;
    linkSigs: list (list w8);
    hon: bool;
    γmonoLinks: gname;
    γmonoTrs: gname;
  }.

Section local_defs.
Context `{!heapGS Σ, !mono_listG (list w8) Σ, !mono_listG gname Σ, !ghost_mapG Σ (list w8) (list w8)}.

Definition my_inv γmonoLinks γmonoTrs : iProp Σ :=
  ∃ links γtrs trs nextTr prevLinks digs,
  "#Hbinds" ∷ ([∗ list] epoch ↦ xy; link ∈ (zip prevLinks digs); links,
    is_hash (chainSepSome.encodesF (chainSepSome.mk epoch xy.1 xy.2)) link) ∗
  "Hlinks" ∷ mono_list_auth_own γmonoLinks (1/2) links ∗
  "Hmaps" ∷ ([∗ list] γtr; tr ∈ γtrs; (trs ++ [nextTr]), ghost_map_auth γtr (1/2) tr) ∗
  "HmonoTrs" ∷ mono_list_auth_own γmonoTrs (1/2) γtrs ∗
  "#Hdigs" ∷ ([∗ list] tr; dig ∈ trs; digs, isTreeDig tr dig).

Definition own ptr obj : iProp Σ :=
  ∃ sk sl_trees sl_treePtrs ptr_updates map_sl_updates sl_chain sl_linkSigs γtrs lastγTr,
  "Hsk" ∷ ptr ↦[server :: "sk"] (slice_val sk) ∗
  "Hown_sk" ∷ own_sk sk (serv_sigpred obj.(γmonoLinks) obj.(γmonoTrs)) obj.(hon) ∗
  "Hchain" ∷ ptr ↦[server :: "chain"] (slice_val sl_chain) ∗
  "Hown_chain" ∷ hashChain.own sl_chain obj.(chain) ∗
  "HmonoLinks" ∷ mono_list_auth_own obj.(γmonoLinks) (1/2) obj.(chain).(hashChain.links) ∗
  "HlinkSigs" ∷ ptr ↦[server :: "linkSigs"] (slice_val sl_linkSigs) ∗
  "Hown_linkSigs" ∷ own_Slice2D sl_linkSigs (DfracOwn 1) obj.(linkSigs) ∗
  (* Exists map from string IDs to slices s.t. the slices own the vals. *)
  "Hmap_sl_updates" ∷ ([∗ map] sl_bytes; bytes ∈ map_sl_updates; (kmap bytes_to_string obj.(updates)),
    own_slice_small sl_bytes byteT (DfracOwn 1) bytes) ∗
  "Hown_updates" ∷ own_map ptr_updates (DfracOwn 1) map_sl_updates ∗
  "Hupdates" ∷ ptr ↦[server :: "updates"] #ptr_updates ∗

  (* Tree-specific stuff. *)
  "Htrees" ∷ ptr ↦[server :: "trees"] (slice_val sl_trees) ∗
  "Hsl_trees" ∷ own_slice_small sl_trees ptrT (DfracOwn 1) sl_treePtrs ∗
  "Hown_trees" ∷ ([∗ list] ptr_tr; tr ∈ sl_treePtrs; obj.(trees),
    own_Tree ptr_tr tr) ∗
  "HmonoTrs" ∷ mono_list_auth_own obj.(γmonoTrs) (1/2) γtrs ∗
  "HlastγTr" ∷ ⌜Some lastγTr = last γtrs⌝ ∗
  "Hview_nextTr" ∷ ghost_map_auth lastγTr (1/2) obj.(updates).

Definition valid ptr obj : iProp Σ :=
  "#Hmu" ∷ ptr ↦[server :: "mu"]□ #obj.(mu) ∗
  "#HmuR" ∷ is_lock nroot #obj.(mu) (own ptr obj).

End local_defs.
End server.

Module servPutReply.
Record t :=
  mk {
    putEpoch: w64;
    prev2Link: list w8;
    prevDig: list w8;
    linkSig: list w8;
    putSig: list w8;
    error: bool;
  }.

Section local_defs.
Context `{!heapGS Σ}.

Definition own ptr obj : iProp Σ :=
  ∃ sl_prev2Link sl_prevDig sl_linkSig sl_putSig d0 d1 d2 d3,
  "HputEpoch" ∷ ptr ↦[servPutReply :: "putEpoch"] #obj.(putEpoch) ∗
  "Hprev2Link" ∷ ptr ↦[servPutReply :: "prev2Link"] (slice_val sl_prev2Link) ∗
  "Hsl_prev2Link" ∷ own_slice_small sl_prev2Link byteT d0 obj.(prev2Link) ∗
  "HprevDig" ∷ ptr ↦[servPutReply :: "prevDig"] (slice_val sl_prevDig) ∗
  "Hsl_prevDig" ∷ own_slice_small sl_prevDig byteT d1 obj.(prevDig) ∗
  "HlinkSig" ∷ ptr ↦[servPutReply :: "linkSig"] (slice_val sl_linkSig) ∗
  "Hsl_linkSig" ∷ own_slice_small sl_linkSig byteT d2 obj.(linkSig) ∗
  "HputSig" ∷ ptr ↦[servPutReply :: "putSig"] (slice_val sl_putSig) ∗
  "Hsl_putSig" ∷ own_slice_small sl_putSig byteT d3 obj.(putSig) ∗
  "Herror" ∷ ptr ↦[servPutReply :: "error"] #obj.(error).

End local_defs.
End servPutReply.

Section proofs.
Context `{!heapGS Σ, !mono_listG (list w8) Σ, !mono_listG gname Σ, !ghost_mapG Σ (list w8) (list w8)}.

Lemma wp_server_put ptr_serv obj_serv sl_id sl_val (id val : list w8) d0 d1 :
  {{{
    "Hvalid_serv" ∷ server.valid ptr_serv obj_serv ∗
    "Hid" ∷ own_slice_small sl_id byteT d0 id ∗
    "Hval" ∷ own_slice_small sl_val byteT d1 val
  }}}
  server__put #ptr_serv (slice_val sl_id) (slice_val sl_val)
  {{{
    ptr_reply reply, RET #ptr_reply;
    "Hreply" ∷ servPutReply.own ptr_reply reply
  }}}.
Proof. Admitted.
(*
  rewrite /server__put.
  iIntros (Φ) "H HΦ"; iNamed "H".
  rewrite /server.valid; iNamed "Hvalid_serv".

  wp_loadField.
  wp_apply (acquire_spec with "[$HmuR]"); iIntros "[Hlocked Hown_serv]".
  iEval (rewrite /server.own) in "Hown_serv"; iNamed "Hown_serv".

  wp_apply wp_allocStruct; [val_ty|];
    iIntros (ptr_errReply) "Hptr_errReply".
  iDestruct (struct_fields_split with "Hptr_errReply") as "H"; iNamed "H".
  wp_storeField.
  iAssert (servPutReply.own ptr_errReply _) with "[putEpoch prev2Link prevDig linkSig putSig error]" as "HerrReply".
  {
    instantiate (1:=servPutReply.mk _ _ _ _ _ _).
    rewrite /servPutReply.own /=.
    iExists Slice.nil, Slice.nil, Slice.nil, Slice.nil.
    iDestruct (own_slice_zero byteT (DfracOwn 1)) as "H0".
    iDestruct (own_slice_to_small with "H0") as "H1".
    iFrame "#∗".
  }

  (* see if id was already changed in this epoch. *)
  wp_apply (wp_StringFromBytes with "[$Hid]"); iIntros "Hid".
  wp_loadField.
  Search impl.MapGet.
  wp_apply (wp_MapGet with "[$Hown_changed]");
    iIntros (? ok) "[%HmapGet Hown_changed]".
  destruct ok.
  {
    wp_loadField.
    wp_apply (release_spec with "[-HΦ HerrReply]"); [iFrame "#∗"|].
    wp_pures; by iApply "HΦ".
  }
  wp_loadField.
Admitted.
*)

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
