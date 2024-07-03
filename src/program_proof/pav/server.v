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
    trees: list loc;
    nextTr: loc;
    chain: list (list w8);
    linkSigs: list (list w8);
    changed: gmap string bool;
    γ: gname;
    hon: bool;
  }.

Section local_defs.
Context `{!heapGS Σ, !mono_listG (list w8) Σ}.

Definition own ptr obj : iProp Σ :=
  ∃ sk sl_trees sl_chain sl_linkSigs ptr_changed,
  "Hsk" ∷ ptr ↦[server :: "sk"] (slice_val sk) ∗
  "Hown_sk" ∷ own_sk sk (serv_sigpred obj.(γ)) obj.(hon) ∗
  "Htrees" ∷ ptr ↦[server :: "trees"] (slice_val sl_trees) ∗
  "Hsl_trees" ∷ own_slice_small sl_trees ptrT (DfracOwn 1) obj.(trees) ∗
  "HnextTr" ∷ ptr ↦[server :: "nextTr"] #obj.(nextTr) ∗
  "Hchain" ∷ ptr ↦[server :: "chain"] (slice_val sl_chain) ∗
  "Hown_chain" ∷ own_Slice2D sl_chain (DfracOwn 1) obj.(chain) ∗
  "HlinkSigs" ∷ ptr ↦[server :: "linkSigs"] (slice_val sl_linkSigs) ∗
  "Hown_linkSigs" ∷ own_Slice2D sl_linkSigs (DfracOwn 1) obj.(linkSigs) ∗
  "Hown_changed" ∷ own_map ptr_changed (DfracOwn 1) obj.(changed) ∗
  "Hchanged" ∷ ptr ↦[server :: "changed"] #ptr_changed.

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
Context `{!heapGS Σ, !mono_listG (list w8) Σ}.

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
Proof.
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
