From stdpp Require Import gmap.
From Perennial.algebra Require Import auth_map.
From Perennial.goose_lang.lib Require Import lock.
From Perennial.goose_lang.ffi Require Import grove_ffi.
From Perennial.program_proof Require Import proof_prelude.
From Goose.github_com.mit_pdos.lockservice Require Import lockservice.
From Perennial.program_proof.lockservice Require Import rpc_proof nondet.

Record kvservice_names := KVserviceGN {
  ks_rpcGN : rpc_names;
  ks_kvMapGN : gname;
}.

Class kvserviceG Σ := KVserviceG {
  ls_rpcG :> rpcG Σ u64; (* RPC layer ghost state *)
  ls_kvMapG :> mapG Σ u64 u64; (* [γkv]: tracks the state of the KV server *logically* *)
}.

Section kv_proof.
Context `{!heapG Σ, !kvserviceG Σ, !rpcregG Σ}.

Implicit Types (γ : kvservice_names).

Local Notation "k [[ γ ]]↦ '_'" := (∃ v, k [[γ]]↦ v)%I
(at level 20, format "k  [[ γ ]]↦ '_'") : bi_scope.

Definition Get_Pre γ va : RPCValsC -> iProp Σ := (λ args, args.(U64_1) [[γ.(ks_kvMapGN)]]↦ va)%I.
Definition Get_Post γ va : RPCValsC -> u64 -> iProp Σ := λ args v, (⌜v = va⌝ ∗ args.(U64_1) [[γ.(ks_kvMapGN)]]↦ v)%I.

Definition Put_Pre γ : RPCValsC -> iProp Σ := (λ args, args.(U64_1) [[γ.(ks_kvMapGN)]]↦ _)%I.
Definition Put_Post γ : RPCValsC -> u64 -> iProp Σ := (λ args _, args.(U64_1) [[γ.(ks_kvMapGN)]]↦ args.(U64_2))%I.

Definition KVServer_own_core γ (srv:loc) : iProp Σ :=
  ∃ (kvs_ptr:loc) (kvsM:gmap u64 u64),
  "HlocksOwn" ∷ srv ↦[KVServer.S :: "kvs"] #kvs_ptr
∗ "HkvsMap" ∷ is_map (kvs_ptr) kvsM
∗ "Hkvctx" ∷ map_ctx γ.(ks_kvMapGN) 1 kvsM
.

(* FIXME: this is currently just a placeholder *)
Definition own_kvclerk γ ck_ptr (srv : u64) : iProp Σ :=
  ∃ (cl_ptr:loc),
   "Hcl_ptr" ∷ ck_ptr ↦[KVClerk.S :: "client"] #cl_ptr ∗
   "Hprimary" ∷ ck_ptr ↦[KVClerk.S :: "primary"] #srv ∗
   "Hcl" ∷ own_rpcclient cl_ptr γ.(ks_rpcGN).

Definition is_kvserver γ (srv:loc) : iProp Σ :=
  ∃ (sv:loc),
  "#Hsv" ∷ readonly (srv ↦[KVServer.S :: "sv"] #sv) ∗
  "#His_rpc" ∷ is_rpcserver sv γ.(ks_rpcGN) (KVServer_own_core γ srv)
.

Lemma put_core_spec γ (srv:loc) args :
{{{ 
     KVServer_own_core γ srv ∗ Put_Pre γ args
}}}
  KVServer__put_core #srv (into_val.to_val args)
{{{
   RET #0; KVServer_own_core γ srv
      ∗ Put_Post γ args 0
}}}.
Proof.
  iIntros (Φ) "[Hksown Hpre] Hpost".
  wp_lam.
  wp_pures.
  iNamed "Hksown".
  wp_pures.
  wp_loadField.
  wp_apply (wp_MapInsert with "HkvsMap"); eauto; iIntros "HkvsMap".
  iDestruct "Hpre" as (v') "Hpre".
  iMod (map_update with "Hkvctx Hpre") as "[Hkvctx Hptsto]".
  wp_seq.
  iApply "Hpost".
  iFrame. iExists _, _; iFrame.
Qed.

Lemma get_core_spec (srv:loc) args (va:u64) γ :
{{{ 
     KVServer_own_core γ srv ∗ Get_Pre γ va args
}}}
  KVServer__get_core #srv (into_val.to_val args)%V
{{{
   r, RET #r; KVServer_own_core γ srv ∗
   Get_Post γ va args r
}}}.
Proof.
  iIntros (Φ) "[Hksown Hpre] Hpost".
  wp_lam.
  wp_pures.
  iNamed "Hksown".
  wp_pures.
  wp_loadField.
  wp_apply (wp_MapGet with "HkvsMap").
  iIntros (v ok) "[% HkvsMap]".
  iDestruct (map_valid with "Hkvctx Hpre") as %Hvalid.
  assert (va = v) as ->.
  {
    rewrite /map_get in H.
    rewrite ->bool_decide_true in H; eauto.
    simpl in H.
    injection H as H.
    rewrite /default in H.
    rewrite Hvalid in H.
    done.
  }
  wp_pures.
  iApply "Hpost".
  iFrame.
  iSplit; last done. iExists _, _; iFrame.
Qed.

Lemma KVServer__Get_spec srv γ :
is_kvserver γ srv -∗
{{{
    True
}}}
    KVServer__Get #srv
{{{ (f:goose_lang.val), RET f;
        ∀ args req va, is_rpcHandler f γ.(ks_rpcGN) args req (Get_Pre γ va args) (Get_Post γ va args)
}}}.
Proof.
  iIntros "#Hls".
  iIntros (Φ) "!# _ Hpost".
  wp_lam.
  wp_pures.
  iApply "Hpost".
  iIntros (args req).
  iIntros (????).
  iIntros (_ _).
  iNamed "Hls". wp_pures.
  wp_loadField.
  iApply (RPCServer__HandleRequest_spec with "[] His_rpc"); last by eauto.
  clear Φ. iIntros "!#" (Φ) "Hpre HΦ".
  wp_pures.
  iApply (get_core_spec with "Hpre"); last by eauto.
Qed.

Lemma KVServer__Put_spec srv γ :
is_kvserver γ srv -∗
{{{
    True
}}}
    KVServer__Put #srv
{{{ (f:goose_lang.val), RET f;
    ∀ args req, is_rpcHandler f γ.(ks_rpcGN) args req (Put_Pre γ args) (Put_Post γ args)
}}}.
Proof.
  iIntros "#Hls".
  iIntros (Φ) "!# _ Hpost".
  wp_lam.
  wp_pures.
  iApply "Hpost".
  iIntros (args req).
  iApply is_rpcHandler_eta; simpl.
  iIntros "!#" (_ _).
  iNamed "Hls". wp_pures.
  wp_loadField.
  iApply (RPCServer__HandleRequest_spec with "[] His_rpc"); last by eauto.
  clear Φ. iIntros "!#" (Φ) "Hpre HΦ".
  wp_pures.
  iApply (put_core_spec with "Hpre"); last by eauto.
Qed.
(* TODO: see if any more repetition can be removed *)

Definition is_kvserver_host γ (host:u64) : iProp Σ :=
  ∃ handlers (fget fput : val),
    "#Hhost" ∷ host [[rpcreg_gname]]↦ro handlers ∗
    "%Hhandler_get" ∷ ⌜handlers !! (U64 2) = Some fget⌝ ∗
    "%Hhandler_put" ∷ ⌜handlers !! (U64 1) = Some fput⌝ ∗
    "#Hgetspec" ∷ (∀ args req va,
      is_rpcHandlerHost host (U64 2) γ.(ks_rpcGN) args req (Get_Pre γ va args) (Get_Post γ va args)) ∗
    "#Hputspec" ∷ (∀ args req,
      is_rpcHandlerHost host (U64 1) γ.(ks_rpcGN) args req (Put_Pre γ args) (Put_Post γ args)) ∗
    "#Hisrpcserver" ∷ is_RPCServer γ.(ks_rpcGN).

Lemma KVClerk__Get_spec (kck:loc) (srv:u64) (key va:u64) γ  :
is_kvserver_host γ srv -∗
{{{
     own_kvclerk γ kck srv ∗ (key [[γ.(ks_kvMapGN)]]↦ va)
}}}
  KVClerk__Get #kck #key
{{{
     v, RET #v; ⌜v = va⌝ ∗ own_kvclerk γ kck srv ∗ (key [[γ.(ks_kvMapGN)]]↦ va )
}}}.
Proof.
  iIntros "#Hserver" (Φ) "!# (Hclerk & Hpre) Hpost".
  wp_lam.
  wp_pures. 
  iNamed "Hclerk".
  repeat wp_loadField.
  wp_apply (RPCClient__MakeRequest_spec _ _ _ {|U64_1:=_ ; U64_2:= _ |} γ.(ks_rpcGN) with "[] [Hpre Hcl]"); eauto.
  {
    iIntros (req).
    iNamed "Hserver".
    iApply "Hgetspec".
  }
  {
    iNamed "Hserver". iFrame "∗#".
  }
  iIntros (v) "Hretv".
  iDestruct "Hretv" as "[Hrpcclient HcorePost]".
  iApply "Hpost".
  iDestruct "HcorePost" as (->) "Hkv".
  iSplit; first done.
  iFrame "Hkv".
  iExists _; iFrame.
Qed.

Lemma KVClerk__Put_spec (kck:loc) (srv:u64) (key va:u64) γ :
is_kvserver_host γ srv -∗
{{{
     own_kvclerk γ kck srv ∗ (key [[γ.(ks_kvMapGN)]]↦ _ )
}}}
  KVClerk__Put #kck #key #va
{{{
     RET #();
     own_kvclerk γ kck srv ∗ (key [[γ.(ks_kvMapGN)]]↦ va )
}}}.
Proof.
  iIntros "#Hserver" (Φ) "!# (Hclerk & Hpre) Hpost".
  wp_lam.
  wp_pures. 
  iNamed "Hclerk".
  repeat wp_loadField.
  wp_apply (RPCClient__MakeRequest_spec _ _ _ {| U64_1:= _; U64_2:=_ |} γ.(ks_rpcGN) with "[] [Hpre Hcl]"); eauto.
  {
    iIntros (req).
    iNamed "Hserver". iApply "Hputspec".
  }
  {
    iNamed "Hserver". iFrame "∗#".
  }
  iIntros (v) "Hretv".
  iDestruct "Hretv" as "[Hrpcclient HcorePost]".
  wp_seq.
  iApply "Hpost".
  iFrame.
  iExists _; iFrame.
Qed.

Definition kvserver_cid_token γ cid :=
  RPCClient_own γ.(ks_rpcGN) cid 1.

Lemma MakeKVServer_spec :
  {{{ True }}}
    MakeKVServer #()
  {{{ γ srv, RET #srv;
    is_kvserver γ srv ∗ [∗ set] cid ∈ fin_to_set u64, kvserver_cid_token γ cid
  }}}.
Proof.
  iIntros (Φ) "_ HΦ". wp_lam.
  iMod make_rpc_server as (γrpc) "(#is_server & server_own & cli_tokens)"; first done.
  iMod (map_init (∅ : gmap u64 u64)) as (γkv) "Hγkv".
  set (γ := KVserviceGN γrpc γkv) in *.
  iApply wp_fupd.

  wp_apply wp_allocStruct; first by eauto.
  iIntros (l) "Hl". wp_pures.
  iDestruct (struct_fields_split with "Hl") as "(l_sv & l_locks & _)".
  wp_apply (wp_NewMap u64 (t:=uint64T)). iIntros (kvs) "Hkvs".
  wp_storeField.
  wp_apply (MakeRPCServer_spec (KVServer_own_core γ l) with "[$server_own $is_server l_locks Hγkv Hkvs]").
  { iExists _, _. iFrame. }
  iIntros (sv) "#Hsv".
  wp_storeField.
  iApply ("HΦ" $! γ).
  iFrame "cli_tokens".
  iExists sv. iFrame "#".
  by iMod (readonly_alloc_1 with "l_sv") as "$".
Qed.
(* TODO: return all of the ptsto's here; update KVServer_own_core so it has map_ctx bigger than the physical map *)

Opaque zero_val.
Lemma KVServer_AllocServer_spec γ srv :
  {{{ is_kvserver γ srv }}}
    KVServer__AllocServer #srv
  {{{ (host:u64), RET #host;
    is_kvserver_host γ host
  }}}.
Proof.
  iIntros (Φ) "#Hsrv HΦ".
  wp_lam.
  wp_apply map.wp_NewMap.
  iIntros (mref) "Hm".
  wp_pures.
  wp_apply KVServer__Put_spec; first eauto.
  iIntros (fput) "#Hfput".
  wp_apply (map.wp_MapInsert with "Hm").
  iIntros "Hm".
  wp_pures.
  wp_apply KVServer__Get_spec; first eauto.
  iIntros (fget) "#Hfget".
  wp_apply (map.wp_MapInsert with "Hm").
  iIntros "Hm".
  wp_apply (wp_AllocServer with "Hm").
  iIntros (host) "#Hhost".
  wp_pures.
  iApply "HΦ".

  iExists _, _, _.
  iFrame "Hhost".
  iSplitR.
  { rewrite lookup_insert. eauto. }
  iSplitR.
  { rewrite lookup_insert_ne; eauto. rewrite lookup_insert. eauto. }
  iSplit.
  {
    iIntros (args req va).
    iExists _, _. iFrame "Hhost".
    iSplitR.
    { rewrite lookup_insert. eauto. }
    iApply "Hfget".
  }
  iSplit.
  {
    iIntros (args req).
    iExists _, _. iFrame "Hhost".
    iSplitR.
    { rewrite lookup_insert_ne; eauto. rewrite lookup_insert. eauto. }
    iApply "Hfput".
  }
  iNamed "Hsrv".
  iNamed "His_rpc".
  iFrame "#".
Qed.

Lemma MakeKVClerk_spec γ (srv : u64) (cid : u64) :
  {{{ is_kvserver_host γ srv ∗ kvserver_cid_token γ cid }}}
    MakeKVClerk #srv #cid
  {{{ ck, RET #ck; own_kvclerk γ ck srv }}}.
Proof.
  iIntros (Φ) "[#Hserver Hcid] HΦ". wp_lam.
  rewrite /kvserver_cid_token /own_kvclerk.
  iApply wp_fupd.

  wp_apply wp_allocStruct; first by eauto.
  iIntros (l) "Hl". wp_pures.
  iDestruct (struct_fields_split with "Hl") as "(l_primary & l_client & _)".
  wp_storeField.
  wp_apply (MakeRPCClient_spec with "Hcid").
  iIntros (cl) "Hcl".
  wp_storeField.
  iApply "HΦ". iExists _.
  by iFrame.
Qed.

End kv_proof.
