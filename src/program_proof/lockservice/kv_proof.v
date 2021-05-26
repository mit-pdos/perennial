From stdpp Require Import gmap.
From Perennial.algebra Require Import auth_map.
From Perennial.goose_lang.lib Require Import lock.
From Perennial.program_proof.lockservice Require Import grove_ffi.
From Perennial.program_proof Require Import disk_prelude.
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

(* FIXME: this is currently just a placeholder *)
Definition KVClerk_own γ ck_ptr (host : string) : iProp Σ :=
  ∃ (cl_ptr:loc),
   "Hcl_ptr" ∷ ck_ptr ↦[KVClerk :: "client"] #cl_ptr ∗
   "Hprimary" ∷ ck_ptr ↦[KVClerk :: "primary"] #(str host) ∗
   "Hcl" ∷ RPCClient_own cl_ptr host γ.(ks_rpcGN).

Print is_lock.

Definition KVServer_own_core γ srv kvsM : iProp Σ :=
  ∃ (kvs_ptr:loc),
  "HlocksOwn" ∷ srv ↦[KVServer :: "kvs"] #kvs_ptr ∗
  "HkvsMap" ∷ is_map (kvs_ptr) kvsM ∗
  "Hkvctx" ∷ map_ctx γ.(ks_kvMapGN) 1 kvsM (* ghost part *)
.

Definition KVServer_mutex_inv γ (srv:loc) : iProp Σ :=
  ∃ (sv:loc) (kvsM lastSeqM lastReplyM:gmap u64 u64),
  "Hcore" ∷ KVServer_own_core γ srv kvsM ∗
  "Hsv" ∷ srv ↦[KVServer :: "sv"] #sv ∗
  "Hrpc_vol" ∷ RPCServer_own_vol sv γ.(ks_rpcGN) lastSeqM lastReplyM ∗
  "Hrpc_ghost" ∷ RPCServer_own_ghost γ.(ks_rpcGN) lastSeqM lastReplyM
.

Definition mutexN := nroot .@ "kvservermutex".

Definition is_kvserver γ (srv:loc) : iProp Σ :=
  ∃ mu,
  "#Hmu" ∷ readonly (srv ↦[KVServer :: "mu"] mu) ∗
  "#His_rpc" ∷ is_lock mutexN mu (KVServer_mutex_inv γ srv)
.

Lemma put_core_spec γ (srv:loc) :
{{{
     True
}}}
  KVServer__put_core #srv
{{{
     (f:goose_lang.val), RET f;
     ∀ args kvsM,
     {{{
         KVServer_own_core γ srv kvsM ∗ ▷ Put_Pre γ args
     }}}
        f (into_val.to_val args)
      {{{
           kvsM', RET #0; KVServer_own_core γ srv kvsM'
                                            ∗ ▷ Put_Post γ args 0
      }}}
}}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_lam.
  wp_pures.
  iApply "HΦ".
  iIntros (??).
  clear Φ.

  iIntros (Φ) "!# [Hksown Hpre] Hpost".
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
  iFrame. iExists _; iFrame.
Qed.

Lemma get_core_spec (srv:loc) γ :
{{{
     True
}}}
  KVServer__get_core #srv
{{{
     (f:goose_lang.val), RET f;
     ∀ args va kvsM,
     {{{
         KVServer_own_core γ srv kvsM ∗ ▷ Get_Pre γ va args
     }}}
        f (into_val.to_val args)
      {{{
           kvsM', RET #va; KVServer_own_core γ srv kvsM'
                                            ∗ ▷ Get_Post γ va args va
      }}}
}}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_lam.
  wp_pures.
  iApply "HΦ".
  iIntros (???).
  clear Φ.

  iIntros (Φ) "!# [Hksown Hpre] Hpost".
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
  iSplit; last done. iExists _; iFrame.
Qed.

Lemma KVServer__Get_spec srv γ :
is_kvserver γ srv -∗
{{{
    True
}}}
    KVServer__Get #srv
{{{ (f:goose_lang.val), RET f;
        ∀ va, is_rpcHandlerEncoded f γ.(ks_rpcGN) (Get_Pre γ va) (Get_Post γ va)
}}}.
Proof.
  iIntros "#Hls".
  iIntros (Φ) "!# _ Hpost".
  wp_lam.
  wp_pures.
  iApply "Hpost".
  iIntros (?).
  clear Φ.
  iIntros (?????? Φ) "!# Hpre HΦ".
  iNamed "Hpre".
  wp_pures.
  iNamed "Hls".
  wp_loadField.
  wp_apply (acquire_spec with "[$His_rpc]").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".
  wp_pures.
  wp_apply (get_core_spec srv γ).
  iIntros (fget) "#Hfget".
  wp_pures.
  wp_loadField.
  wp_apply (RPCServer__HandleRequest_spec _ _ _ _ (KVServer_own_core γ srv kvsM) (∃ kvsM', KVServer_own_core γ srv kvsM')%I _ _ _ with "[] [Hargs Hrpc_vol Hrpc_ghost Hreply Hcore]").
  {
    clear Φ.
    iIntros (Φ) "!# Hpre HΦ".
    wp_apply ("Hfget" with "[- HΦ]").
    {
      iDestruct "Hpre" as "[$ Hpre]".
      iFrame "Hpre".
    }
    iIntros (?) "[Hctx' Hpost]".
    iApply "HΦ".
    iFrame.
    iExists _; iFrame.
  }
  {
    iFrame "∗ #".
    iExists _; iFrame.
  }
  iIntros (?) "HH".
  iDestruct "HH" as (??) "(Hrpc_vol & Hrpc_ghost & Hreply & #Hpost & Hkv_own)".
  wp_pures.
  wp_loadField.
  wp_apply (release_spec with "[$His_rpc $Hlocked Hrpc_vol Hrpc_ghost Hkv_own Hsv]").
  {
    iNext.
    iDestruct "Hkv_own" as "[Hkv_own|Hkv_own]".
    { iExists _, _, _, _. iFrame. }
    {
      iDestruct "Hkv_own" as (?) "H".
      iExists _, _, _, _. iFrame.
    }
  }

  wp_pures.
  iApply "HΦ".
  iExists _; iFrame.
  iFrame "Hpost".
Qed.

(*
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
*)

(* TODO: see if any more repetition can be removed *)

Definition is_kvserver_host γ (host:string) : iProp Σ :=
    "#Hputspec" ∷ (
      handler_is2 host (U64 1) γ.(ks_rpcGN) (Put_Pre γ) (Put_Post γ)) ∗
    "#Hgetspec" ∷ (∀ va,
      handler_is2 host (U64 2) γ.(ks_rpcGN) (Get_Pre γ va) (Get_Post γ va)) ∗
    "#Hrpcserver" ∷ is_RPCServer γ.(ks_rpcGN).

Lemma KVClerk__Get_spec (kck:loc) (srv:string) (key va:u64) γ  :
is_kvserver_host γ srv -∗
{{{
     KVClerk_own γ kck srv ∗ (key [[γ.(ks_kvMapGN)]]↦ va)
}}}
  KVClerk__Get #kck #key
{{{
     v, RET #v; ⌜v = va⌝ ∗ KVClerk_own γ kck srv ∗ (key [[γ.(ks_kvMapGN)]]↦ va )
}}}.
Proof.
  iIntros "#Hserver" (Φ) "!# (Hclerk & Hpre) Hpost".
  wp_lam.
  wp_pures. 
  iNamed "Hclerk".
  repeat wp_loadField.
  wp_apply (RPCClient__MakeRequest_spec _ _ _ {|U64_1:=_ ; U64_2:= _ |} γ.(ks_rpcGN) with "[] [Hpre Hcl]"); eauto.
  {
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

Lemma KVClerk__Put_spec (kck:loc) (srv:string) (key va:u64) γ :
is_kvserver_host γ srv -∗
{{{
     KVClerk_own γ kck srv ∗ (key [[γ.(ks_kvMapGN)]]↦ _ )
}}}
  KVClerk__Put #kck #key #va
{{{
     RET #();
     KVClerk_own γ kck srv ∗ (key [[γ.(ks_kvMapGN)]]↦ va )
}}}.
Proof.
  iIntros "#Hserver" (Φ) "!# (Hclerk & Hpre) Hpost".
  wp_lam.
  wp_pures. 
  iNamed "Hclerk".
  repeat wp_loadField.
  wp_apply (RPCClient__MakeRequest_spec _ _ _ {| U64_1:= _; U64_2:=_ |} γ.(ks_rpcGN) with "[] [Hpre Hcl]"); eauto.
  {
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
  RPCClient_own_ghost γ.(ks_rpcGN) cid 1.

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
  iDestruct (struct_fields_split with "Hl") as "(l_mu & l_sv & l_kvs & _)".
  wp_apply (wp_new_free_lock).
  iIntros (mu) "Hmu".
  wp_storeField.
  wp_apply (wp_NewMap u64 (t:=uint64T)). iIntros (kvs) "Hkvs".
  wp_storeField.
  wp_apply (MakeRPCServer_spec with "[$is_server]").
  iIntros (sv) "Hrpcown".
  wp_storeField.
  iApply ("HΦ" $! γ).
  iFrame "cli_tokens".
  iExists _.
  iMod (readonly_alloc_1 with "l_mu") as "$".
  iApply (alloc_lock with "Hmu [-]").
  iExists _, _, _, _.
  iNext.
  iFrame "∗#".
  iExists _.
  iFrame.
Qed.
(* TODO: return all of the ptsto's here; update KVServer_own_core so it has map_ctx bigger than the physical map *)

Opaque zero_val.
Lemma KVServer_AllocServer_spec γ srv :
is_kvserver γ srv -∗
  {{{ True }}}
    KVServer__Start #srv
  {{{ RET #(); True }}}.
Proof.
  iIntros "#Hsrv !#" (Φ) "_ HΦ".
  wp_lam.
  wp_apply map.wp_NewMap.
  iIntros (mref) "Hm".
  wp_pures.
  wp_lam.
  wp_apply (wp_ConjugateRpcFunc with "[]").
  {
    admit.
  }
  iIntros (fput) "#Hputspec".

  wp_apply (map.wp_MapInsert with "[$Hm]").
  iIntros "Hm".
  unfold map.map_insert.
  rewrite insert_empty.

  wp_pures.
  wp_apply (KVServer__Get_spec with "Hsrv").
  iIntros (fget) "#Hfget".
  wp_apply (wp_ConjugateRpcFunc with "[]").
  {
    iApply "Hfget".
  }

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
  {{{ ck, RET #ck; KVClerk_own γ ck srv }}}.
Proof.
  iIntros (Φ) "[#Hserver Hcid] HΦ". wp_lam.
  rewrite /kvserver_cid_token /KVClerk_own.
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
