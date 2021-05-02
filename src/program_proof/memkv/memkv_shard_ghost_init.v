From Perennial.algebra Require Import gen_heap_names.
From Perennial.goose_lang Require Import adequacy recovery_adequacy dist_adequacy.
From Perennial.program_proof Require Import dist_prelude.
From Goose.github_com.mit_pdos.gokv Require Import memkv.
From Perennial.program_proof.lockservice Require Import rpc.

From Perennial.program_proof.memkv Require Export memkv_shard_definitions.

Section memkv_shard_ghost_init_proof.

(* These lemmas happen *before* we get node local names (e.g. the gname for memory, crashes etc. *)
Context `{!heapPreG Σ, !heap_globalG Σ, rpcG Σ ShardReplyC, rpcregG Σ, kvMapG Σ, invG Σ}.

Let gn := heap_globalG_names.
Let gpG := (heap_preG_ffi).

Instance local_groveG : groveG Σ := {| groveG_gen_heapG := gen_heapG_update_pre (@grove_preG_gen_heapG _ gpG) gn |}.


(* TODO: duplicating these specs is unfortunate, should try to unify with the set up in shard_definitions *)
Definition is_shard_server_putSpec (γkv : gname) γrpc : RPCSpec :=
  {| spec_rpcid := uKV_PUT;
     spec_ty := (coPset * coPset * (iProp Σ) * rpc_request_names)%type;
     spec_Pre := (λ x reqData, ∃ req, ⌜has_encoding_PutRequest reqData req⌝ ∗
                  is_RPCRequest γrpc x.2
                     (PreShardPut x.1.1.1 x.1.1.2 γkv req.(PR_Key) x.1.2 req.(PR_Value))
                     (PostShardPut x.1.1.1 x.1.1.2 γkv req.(PR_Key) x.1.2 req.(PR_Value))
                     {| Req_CID:=req.(PR_CID); Req_Seq:=req.(PR_Seq) |})%I;
     spec_Post := (λ x reqData repData, ∃ req rep, ⌜has_encoding_PutReply repData rep⌝ ∗
                  ⌜has_encoding_PutRequest reqData req⌝ ∗
                  (RPCRequestStale γrpc {| Req_CID:=req.(PR_CID); Req_Seq:=req.(PR_Seq) |} ∨
                    ∃ dummy_val dummy_succ, RPCReplyReceipt γrpc
                                                            {| Req_CID:=req.(PR_CID); Req_Seq:=req.(PR_Seq) |}
                                                            (mkShardReplyC rep.(PR_Err) dummy_val dummy_succ))
             )%I |}.

Definition is_shard_server_conditionalPutSpec γkv γrpc : RPCSpec :=
  {| spec_rpcid := uKV_CONDITIONAL_PUT;
     spec_ty := (coPset * coPset * (bool → iProp Σ) * rpc_request_names);
     spec_Pre :=(λ x reqData, ∃ req, ⌜has_encoding_ConditionalPutRequest reqData req⌝ ∗
                  is_RPCRequest γrpc x.2
                     (PreShardConditionalPut x.1.1.1 x.1.1.2 γkv req.(CPR_Key) x.1.2 req.(CPR_ExpValue) req.(CPR_NewValue))
                     (PostShardConditionalPut x.1.1.1 x.1.1.2 γkv req.(CPR_Key) x.1.2 req.(CPR_ExpValue) req.(CPR_NewValue))
                     {| Req_CID:=req.(CPR_CID); Req_Seq:=req.(CPR_Seq) |}
             )%I;
     spec_Post :=(λ x reqData repData, ∃ req rep, ⌜has_encoding_ConditionalPutReply repData rep⌝ ∗
                  ⌜has_encoding_ConditionalPutRequest reqData req⌝ ∗
                  (RPCRequestStale γrpc {| Req_CID:=req.(CPR_CID); Req_Seq:=req.(CPR_Seq) |} ∨
                    ∃ dummy_val, RPCReplyReceipt γrpc {| Req_CID:=req.(CPR_CID); Req_Seq:=req.(CPR_Seq) |} (mkShardReplyC rep.(CPR_Err) dummy_val rep.(CPR_Succ)))
             )%I |}.

Definition is_shard_server_getSpec γkv γrpc : RPCSpec :=
  {| spec_rpcid := uKV_GET;
     spec_ty := (coPset * coPset * (list u8 → iProp Σ) * rpc_request_names);
     spec_Pre := (λ x reqData, ∃ req, ⌜has_encoding_GetRequest reqData req⌝ ∗
                  is_RPCRequest γrpc x.2 (PreShardGet x.1.1.1 x.1.1.2 γkv req.(GR_Key) x.1.2)
                    (PostShardGet x.1.1.1 x.1.1.2 γkv req.(GR_Key) x.1.2)
                    {| Req_CID:=req.(GR_CID); Req_Seq:=req.(GR_Seq) |}
             )%I;
     spec_Post :=(λ x reqData repData, ∃ req rep, ⌜has_encoding_GetReply repData rep⌝ ∗
                  ⌜has_encoding_GetRequest reqData req⌝ ∗
                  (RPCRequestStale γrpc {| Req_CID:=req.(GR_CID); Req_Seq:=req.(GR_Seq) |} ∨
                    ∃ dummy_succ, RPCReplyReceipt γrpc {| Req_CID:=req.(GR_CID); Req_Seq:=req.(GR_Seq) |} (mkShardReplyC rep.(GR_Err) rep.(GR_Value) dummy_succ))
             )%I |}.

Definition is_shard_server_moveSpec : @RPCSpec Σ :=
  {| spec_rpcid := uKV_MOV_SHARD;
     spec_ty := memkv_shard_names;
     spec_Pre :=(λ x reqData, ∃ args, ⌜has_encoding_MoveShardRequest reqData args⌝ ∗
                                  ⌜int.Z args.(MR_Sid) < uNSHARD⌝ ∗
                                  (▷ is_shard_server args.(MR_Dst) x)
             )%I;
     spec_Post := (λ x reqData repData, True)%I |}.

Definition is_shard_server_installSpec γkv γrpc : RPCSpec :=
  {| spec_rpcid := uKV_INS_SHARD;
     spec_ty := rpc_request_names;
     spec_Pre := (λ x reqData, ∃ args, ⌜has_encoding_InstallShardRequest reqData args⌝ ∗
                                  ⌜int.Z args.(IR_Sid) < uNSHARD⌝ ∗
                                  is_RPCRequest γrpc x (own_shard γkv args.(IR_Sid) args.(IR_Kvs))
                                                            (λ _, True)
                                                            {| Req_CID:=args.(IR_CID); Req_Seq:=args.(IR_Seq) |}
             )%I;
     spec_Post := (λ x reqData repData, True)%I |}.

Definition is_shard_server_freshSpec γrpc : RPCSpec :=
  {| spec_rpcid := uKV_FRESHCID;
     spec_ty := unit;
     spec_Pre := (λ x reqData, True)%I;
     spec_Post := (λ x reqData repData, ∃ cid, ⌜has_encoding_Uint64 repData cid⌝ ∗
              RPCClient_own_ghost γrpc cid 1)%I |}.

Definition shard_SpecList γkv γrpc : RPCSpecList :=
  spec_cons (is_shard_server_putSpec γkv γrpc)
    (spec_cons (is_shard_server_conditionalPutSpec γkv γrpc)
      (spec_cons (is_shard_server_getSpec γkv γrpc)
        (spec_cons (is_shard_server_moveSpec)
          (spec_cons (is_shard_server_installSpec γkv γrpc)
            (spec_cons (is_shard_server_freshSpec γrpc) spec_nil))))).

Lemma shard_server_ghost_init host (γkv : gname) :
  host c↦ ∅ ={⊤}=∗
  ∃ γ, ⌜ γ.(kv_gn) = γkv ⌝ ∗
       is_shard_server host γ ∗
       RPCServer_own_ghost γ.(rpc_gn) ∅ ∅ ∗
      ([∗ set] cid ∈ fin_to_set u64, RPCClient_own_ghost γ.(rpc_gn) cid 1).
Proof.
  iIntros "Hg".
  iMod (make_rpc_server (R := ShardReplyC)) as (γrpc) "(#Hown&Hrpc1&Hrpc2)".
  { set_solver. }
  iMod (handler_is_init_list host (shard_SpecList γkv γrpc) with "[Hg]") as (γ) "H".
  { simpl. set_solver. }
  { iExactEq "Hg". f_equal. }
  iDestruct "H" as "(#Hdom&#Hput&#Hcput&#Hget&#Hmove&#Hinstall&#Hfresh&_)".

  set (Γsrv := {| rpc_gn := γrpc; urpc_gn := γ; kv_gn := γkv |}).
  iAssert (is_shard_server host Γsrv) as "Hshard".
  {
    rewrite is_shard_server_unfold /is_shard_server_pre.
    iSplitL.
    { iFrame "#Hown". }
    iSplitL. { iFrame "Hput". }
    iSplitL. { iFrame "Hcput". }
    iSplitL. { iFrame "Hget". }
    iSplitL. { iFrame "Hmove". }
    iSplitL. { iFrame "Hinstall". }
    iFrame "Hfresh".
  }
  iExists Γsrv. iFrame "# ∗".
  eauto.
Qed.

End memkv_shard_ghost_init_proof.
