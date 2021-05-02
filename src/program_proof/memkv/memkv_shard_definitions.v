From Perennial.program_proof Require Import dist_prelude.
From Perennial.goose_lang Require Import adequacy.
From Goose.github_com.mit_pdos.gokv Require Import memkv.
From Perennial.program_proof.lockservice Require Import rpc.
From Perennial.program_proof.memkv Require Export common_proof.
From Perennial.program_proof.memkv Require Export rpc_proof memkv_ghost memkv_marshal_put_proof memkv_marshal_get_proof memkv_marshal_conditional_put_proof memkv_marshal_install_shard_proof memkv_marshal_getcid_proof memkv_marshal_move_shard_proof.
From iris.bi.lib Require Import fixpoint.

Open Scope Z.

(** "universal" reply type for the reply cache *)
Record ShardReplyC := mkShardReplyC {
  SR_Err : u64;
  SR_Value : list u8;
  SR_Success : bool;
}.

Section memkv_shard_pre_definitions.

Context `{rpcG Σ ShardReplyC, rpcregG Σ, kvMapG Σ, invG Σ, groveG Σ}.
Context `{!heapPreG Σ (ext:=grove_op) (ffi:=grove_model)}.
(*
, rpcG Σ ShardReplyC, rpcregG Σ, kvMapG Σ}.
*)

Definition uKV_FRESHCID: nat :=
  Eval vm_compute in match KV_FRESHCID with LitV (LitInt n) => int.nat n | _ => 0 end.
Definition uKV_PUT: nat :=
  Eval vm_compute in match KV_PUT with LitV (LitInt n) => int.nat n | _ => 0 end.
Definition uKV_CONDITIONAL_PUT: nat :=
  Eval vm_compute in match KV_CONDITIONAL_PUT with LitV (LitInt n) => int.nat n | _ => 0 end.
Definition uKV_GET: nat :=
  Eval vm_compute in match KV_GET with LitV (LitInt n) => int.nat n | _ => 0 end.
Definition uKV_INS_SHARD: nat :=
  Eval vm_compute in match KV_INS_SHARD with LitV (LitInt n) => int.nat n | _ => 0 end.
Definition uKV_MOV_SHARD: nat :=
  Eval vm_compute in match KV_MOV_SHARD with LitV (LitInt n) => int.nat n | _ => 0 end.

Record memkv_shard_names := {
 rpc_gn : rpc_names ;
 urpc_gn : server_chan_gnames ;
 kv_gn : gname
}
.

Implicit Type γ : memkv_shard_names.

Definition PreShardGet Eo Ei γkv key Q : iProp Σ :=
  |={Eo,Ei}=> (∃ v, kvptsto γkv key v ∗ (kvptsto γkv key v -∗ |={Ei,Eo}=> Q v))
.

Definition PostShardGet Eo Ei γkv (key:u64) Q (rep:ShardReplyC) : iProp Σ :=
  ⌜rep.(SR_Err) ≠ 0⌝ ∗ (PreShardGet Eo Ei γkv key Q) ∨ ⌜rep.(SR_Err) = 0⌝ ∗ (Q rep.(SR_Value)).

Definition PreShardPut Eo Ei γkv key Q v : iProp Σ :=
  |={Eo,Ei}=> (∃ oldv, kvptsto γkv key oldv ∗ (kvptsto γkv key v -∗ |={Ei,Eo}=> Q))
.

Definition PostShardPut Eo Ei γkv (key:u64) Q v (rep:ShardReplyC) : iProp Σ :=
  ⌜rep.(SR_Err) ≠ 0⌝ ∗ (PreShardPut Eo Ei γkv key Q v) ∨ ⌜rep.(SR_Err) = 0⌝ ∗ Q .

Definition PreShardConditionalPut Eo Ei γkv key Q expv newv : iProp Σ :=
  |={Eo,Ei}=> (∃ oldv, kvptsto γkv key oldv ∗
    (let succ := bool_decide (expv = oldv) in kvptsto γkv key (if succ then newv else oldv) -∗
      |={Ei,Eo}=> Q succ))
.

Definition PostShardConditionalPut Eo Ei γkv (key:u64) Q expv newv (rep:ShardReplyC) : iProp Σ :=
  ⌜rep.(SR_Err) ≠ 0⌝ ∗ (PreShardConditionalPut Eo Ei γkv key Q expv newv) ∨ ⌜rep.(SR_Err) = 0⌝ ∗ Q rep.(SR_Success).


Definition is_shard_server_pre (ρ:u64 -d> memkv_shard_names -d> iPropO Σ) : (u64 -d> memkv_shard_names -d> iPropO Σ) :=
  λ host γ,
  ("#His_rpc" ∷ is_RPCServer γ.(rpc_gn) ∗
  "#HputSpec" ∷ handler_is (urpc_gn γ) (coPset * coPset * (iProp Σ) * rpc_request_names) host uKV_PUT
             (λ x reqData, ∃ req, ⌜has_encoding_PutRequest reqData req⌝ ∗
                  is_RPCRequest γ.(rpc_gn) x.2
                     (PreShardPut x.1.1.1 x.1.1.2 γ.(kv_gn) req.(PR_Key) x.1.2 req.(PR_Value))
                     (PostShardPut x.1.1.1 x.1.1.2 γ.(kv_gn) req.(PR_Key) x.1.2 req.(PR_Value))
                     {| Req_CID:=req.(PR_CID); Req_Seq:=req.(PR_Seq) |}
             ) (* pre *)
             (λ x reqData repData, ∃ req rep, ⌜has_encoding_PutReply repData rep⌝ ∗
                  ⌜has_encoding_PutRequest reqData req⌝ ∗
                  (RPCRequestStale γ.(rpc_gn) {| Req_CID:=req.(PR_CID); Req_Seq:=req.(PR_Seq) |} ∨
                    ∃ dummy_val dummy_succ, RPCReplyReceipt γ.(rpc_gn) {| Req_CID:=req.(PR_CID); Req_Seq:=req.(PR_Seq) |} (mkShardReplyC rep.(PR_Err) dummy_val dummy_succ))
             ) (* post *) ∗

  "#HconditionalPutSpec" ∷ handler_is (urpc_gn γ) (coPset * coPset * (bool → iProp Σ) * rpc_request_names) host uKV_CONDITIONAL_PUT
             (λ x reqData, ∃ req, ⌜has_encoding_ConditionalPutRequest reqData req⌝ ∗
                  is_RPCRequest γ.(rpc_gn) x.2
                     (PreShardConditionalPut x.1.1.1 x.1.1.2 γ.(kv_gn) req.(CPR_Key) x.1.2 req.(CPR_ExpValue) req.(CPR_NewValue))
                     (PostShardConditionalPut x.1.1.1 x.1.1.2 γ.(kv_gn) req.(CPR_Key) x.1.2 req.(CPR_ExpValue) req.(CPR_NewValue))
                     {| Req_CID:=req.(CPR_CID); Req_Seq:=req.(CPR_Seq) |}
             ) (* pre *)
             (λ x reqData repData, ∃ req rep, ⌜has_encoding_ConditionalPutReply repData rep⌝ ∗
                  ⌜has_encoding_ConditionalPutRequest reqData req⌝ ∗
                  (RPCRequestStale γ.(rpc_gn) {| Req_CID:=req.(CPR_CID); Req_Seq:=req.(CPR_Seq) |} ∨
                    ∃ dummy_val, RPCReplyReceipt γ.(rpc_gn) {| Req_CID:=req.(CPR_CID); Req_Seq:=req.(CPR_Seq) |} (mkShardReplyC rep.(CPR_Err) dummy_val rep.(CPR_Succ)))
             ) (* post *) ∗

  "#HgetSpec" ∷ handler_is (urpc_gn γ) (coPset * coPset * (list u8 → iProp Σ) * rpc_request_names) host uKV_GET
             (λ x reqData, ∃ req, ⌜has_encoding_GetRequest reqData req⌝ ∗
                  is_RPCRequest γ.(rpc_gn) x.2 (PreShardGet x.1.1.1 x.1.1.2 γ.(kv_gn) req.(GR_Key) x.1.2)
                    (PostShardGet x.1.1.1 x.1.1.2 γ.(kv_gn) req.(GR_Key) x.1.2)
                    {| Req_CID:=req.(GR_CID); Req_Seq:=req.(GR_Seq) |}
             ) (* pre *)
             (λ x reqData repData, ∃ req rep, ⌜has_encoding_GetReply repData rep⌝ ∗
                  ⌜has_encoding_GetRequest reqData req⌝ ∗
                  (RPCRequestStale γ.(rpc_gn) {| Req_CID:=req.(GR_CID); Req_Seq:=req.(GR_Seq) |} ∨
                    ∃ dummy_succ, RPCReplyReceipt γ.(rpc_gn) {| Req_CID:=req.(GR_CID); Req_Seq:=req.(GR_Seq) |} (mkShardReplyC rep.(GR_Err) rep.(GR_Value) dummy_succ))
             ) (* post *) ∗

  "#HmoveSpec" ∷ handler_is (urpc_gn γ) (memkv_shard_names) host uKV_MOV_SHARD
             (λ x reqData, ∃ args, ⌜has_encoding_MoveShardRequest reqData args⌝ ∗
                                  ⌜int.Z args.(MR_Sid) < uNSHARD⌝ ∗
                                  (▷ ρ args.(MR_Dst) x)
             ) (* pre *)
             (λ x reqData repData, True
             ) (* post *) ∗

  "#HinstallSpec" ∷ handler_is (urpc_gn γ) (rpc_request_names) host uKV_INS_SHARD
             (λ x reqData, ∃ args, ⌜has_encoding_InstallShardRequest reqData args⌝ ∗
                                  ⌜int.Z args.(IR_Sid) < uNSHARD⌝ ∗
                                  is_RPCRequest γ.(rpc_gn) x (own_shard γ.(kv_gn) args.(IR_Sid) args.(IR_Kvs))
                                                            (λ _, True)
                                                            {| Req_CID:=args.(IR_CID); Req_Seq:=args.(IR_Seq) |}
             ) (* pre *)
             (λ x reqData repData, True
             ) (* post *) ∗

  "#HfreshSpec" ∷ handler_is (urpc_gn γ) unit host uKV_FRESHCID
             (λ x reqData, True
             ) (* pre *)
             (λ x reqData repData, ∃ cid, ⌜has_encoding_Uint64 repData cid⌝ ∗
              RPCClient_own_ghost γ.(rpc_gn) cid 1
             ) (* post *)
             )%I
.

(* Actually, handler_is is contractive now so we can remove the ▷ in is_shard_server *)
Instance is_shard_server_pre_contr : Contractive is_shard_server_pre.
Proof.
  rewrite /is_shard_server_pre=> n is1 is2 Hpre host γ.
  do 4 (f_contractive || f_equiv).
  f_equiv. rewrite /handler_is.
  do 10 f_equiv.
  unfold named.
  apply saved_prop.saved_pred_own_contractive.
  rewrite /dist_later. destruct n; auto.
  intros => ?.
  rewrite /is_rpcHandler.
  do 21 f_equiv.
  f_contractive. simpl in Hpre.
  eapply (dist_S). eapply Hpre.
Qed.

Definition is_shard_server :=
  fixpoint (is_shard_server_pre).

(* TODO: seal is_shard_server *)

Lemma is_shard_server_unfold host γ :
  is_shard_server host γ ⊣⊢ is_shard_server_pre (is_shard_server) host γ
.
Proof.
  apply (fixpoint_unfold (is_shard_server_pre)).
Qed.

Global Instance is_shard_server_pers host γ : Persistent (is_shard_server host γ).
Proof.
  rewrite is_shard_server_unfold.
  apply _.
Qed.
End memkv_shard_pre_definitions.

Section memkv_shard_definitions.

Context `{!heapG Σ (ext:=grove_op) (ffi:=grove_model), rpcG Σ ShardReplyC, rpcregG Σ, kvMapG Σ}.
Global Instance heapG_to_preG' : heapG Σ → heapPreG Σ := heapG_to_preG Σ.

Definition own_MemKVShardClerk (ck:loc) γ : iProp Σ :=
  ∃ (cid seq:u64) (cl:loc) (host:u64),
    "Hcid" ∷ ck ↦[MemKVShardClerk :: "cid"] #cid ∗
    "Hseq" ∷ ck ↦[MemKVShardClerk :: "seq"] #seq ∗
    "Hcl" ∷ ck ↦[MemKVShardClerk :: "cl"] #cl ∗
    "Hcrpc" ∷ RPCClient_own_ghost γ.(rpc_gn) cid seq ∗
    "Hcl_own" ∷ RPCClient_own cl host ∗
    "#His_shard" ∷ is_shard_server host γ ∗
    "%HseqPostitive" ∷ ⌜0%Z < int.Z seq⌝%Z
.

Definition memKVN := nroot .@ "memkv".

Definition own_MemKVShardServer (s:loc) γ : iProp Σ :=
  ∃ (lastReply_ptr lastSeq_ptr peers_ptr:loc) (kvss_sl shardMap_sl:Slice.t)
    (lastReplyM:gmap u64 ShardReplyC) (lastReplyMV:gmap u64 goose_lang.val) (lastSeqM:gmap u64 u64) (nextCID:u64) (shardMapping:list bool) (kvs_ptrs:list loc)
    (peersM:gmap u64 loc),
  "HlastReply" ∷ s ↦[MemKVShardServer :: "lastReply"] #lastReply_ptr ∗
  "HlastReplyMap" ∷ map.is_map lastReply_ptr 1 (lastReplyMV, zero_val (struct.t ShardReply)) ∗ (* TODO: default *)
  "%HlastReplyMVdom" ∷ ⌜dom (gset u64) lastReplyMV = dom (gset u64) lastSeqM⌝ ∗
  "HlastReply_structs" ∷ ([∗ map] k ↦ v;rep ∈ lastReplyMV ; lastReplyM,
    (∃ val_sl q, ⌜v = struct.mk_f ShardReply [
              "Err" ::= #rep.(SR_Err);
              "Value" ::= slice_val val_sl;
              "Success" ::= #rep.(SR_Success)
            ]%V⌝ ∗ typed_slice.is_slice_small val_sl byteT q rep.(SR_Value))) ∗
  "HlastSeq" ∷ s ↦[MemKVShardServer :: "lastSeq"] #lastSeq_ptr ∗
  "HlastSeqMap" ∷ is_map lastSeq_ptr 1 lastSeqM ∗
  "HnextCID" ∷ s ↦[MemKVShardServer :: "nextCID"] #nextCID ∗
  "HshardMap" ∷ s ↦[MemKVShardServer :: "shardMap"] (slice_val shardMap_sl) ∗
  "HshardMap_sl" ∷ typed_slice.is_slice shardMap_sl boolT 1%Qp shardMapping ∗
  "Hkvss" ∷ s ↦[MemKVShardServer :: "kvss"] (slice_val kvss_sl) ∗
  "Hkvss_sl" ∷ slice.is_slice kvss_sl (mapT (slice.T byteT)) 1%Qp (fmap (λ x:loc, #x) kvs_ptrs) ∗
  "Hpeers" ∷ s ↦[MemKVShardServer :: "peers"] #peers_ptr ∗
  "Hrpc" ∷ RPCServer_own_ghost γ.(rpc_gn) lastSeqM lastReplyM ∗
  "%HshardMapLength" ∷ ⌜Z.of_nat (length shardMapping) = uNSHARD⌝ ∗
  "%HkvssLength" ∷ ⌜Z.of_nat (length kvs_ptrs) = uNSHARD⌝ ∗
  "HownShards" ∷ ([∗ set] sid ∈ (fin_to_set u64),
                  ⌜(shardMapping !! (int.nat sid)) ≠ Some true⌝ ∨
                  (∃ (kvs_ptr:loc) (m:gmap u64 (list u8)) (mv:gmap u64 goose_lang.val),
                      own_shard γ.(kv_gn) sid m ∗ (* own shard *)
                      ⌜kvs_ptrs !! (int.nat sid) = Some kvs_ptr⌝ ∗
                      map.is_map kvs_ptr 1 (mv, (slice_val Slice.nil)) ∗
                      ([∗ set] k ∈ (fin_to_set u64),
                       ⌜shardOfC k ≠ sid⌝ ∨ (∃ vsl, ⌜default (slice_val Slice.nil) (mv !! k) = (slice_val vsl)⌝ ∗ typed_slice.is_slice vsl byteT (1%Qp) (default [] (m !! k))) )
                  )
                 ) ∗
  "HpeersMap" ∷ is_map (V:=loc) peers_ptr 1 peersM ∗
  "HpeerClerks" ∷ ([∗ map] k ↦ ck ∈ peersM, (∃ γsh, own_MemKVShardClerk ck γsh ∗ ⌜γsh.(kv_gn) = γ.(kv_gn)⌝)) ∗
  "Hcids" ∷ [∗ set] cid ∈ (fin_to_set u64), ⌜int.Z cid < int.Z nextCID⌝%Z ∨ (RPCClient_own_ghost γ.(rpc_gn) cid 1)
.

Definition is_MemKVShardServer (s:loc) γ : iProp Σ :=
  ∃ mu,
  "#His_srv" ∷ is_RPCServer γ.(rpc_gn) ∗
  "#Hmu" ∷ readonly (s ↦[MemKVShardServer :: "mu"] mu) ∗
  "#HmuInv" ∷ is_lock memKVN mu (own_MemKVShardServer s γ)
.

End memkv_shard_definitions.
