From Perennial.program_proof Require Import grove_prelude.
From iris.bi.lib Require Import fixpoint.
From Perennial.goose_lang Require Import adequacy.
From Perennial.goose_lang Require Import dist_lifting.
From Goose.github_com.mit_pdos.gokv Require Import memkv.
From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.grove_shared Require Export  erpc_lib urpc_proof urpc_spec erpc_proof.
From Perennial.program_proof.memkv Require Export common_proof connman_proof memkv_ghost memkv_marshal_put_proof memkv_marshal_get_proof memkv_marshal_conditional_put_proof memkv_marshal_install_shard_proof memkv_marshal_getcid_proof memkv_marshal_move_shard_proof.

#[local] Set Universe Polymorphism.

Section memkv_shard_pre_definitions.

Context `{erpcG Σ, urpcregG Σ, kvMapG Σ}.
Context `{!gooseGlobalGS Σ}.

Definition uKV_FRESHCID: nat :=
  Eval vm_compute in match KV_FRESHCID with LitV (LitInt n) => uint.nat n | _ => 0 end.
Definition uKV_PUT: nat :=
  Eval vm_compute in match KV_PUT with LitV (LitInt n) => uint.nat n | _ => 0 end.
Definition uKV_CONDITIONAL_PUT: nat :=
  Eval vm_compute in match KV_CONDITIONAL_PUT with LitV (LitInt n) => uint.nat n | _ => 0 end.
Definition uKV_GET: nat :=
  Eval vm_compute in match KV_GET with LitV (LitInt n) => uint.nat n | _ => 0 end.
Definition uKV_INS_SHARD: nat :=
  Eval vm_compute in match KV_INS_SHARD with LitV (LitInt n) => uint.nat n | _ => 0 end.
Definition uKV_MOV_SHARD: nat :=
  Eval vm_compute in match KV_MOV_SHARD with LitV (LitInt n) => uint.nat n | _ => 0 end.

Record memkv_shard_names := {
 erpc_gn : erpc_names ;
 urpc_gn : server_chan_gnames ;
 kv_gn : gname
}
.

Implicit Type γ : memkv_shard_names.

Definition PreShardGet γkv key Q : iProp Σ :=
  |={⊤,∅}=> (∃ v, kvptsto γkv key v ∗ (kvptsto γkv key v -∗ |={∅,⊤}=> Q v)).
Definition PostShardGet γkv (key:u64) Q (rep:GetReplyC) : iProp Σ :=
  ⌜rep.(GR_Err) ≠ 0⌝ ∗ (PreShardGet γkv key Q) ∨ ⌜rep.(GR_Err) = 0⌝ ∗ (Q rep.(GR_Value)).
Polymorphic Definition is_shard_server_getSpec γkv : eRPCSpec :=
  {| espec_ty := ((list u8 → iProp Σ) * GetRequestC);
     espec_Pre := (λ '(Q, req) reqData, ⌜has_encoding_GetRequest reqData req⌝ ∗
                    PreShardGet γkv req.(GR_Key) Q
             )%I;
     espec_Post :=(λ '(Q, req) reqData repData, ∃ rep, ⌜has_encoding_GetReply repData rep⌝ ∗
                    PostShardGet γkv req.(GR_Key) Q rep
             )%I |}.

Definition PreShardPut γkv key Q v : iProp Σ :=
  |={⊤,∅}=> (∃ oldv, kvptsto γkv key oldv ∗ (kvptsto γkv key v -∗ |={∅,⊤}=> Q)).
Definition PostShardPut γkv (key:u64) Q v (rep:PutReplyC) : iProp Σ :=
  ⌜rep.(PR_Err) ≠ 0⌝ ∗ (PreShardPut γkv key Q v) ∨ ⌜rep.(PR_Err) = 0⌝ ∗ Q .
Polymorphic Definition is_shard_server_putSpec (γkv : gname) : eRPCSpec :=
  {| espec_ty := (iProp Σ * PutRequestC)%type;
     espec_Pre := (λ '(Q, req) reqData, ⌜has_encoding_PutRequest reqData req⌝ ∗
                     (PreShardPut γkv req.(PR_Key) Q req.(PR_Value))
             )%I;
     espec_Post := (λ '(Q, req) reqData repData, ∃ rep, ⌜has_encoding_PutReply repData rep⌝ ∗
                     (PostShardPut γkv req.(PR_Key) Q req.(PR_Value)) rep
             )%I |}.

Definition PreShardConditionalPut γkv key Q expv newv : iProp Σ :=
  |={⊤,∅}=> (∃ oldv, kvptsto γkv key oldv ∗
    (let succ := bool_decide (expv = oldv) in kvptsto γkv key (if succ then newv else oldv) -∗
      |={∅,⊤}=> Q succ)).
Definition PostShardConditionalPut γkv (key:u64) Q expv newv (rep:ConditionalPutReplyC) : iProp Σ :=
  ⌜rep.(CPR_Err) ≠ 0⌝ ∗ (PreShardConditionalPut γkv key Q expv newv) ∨ ⌜rep.(CPR_Err) = 0⌝ ∗ Q rep.(CPR_Succ).
Polymorphic Definition is_shard_server_conditionalPutSpec γkv : eRPCSpec :=
  {| espec_ty := ((bool → iProp Σ) * ConditionalPutRequestC);
     espec_Pre :=(λ '(Q, req) reqData, ⌜has_encoding_ConditionalPutRequest reqData req⌝ ∗
                  PreShardConditionalPut γkv req.(CPR_Key) Q req.(CPR_ExpValue) req.(CPR_NewValue)
             )%I;
     espec_Post :=(λ '(Q, req) reqData repData, ∃ rep, ⌜has_encoding_ConditionalPutReply repData rep⌝ ∗
                  PostShardConditionalPut γkv req.(CPR_Key) Q req.(CPR_ExpValue) req.(CPR_NewValue) rep
             )%I |}.

Polymorphic Definition is_shard_server_installSpec γkv : eRPCSpec :=
  {| espec_ty := ();
     espec_Pre := (λ _ reqData, ∃ args, ⌜has_encoding_InstallShardRequest reqData args⌝ ∗
                            ⌜uint.Z args.(IR_Sid) < uNSHARD⌝ ∗
                            own_shard γkv args.(IR_Sid) args.(IR_Kvs)
             )%I;
     espec_Post := (λ _ reqData repData, True)%I |}.

Polymorphic Definition is_shard_server_freshSpec γrpc : RpcSpec :=
  {| spec_ty := unit;
     spec_Pre := (λ x reqData, True)%I;
     spec_Post := (λ x reqData repData, ∃ cid, ⌜has_encoding_Uint64 repData cid⌝ ∗
              erpc_make_client_pre γrpc cid)%I |}.

Polymorphic Definition is_shard_server_moveSpec_pre γkv (ρ:u64 -d> memkv_shard_names -d> iPropO Σ) : RpcSpec :=
  {| spec_ty := memkv_shard_names;
     spec_Pre :=(λ x reqData, ∃ args, ⌜has_encoding_MoveShardRequest reqData args⌝ ∗
                                  ⌜uint.Z args.(MR_Sid) < uNSHARD⌝ ∗
                                  (▷ ρ args.(MR_Dst) x) ∗
                                  ⌜ x.(kv_gn) = γkv ⌝
             )%I;
     spec_Post := (λ x reqData repData, True)%I |}.

Polymorphic Definition is_shard_server_pre (ρ:u64 -d> memkv_shard_names -d> iPropO Σ) : (u64 -d> memkv_shard_names -d> iPropO Σ) :=
  (λ host γ,
  "#HputSpec" ∷ is_erpc_spec γ.(urpc_gn) γ.(erpc_gn) host uKV_PUT (is_shard_server_putSpec γ.(kv_gn)) ∗
  "#HconditionalPutSpec" ∷ is_erpc_spec γ.(urpc_gn) γ.(erpc_gn) host uKV_CONDITIONAL_PUT
                                    (is_shard_server_conditionalPutSpec γ.(kv_gn)) ∗
  "#HgetSpec" ∷ is_erpc_spec γ.(urpc_gn) γ.(erpc_gn) host uKV_GET (is_shard_server_getSpec γ.(kv_gn)) ∗
  "#HmoveSpec" ∷ is_urpc_spec γ.(urpc_gn) host uKV_MOV_SHARD (is_shard_server_moveSpec_pre γ.(kv_gn) ρ) ∗
  "#HinstallSpec" ∷ is_erpc_spec γ.(urpc_gn) γ.(erpc_gn) host uKV_INS_SHARD (is_shard_server_installSpec γ.(kv_gn)) ∗
  "#HfreshSpec" ∷ is_urpc_spec γ.(urpc_gn) host uKV_FRESHCID (is_shard_server_freshSpec γ.(erpc_gn))
)%I.

(* Actually, handler_is is contractive now so we can remove the ▷ in is_shard_server *)
Polymorphic Instance is_shard_server_pre_contr : Contractive is_shard_server_pre.
Proof.
  rewrite /is_shard_server_pre=> n is1 is2 Hpre host γ.
  do 4 (f_contractive || f_equiv).
  f_equiv. rewrite /is_urpc_spec /=. (* FIXME unfolding other abstractions (RpcSpec is not an OFE) *)
  f_contractive.
  rewrite /RpcSpec_Spec /is_shard_server_moveSpec_pre /=.
  intros args Φ. simpl.
  repeat f_equiv.
Qed.

Polymorphic Definition is_shard_server_def :=
  fixpoint (is_shard_server_pre).
Polymorphic Definition is_shard_server_aux : seal (is_shard_server_def). by eexists. Qed.
Polymorphic Definition is_shard_server := is_shard_server_aux.(unseal).
Polymorphic Definition is_shard_server_eq : is_shard_server = is_shard_server_def := is_shard_server_aux.(seal_eq).

Definition is_shard_server_moveSpec γkv := is_shard_server_moveSpec_pre γkv is_shard_server.

Polymorphic Lemma is_shard_server_unfold@{u1 u2 u3 u4} host γ :
  is_shard_server@{u1 u2 u3 u4} host γ ≡ is_shard_server_pre@{u1 u2 u3 u4} (is_shard_server@{u1 u2 u3 u4}) host γ
.
Proof.
  rewrite is_shard_server_eq. apply (fixpoint_unfold (is_shard_server_pre)).
Qed.

Global Polymorphic Instance is_shard_server_pers host γ : Persistent (is_shard_server host γ).
Proof.
  rewrite is_shard_server_unfold.
  apply _.
Qed.
End memkv_shard_pre_definitions.

Section memkv_shard_definitions.

Context `{!heapGS Σ (ext:=grove_op) (ffi:=grove_model), erpcG Σ, urpcregG Σ, kvMapG Σ}.

Definition own_KVShardClerk (ck:loc) γkv : iProp Σ :=
  ∃ (c erpc:loc) (host:u64) (γ:memkv_shard_names),
    "Hc" ∷ ck ↦[KVShardClerk :: "c"] #c ∗
    "erpc" ∷ ck ↦[KVShardClerk :: "erpc"] #erpc ∗
    "Hhost" ∷ ck ↦[KVShardClerk :: "host"] #host ∗
    "Herpc" ∷ own_erpc_client γ.(erpc_gn) erpc ∗
    "#Hc_own" ∷ is_ConnMan c ∗
    "#His_shard" ∷ is_shard_server host γ ∗
    "%Hγeq" ∷ ⌜γ.(kv_gn) = γkv⌝
.

Definition memKVN := nroot .@ "memkv".

Definition own_KVShardServer (s:loc) γ : iProp Σ :=
  ∃ (peers_ptr:loc) (kvss_sl shardMap_sl:Slice.t)
    (shardMapping:list bool) (kvs_ptrs:list loc)
    (peersM:gmap u64 loc),
  "HshardMap" ∷ s ↦[KVShardServer :: "shardMap"] (slice_val shardMap_sl) ∗
  "HshardMap_sl" ∷ typed_slice.own_slice shardMap_sl boolT (DfracOwn 1) shardMapping ∗
  "Hkvss" ∷ s ↦[KVShardServer :: "kvss"] (slice_val kvss_sl) ∗
  "Hkvss_sl" ∷ slice.own_slice kvss_sl (mapT (slice.T byteT)) (DfracOwn 1) (fmap (λ x:loc, #x) kvs_ptrs) ∗
  "Hpeers" ∷ s ↦[KVShardServer :: "peers"] #peers_ptr ∗
  "%HshardMapLength" ∷ ⌜Z.of_nat (length shardMapping) = uNSHARD⌝ ∗
  "%HkvssLength" ∷ ⌜Z.of_nat (length kvs_ptrs) = uNSHARD⌝ ∗
  "HownShards" ∷ ([∗ set] sid ∈ (fin_to_set u64),
                  ⌜(shardMapping !! (uint.nat sid)) ≠ Some true⌝ ∨
                  (∃ (kvs_ptr:loc) (m:gmap u64 (list u8)) (mv:gmap u64 goose_lang.val),
                      own_shard γ.(kv_gn) sid m ∗ (* own shard *)
                      ⌜kvs_ptrs !! (uint.nat sid) = Some kvs_ptr⌝ ∗
                      ⌜dom m = dom mv⌝ ∗
                      map.own_map kvs_ptr (DfracOwn 1) (mv, (slice_val Slice.nil)) ∗
                      ([∗ set] k ∈ (fin_to_set u64),
                       ⌜shardOfC k ≠ sid ∧ mv !! k = None ∧ m !! k = None ⌝ ∨ (∃ vsl, ⌜default (slice_val Slice.nil) (mv !! k) = (slice_val vsl)⌝ ∗ typed_slice.own_slice_small vsl byteT DfracDiscarded (default [] (m !! k))) )
                  )
                 ) ∗
  "HpeersMap" ∷ own_map (V:=loc) peers_ptr (DfracOwn 1) peersM ∗
  "HpeerClerks" ∷ ([∗ map] k ↦ ck ∈ peersM, own_KVShardClerk ck γ.(kv_gn))
.

Definition is_KVShardServer (s:loc) γ : iProp Σ :=
  ∃ mu (erpc cm:loc),
  "#Hmu" ∷ readonly (s ↦[KVShardServer :: "mu"] mu) ∗
  "#Herpc" ∷ readonly (s ↦[KVShardServer :: "erpc"] #erpc) ∗
  "#Hcm" ∷ readonly (s ↦[KVShardServer :: "cm"] #cm) ∗
  "#HmuInv" ∷ is_lock memKVN mu (own_KVShardServer s γ) ∗
  "#HercInv" ∷ is_erpc_server γ.(erpc_gn) erpc ∗
  "#Hiscm" ∷ is_ConnMan cm
.

End memkv_shard_definitions.
