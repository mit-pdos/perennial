From Perennial.Helpers Require Import ModArith.
From Goose.github_com.mit_pdos.gokv Require Import connman.
From Perennial.program_proof Require Import grove_prelude std_proof.
From Perennial.program_proof Require Import marshal_proof.
From Perennial.algebra Require Import auth_map.
From Perennial.program_proof.memkv Require Import rpc_proof.
From Perennial.goose_lang.lib Require Import slice.typed_slice.

Section connman_proof.

Context `{!rpcregG Σ}.
Context `{hG: !heapGS Σ}.
Definition connmanN := nroot .@ "connman".
Definition own_ConnMan (c_ptr:loc) : iProp Σ :=
  ∃ (mref:loc) (rpcClsV:gmap u64 val) (rpcClsM:gmap u64 loc),
    "HrpcCls" ∷ c_ptr ↦[ConnMan :: "rpcCls"] #mref ∗
    "Hcls_map" ∷ map.is_map mref 1 (rpcClsV, zero_val (struct.ptrT rpc.RPCClient)) ∗
    "#HownRpcCls" ∷ [∗ map] host ↦ cl;v ∈ rpcClsM;rpcClsV, RPCClient_own cl host ∗ ⌜v = #cl⌝
.

Definition is_ConnMan (c_ptr:loc) : iProp Σ :=
  ∃ mu,
  "#Hmu" ∷ readonly (c_ptr ↦[ConnMan :: "mu"] mu) ∗
  "#Hinv" ∷ is_lock connmanN mu (own_ConnMan c_ptr)
.

Lemma wp_ConnMan__Call {X:Type} (x:X) γsmap (c_ptr:loc) (rpcid:u64) (host:u64) req rep_out_ptr
      (timeout_ms : u64) dummy_sl_val (reqData:list u8) Pre Post :
  is_ConnMan c_ptr -∗
  {{{
      is_slice req byteT 1 reqData ∗
      rep_out_ptr ↦[slice.T byteT] dummy_sl_val ∗
      handler_is γsmap X host rpcid Pre Post ∗
      □(▷ Pre x reqData)
  }}}
      ConnMan__CallAtLeastOnce #c_ptr #host #rpcid (slice_val req) #rep_out_ptr #timeout_ms
    {{{
      RET #();
      is_slice req byteT 1 reqData ∗
      ∃ rep_sl (repData:list u8),
        rep_out_ptr ↦[slice.T byteT] (slice_val rep_sl) ∗
        typed_slice.is_slice rep_sl byteT 1 repData ∗
        (▷ Post x reqData repData)
    }}}
    .
Proof.
  iIntros "#Hconn !#" (Φ) "Hpre HΦ".
  iNamed "Hconn".
  Opaque rpc.RPCClient.
  Opaque zero_val.
  wp_lam.
  wp_pures.
  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (cl_ptr) "Hcl_ptr".
  wp_pures.
  wp_loadField.
  wp_apply (acquire_spec with "Hinv").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".
  wp_pures.
  wp_loadField.
  wp_apply (map.wp_MapGet with "Hcls_map").
  iIntros (cl1 ok1) "[%Hcl1 Hcls_map]".
  wp_pures.
  Search "wp_if".
  wp_apply (wp_If_join (∃ (cl:loc), "Hown" ∷ own_ConnMan c_ptr ∗
                        "Hcl" ∷ cl_ptr ↦[refT (struct.t rpc.RPCClient)] #cl ∗
                        "#HisRpcCl" ∷ RPCClient_own cl host ∗
                        "Hlocked" ∷ locked mu
                       ) with "[-Hpre HΦ]"); first iSplit.
  { (* *)
    iIntros "HΦ".
    (* TODO: apply spec for getNewClient *)
    admit.
  }
  {
    iIntros "[%Hnegb HΦ]".

    destruct ok1 as [|] eqn:Hok; last first.
    { exfalso. done. }
    apply map.map_get_true in Hcl1.
    iDestruct (big_sepM2_lookup_r with "HownRpcCls") as "HH".
    { done. }
    iDestruct "HH" as (cl) "[%Hcl [#HrpcCl %HclVal]]".

    wp_apply (wp_StoreAt with "Hcl_ptr").
    { naive_solver. }
    iIntros "Hcl_ptr".
    iApply "HΦ".

    iExists cl.
    rewrite HclVal.
    iFrame "Hcl_ptr Hlocked #".
    iExists _,_,_.
    iFrame "∗#".
  }
  iNamed 1.
  wp_pures.
  wp_loadField.
  wp_apply (release_spec with "[$Hinv $Hlocked $Hown]").
  wp_pures.
Admitted.

End connman_proof.
