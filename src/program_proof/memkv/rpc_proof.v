From Perennial.program_proof Require Import dist_prelude.
From Goose.github_com.mit_pdos.gokv.urpc Require Import rpc.

Class rpcregG (Σ : gFunctors) := RpcRegG {
  rpcreg_map : gmap (u64*u64) { X: Type & ((X → list u8 → iProp Σ) * (X → list u8 → list u8 → iProp Σ))%type };
}.

Section rpc_proof.

Context `{!rpcregG Σ}.

Definition handler_is : ∀ (X:Type) (host:u64) (rpcid:u64) (Pre:X → list u8 → iProp Σ)
                          (Post:X → list u8 → list u8 → iProp Σ), iProp Σ :=
  λ X host rpcid Pre Post, ⌜ rpcreg_map !! (host, rpcid) = Some (existT X (Pre, Post)) ⌝%I.

Global Instance handler_is_pers_instance X host rpcid pre post : Persistent (handler_is X host rpcid pre post).
Proof. apply _. Qed.

Context `{!heapG Σ}.

Definition RPCClient_own (cl_ptr : loc) (host:u64) : iProp Σ := True%I.

Lemma wp_MakeRPCClient (host:u64):
  {{{
       True
  }}}
    MakeRPCClient #host
  {{{
       (cl_ptr:loc), RET #cl_ptr; RPCClient_own cl_ptr host
  }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_lam.

  wp_apply (wp_Connect).
  iIntros (err r) "Hr".
  destruct err.
  { admit. (* TODO FIXME: RPCClient should check this error, or panic *) }
  wp_pures.

  replace (ref (InjLV #null))%E with (NewMap (struct.ptrT callback)) by naive_solver.
  wp_apply (wp_new_free_lock). iIntros (lk) "Hfree".
  wp_pures.
  (* XXX: I think this is going to have to be untyped since callback contains a slice in it *)
  wp_apply (map.wp_NewMap).
  iIntros (mref) "Hmref".

  wp_apply (wp_allocStruct).
  { enough (val_ty (send_endpoint host r) Sender) by naive_solver.
    admit. }
  iIntros (cl) "Hcl".
  iNamed "Hcl".
  iDestruct (struct_fields_split with "Hcl") as "Hcl". iNamed "Hcl".
  wp_pures.
Abort.

End rpc_proof.