From Perennial.program_proof Require Import dist_prelude.
From Goose.github_com.mit_pdos.gokv.urpc Require Import rpc.
From Perennial.goose_lang.lib Require Import slice.typed_slice.

Section rpc_axioms.
Context `{!heapG Σ}.

Axiom handler_is : ∀ (X:Type) (host:u64) (rpcid:u64) (Pre:X → list u8 → iProp Σ)
                     (Post:X → list u8 → list u8 → iProp Σ), iProp Σ.

Axiom handler_is_pers : ∀ X host rpcid pre post, Persistent (handler_is X host rpcid pre post).

Global Instance handler_is_pers_instance X host rpcid pre post : Persistent (handler_is X host rpcid pre post).
apply handler_is_pers.
Defined.

Axiom RPCClient_own : ∀ (cl_ptr:loc) (host:u64), iProp Σ.

Axiom wp_MakeRPCClient : ∀ (host:u64) ,
  {{{
       True
  }}}
    MakeRPCClient #host
  {{{
       (cl_ptr:loc), RET #cl_ptr; RPCClient_own cl_ptr host
  }}}.

Axiom wp_RPCClient__Call : ∀ {X:Type} (x:X) (cl_ptr:loc) (rpcid:u64) (host:u64) req rep_ptr dummy_sl_val (reqData:list u8) Pre Post k,
  {{{
      is_slice req byteT 1 reqData ∗
      rep_ptr ↦[slice.T byteT] dummy_sl_val ∗
      handler_is X host rpcid Pre Post ∗
      RPCClient_own cl_ptr host ∗
      □(▷ Pre x reqData)
  }}}
    RPCClient__Call #cl_ptr #rpcid (slice_val req) #rep_ptr @ k ; ⊤
  {{{
       (b:bool) rep_sl (repData:list u8), RET #b;
       rep_ptr ↦[slice.T byteT] (slice_val rep_sl) ∗
       RPCClient_own cl_ptr host ∗
       typed_slice.is_slice req byteT 1 reqData ∗
       typed_slice.is_slice rep_sl byteT 1 repData ∗
       (⌜b = true⌝ ∨ ⌜b = false⌝ ∗ (▷ Post x reqData repData))
  }}}.

Definition is_rpcHandler {X:Type} (f:val) Pre Post : iProp Σ :=
  ∀ (x:X) req rep dummy_rep_sl (reqData:list u8),
  {{{
      is_slice req byteT 1 reqData ∗
      rep ↦[slice.T byteT] (slice_val dummy_rep_sl) ∗
      ▷ Pre x reqData
  }}}
    f (slice_val req) #rep
  {{{
       rep_sl (repData:list u8), RET #(); rep ↦[slice.T byteT] (slice_val rep_sl) ∗
         is_slice rep_sl byteT 1 repData ∗
         ▷ Post x reqData repData
  }}}.

Axiom own_RPCServer : loc → gmap u64 val → iProp Σ.

Axiom wp_MakeRPCServer : ∀ (handlers : gmap u64 val) (mref:loc) (def : val) k,
  {{{
       map.is_map mref (handlers, def)
  }}}
    MakeRPCServer #mref @ k ; ⊤
  {{{
      (s:loc), RET #s; own_RPCServer s handlers
  }}}.

Axiom wp_StartRPCServer : ∀ host (handlers : gmap u64 val) (s : loc) k (n:u64),
  {{{
       own_RPCServer s handlers ∗
      [∗ map] rpcid ↦ handler ∈ handlers, (∃ X Pre Post, handler_is X host rpcid Pre Post ∗ is_rpcHandler handler Pre Post)
  }}}
    RPCServer__Serve #s #host #n @ k ; ⊤
  {{{
      RET #(); True
  }}}.

End rpc_axioms.
