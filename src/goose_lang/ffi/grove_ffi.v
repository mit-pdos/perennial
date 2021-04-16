From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang Require Export ffi.disk_prelude.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.goose_lang.lib Require Import slice.typed_slice.
From Perennial.algebra Require Import auth_map.
From iris.base_logic Require Import ghost_map.
Require Import Decimal Ascii String DecimalString.

Axiom Read : val.
Axiom Write : val.
Axiom AtomicAppend : val.
Axiom U64ToString : val.
Axiom GetServer : val.
Axiom AllocServer : val.

Module RPCClient.
  Axiom S : descriptor.
End RPCClient.

Axiom MakeRPCClient : val.
Axiom RPCClient__Call : val.
Axiom StartRPCServer : val.

Section grove_ffi.
Context `{!heapG Σ}.

Class filesysG Σ := FileSysG {
  filesys_gname : gname ; (* Name of str -> []byte authmap used for filesys ffi *)
  filesys_inG :> mapG Σ string (list byte)
}.

Definition file_mapsto {fG:filesysG Σ} (s:string) (c:list byte) (q:Qp): iProp Σ :=
  s [[filesys_gname]]↦{q} c.

Context `{!filesysG Σ}.

Notation "s f↦{ q } c" := (file_mapsto s c q)
(at level 20, q at level 50, format "s  f↦{ q } c") : bi_scope.

Notation "s f↦ c" := (s f↦{1} c)%I
(at level 20, format "s  f↦ c") : bi_scope.

Axiom wpc_Read : ∀ {k} filename (q:Qp) content,
  {{{
      filename f↦{q} content
  }}}
    grove_ffi.Read #(str filename) @ k ; ⊤
  {{{
       s, RET slice_val s; typed_slice.is_slice s byteT 1 content ∗
                           filename f↦{q} content
  }}}
  {{{
      filename f↦{q} content
  }}}.

Axiom wpc_Write : ∀ {k} filename content_old content (content_sl:Slice.t) q,
  {{{
      filename f↦ content_old ∗
      typed_slice.is_slice content_sl byteT q content
  }}}
    grove_ffi.Write #(str filename) (slice_val content_sl) @ k ; ⊤
  {{{
       RET #(); filename f↦ content ∗
      typed_slice.is_slice content_sl byteT q content
  }}}
  {{{
      filename f↦ content_old ∨
      filename f↦ content
  }}}.

Axiom wpc_AtomicAppend : ∀ {k} filename content_old content (content_sl:Slice.t) q,
  {{{
      filename f↦ content_old ∗
      typed_slice.is_slice content_sl byteT q content
  }}}
    grove_ffi.AtomicAppend #(str filename) (slice_val content_sl) @ k ; ⊤
  {{{
       RET #(); filename f↦ (content_old ++ content) ∗
      typed_slice.is_slice content_sl byteT q (content_old ++ content)
  }}}
  {{{
      filename f↦ content_old ∨
      filename f↦ (content_old ++ content)
  }}}.

Definition u64_to_string : u64 -> string := λ u, NilZero.string_of_int (Z.to_int (int.Z u)).

(* Spec for U64ToString will be annoying *)
Axiom wp_U64ToString : ∀ (u:u64),
  {{{
       True
  }}}
    grove_ffi.U64ToString #u
  {{{
       RET #(str u64_to_string u); True
  }}}.

Class rpcregG Σ := RpcRegG {
  rpcreg_gname : gname ;
  rpcreg_inG :> ghost_mapG Σ (string*u64) ((list u8 → laterO (iPropO Σ)) * (list u8 → list u8 → laterO (iPropO Σ)))
}.
(* XXX: these laters probably aren't a problem, because the eventual
   implementation of RPC will possibly have to use invariants to move the Pre to
   the server and the Post to the client. Getting the (not-necessarily
   persistent) Post would involve more escrow....

   If we demand that Post is always persistent, we might be able to get
   away with keeping the Post outside the inv somehow, and not need the later.
   Not going to worry about that for now.
 *)

Context `{!rpcregG Σ}.

Axiom handler_is : ∀ (X:Type) (host:string) (rpcid:u64) (Pre:X → list u8 → iProp Σ)
                     (Post:X → list u8 → list u8 → iProp Σ), iProp Σ.

Axiom handler_is_pers : ∀ X host rpcid pre post, Persistent (handler_is X host rpcid pre post).

Global Instance handler_is_pers_instance X host rpcid pre post : Persistent (handler_is X host rpcid pre post).
apply handler_is_pers.
Defined.

Axiom RPCClient_own : ∀ (cl_ptr:loc) (host:string), iProp Σ.

Axiom wp_MakeRPCClient : ∀ (host:string) ,
  {{{
       True
  }}}
    MakeRPCClient #(str host)
  {{{
       (cl_ptr:loc), RET #cl_ptr; RPCClient_own cl_ptr host
  }}}.


(*
Axiom wp_RPCClient__RemoteProcedureCall : ∀ (cl_ptr:loc) (rpcid:u64) (host:string) req rep_ptr dummy_rep_sl (reqData:list u8) spec,
handler_is host rpcid spec -∗
∀ Φ,
(is_slice req byteT 1 reqData ∗
 rep_ptr ↦[slice.T byteT] (slice_val dummy_rep_sl) ∗
 RPCClient_own cl_ptr host) ∗
 (spec reqData (λ repData, ∃ rep_sl,
       rep_ptr ↦[slice.T byteT] (slice_val rep_sl) ∗
       RPCClient_own cl_ptr host ∗
       is_slice req byteT 1 reqData ∗
       is_slice rep_sl byteT 1 repData -∗
            Φ #())) -∗
  WP grove_ffi.RPCClient__RemoteProcedureCall #cl_ptr #rpcid (slice_val req) #rep_ptr {{ Φ }}
.
*)

Axiom wp_RPCClient__Call : ∀ {X:Type} (x:X) (cl_ptr:loc) (rpcid:u64) (host:string) req rep_ptr dummy_sl_val (reqData:list u8) Pre Post k,
  {{{
      is_slice req byteT 1 reqData ∗
      rep_ptr ↦[slice.T byteT] dummy_sl_val ∗
      handler_is X host rpcid Pre Post ∗
      RPCClient_own cl_ptr host ∗
      □(▷ Pre x reqData)
  }}}
    grove_ffi.RPCClient__Call #cl_ptr #rpcid (slice_val req) #rep_ptr @ k ; ⊤
  {{{
       (b:bool) rep_sl (repData:list u8), RET #b;
       rep_ptr ↦[slice.T byteT] (slice_val rep_sl) ∗
       RPCClient_own cl_ptr host ∗
       is_slice req byteT 1 reqData ∗
       is_slice rep_sl byteT 1 repData ∗
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

Axiom wp_StartRPCServer : ∀ host (handlers : gmap u64 val) (mref : loc) (def : val) k,
  {{{
      map.is_map mref (handlers, def) ∗
      [∗ map] rpcid ↦ handler ∈ handlers, (∃ X Pre Post, handler_is X host rpcid Pre Post ∗ is_rpcHandler handler Pre Post)
  }}}
    grove_ffi.StartRPCServer #mref @ k ; ⊤
  {{{
      RET #(); True
  }}}.

End grove_ffi.

Notation "s f↦{ q } c" := (file_mapsto s c q)
(at level 20, q at level 50, format "s  f↦{ q } c") : bi_scope.

Notation "s f↦ c" := (s f↦{1} c)%I
(at level 20, format "s  f↦ c") : bi_scope.
