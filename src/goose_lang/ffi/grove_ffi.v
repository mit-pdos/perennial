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
Axiom RPCClient__RemoteProcedureCall : val.
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

Definition handler_is (host:string) (rpcid:u64) (Pre:list u8 → iProp Σ) (Post:list u8 → list u8 → iProp Σ) : iProp Σ :=
  (host,rpcid) ↪[rpcreg_gname]□ (λ d, Next (Pre d), λ reqData repData, Next (Post reqData repData)).

Axiom wp_RPCClient__RemoteProcedureCall : ∀ (cl_ptr:loc) (rpcid:u64) (host:string) req reply (reqData:list u8) Pre Post k,
  {{{
      is_slice req byteT 1 reqData ∗
      (∃ repData, is_slice reply byteT 1 repData) ∗
      handler_is host rpcid Pre Post ∗
      □(▷ Pre reqData)
  }}}
    (* TODO: should be a pointer to a byte slice for reply *)
    grove_ffi.RPCClient__RemoteProcedureCall #cl_ptr #rpcid (slice_val req) (slice_val reply) @ k ; ⊤
  {{{
       (b:bool) (repData:list u8), RET #b;
       is_slice req byteT 1 reqData ∗
       is_slice reply byteT 1 repData ∗
       ⌜b = true⌝ ∨ ⌜b = false⌝ ∗ (▷ Post reqData repData)
  }}}.

Definition is_rpcHandler (f:val) Pre Post : iProp Σ :=
  ∀ req rep (reqData repData:list u8),
  {{{
      is_slice req byteT 1 reqData ∗
      (∃ repData, is_slice req byteT 1 repData) ∗
      ▷ Pre reqData
  }}}
    f (slice_val req) (slice_val rep)
  {{{
      RET #(); is_slice req byteT 1 repData ∗
                        ▷ Post reqData repData
  }}}.

Axiom wp_StartRPCServer : ∀ host (handlers : gmap u64 val) (mref : loc) (def : val) k,
  {{{
      map.is_map mref (handlers, def) ∗
      [∗ map] rpcid ↦ handler ∈ handlers, (∃ Pre Post, handler_is host rpcid Pre Post ∗ is_rpcHandler handler Pre Post)
  }}}
    grove_ffi.StartRPCServer @ k ; ⊤
  {{{
      RET #(); True
  }}}.

End grove_ffi.

Notation "s f↦{ q } c" := (file_mapsto s c q)
(at level 20, q at level 50, format "s  f↦{ q } c") : bi_scope.

Notation "s f↦ c" := (s f↦{1} c)%I
(at level 20, format "s  f↦ c") : bi_scope.
