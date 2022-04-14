From Perennial.Helpers Require Import ModArith.
From Goose.github_com.mit_pdos.gokv Require Import erpc.
From Perennial.goose_lang Require Import adequacy.
From Perennial.base_logic Require Import lib.ghost_map lib.mono_nat lib.saved_spec.
From Perennial.program_proof Require Import grove_prelude std_proof marshal_stateless_proof.
From Perennial.program_proof.memkv Require Import urpc_proof urpc_spec erpc_lib.

(** Spec for an eRPC handler.
This is isomorphic to uRPCSpec, but to avoid confusion we use distinct types. *)
Record eRPCSpec {Σ} :=
  { espec_rpcid : u64;
    espec_ty : Type;
    espec_Pre : espec_ty → list u8 → iProp Σ;
    espec_Post : espec_ty → list u8 → list u8 → iProp Σ }.

Section erpc.
Context `{rpcG Σ (list u8), invGS Σ}.

Local Definition encode_request (rid : RPCRequestID) (payload : list u8) :=
  u64_le rid.(Req_CID) ++ u64_le rid.(Req_Seq) ++ payload.

(** [Spec] is the spec of the eRPC handler;
    we compute the spec of the underlying uRPC handler. *)
Definition eRPCSpec_uRPC γrpc (spec : eRPCSpec (Σ:=Σ)) : uRPCSpec :=
 {| spec_rpcid := spec.(espec_rpcid);
    spec_ty := rpc_request_names * RPCRequestID * (list u8) * spec.(espec_ty);
    spec_Pre :=(λ '(γreq, rid, payload, x) req,
                  ⌜req = encode_request rid payload⌝ ∗
                  is_RPCRequest γrpc γreq
                     (spec.(espec_Pre) x req)
                     (spec.(espec_Post) x req)
                     rid
             )%I;
    spec_Post :=(λ '(γreq, rid, payload, x) req rep,
                (RPCRequestStale γrpc rid ∨
                 RPCReplyReceipt γrpc rid rep)
             )%I
 |}.

(** Convenience function to say that a given rpcid has such a handler *)
Definition handler_erpc_spec`{!urpcregG Σ, !gooseGlobalGS Σ} Γsrv γrpc (host:u64) (spec : eRPCSpec) :=
  handler_urpc_spec Γsrv host (eRPCSpec_uRPC γrpc spec).

End erpc.
