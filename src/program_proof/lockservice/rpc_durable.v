From Perennial.Helpers Require Import NamedProps.
From Perennial.Helpers Require Import ModArith.
From Perennial.algebra Require Import auth_map fmcounter.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof.lockservice Require Import fmcounter_map rpc.

Section rpc_durable.
Context `{!heapG Σ}.
Context {A:Type} {R:Type}.
Context `{!rpcG Σ R}.

(** The per-request invariant now has 3 states.
initialized: Request created and "on its way" to the server.
done: The reply was computed as is waiting for the client to take notice.
dead: The client took out ownership of the reply. *)
Local Definition RPCRequest_durable_inv (γrpc:rpc_names) (γPost:gname) (PreCond : A -> iProp Σ) (PostCond : A -> R -> iProp Σ) (req:RPCRequest) : iProp Σ :=
   "#Hlseq_bound" ∷ req.(CID) fm[[γrpc.(cseq)]]> int.nat req.(Seq)
    ∗ ( (* Initialized, but server has not started processing *)
      "Hreply" ∷ (req.(CID), req.(Seq)) [[γrpc.(rc)]]↦ None ∗ PreCond req.(Args) ∨ 

      (* Server has finished processing; two sub-states for wether client has taken PostCond out *)
      req.(CID) fm[[γrpc.(lseq)]]≥ int.nat req.(Seq)
      ∗ (∃ (last_reply:R), (req.(CID), req.(Seq)) [[γrpc.(rc)]]↦ro Some last_reply
        ∗ (own γPost (Excl ()) ∨ PostCond req.(Args) last_reply)
      )
    ).

Definition is_durable_RPCRequest (γrpc:rpc_names) (γPost:gname) (PreCond : A -> iProp Σ) (PostCond : A -> R -> iProp Σ) (req:RPCRequest) : iProp Σ :=
  inv rpcRequestInvN (RPCRequest_durable_inv γrpc γPost PreCond PostCond req).

End rpc_durable.
