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

Lemma server_executes_durable_request (req:@RPCRequest A) reply γrpc γPost PreCond PostCond lastSeqM lastReplyM :
  is_durable_RPCRequest γrpc γPost PreCond PostCond req -∗
  is_RPCServer γrpc -∗
  RPCServer_own γrpc lastSeqM lastReplyM -∗
  (PreCond req.(Args) ==∗ PostCond req.(Args) reply) -∗
  RPCReplyReceipt γrpc req reply ∗
  RPCServer_own γrpc (<[req.(CID):=req.(Seq)]> lastSeqM) (<[req.(CID):=reply]> lastReplyM)
  .
Admitted.

(* Semantic cancellable invariant *)
Definition cinv_sem (N : namespace) (R : iProp Σ) (P : iProp Σ) : iProp Σ :=
  □ ∀ E, ⌜↑N ⊆ E⌝ → (R ={E, E ∖ ↑N }=∗ ▷ P ∗ R ∗ (▷ P ={E ∖ ↑N, E}=∗ True))
.

Lemma rpc_get_cancellable_inv (req:@RPCRequest A) γrpc γPost PreCond PostCond lastSeqM lastReplyM (old_seq:u64) :
  ((map_get lastSeqM req.(CID)).1 = old_seq) →
  (int.Z req.(Seq) > int.Z old_seq)%Z →
  is_durable_RPCRequest γrpc γPost PreCond PostCond req ={⊤}=∗
  cinv_sem rpcRequestInvN (RPCServer_own γrpc lastSeqM lastReplyM) (PreCond req.(Args)).
Proof.
Admitted.

End rpc_durable.
