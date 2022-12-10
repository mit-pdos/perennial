From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv Require Export reconnectclient.
From Perennial.program_proof.grove_shared Require Export urpc_proof urpc_spec.

Section proof.

Context `{!heapGS Σ}.
Context `{!urpcregG Σ}.

Definition is_ReconnectingClient : loc → u64 → iProp Σ.
Admitted.

Global Instance is_ReconnectingClient_pers cl host : Persistent (is_ReconnectingClient cl host).
Admitted.

Lemma wp_ReconnectingClient__Call2 γsmap (cl_ptr:loc) (rpcid:u64) (host:u64) req rep_out_ptr
      (timeout_ms : u64) dummy_sl_val (reqData:list u8) Spec Φ :
  is_ReconnectingClient cl_ptr host -∗
  handler_spec γsmap host rpcid Spec -∗
  is_slice_small req byteT 1 reqData -∗
  rep_out_ptr ↦[slice.T byteT] dummy_sl_val -∗
  □(▷ Spec reqData (λ reply,
       is_slice_small req byteT 1 reqData -∗
        ∀ rep_sl,
          rep_out_ptr ↦[slice.T byteT] (slice_val rep_sl) -∗
          is_slice_small rep_sl byteT 1 reply -∗
          Φ #0)
  ) -∗
  (
   ∀ (err:u64), ⌜err ≠ 0⌝ →
                is_slice_small req byteT 1 reqData -∗
                rep_out_ptr ↦[slice.T byteT] dummy_sl_val -∗ Φ #err
  ) -∗
  WP ReconnectingClient__Call #cl_ptr #rpcid (slice_val req) #rep_out_ptr #timeout_ms {{ Φ }}.
Proof.
Admitted.

Lemma wp_MakeReconnectingClient (srv:u64):
  {{{
       True
  }}}
    MakeReconnectingClient #srv
  {{{
       (cl_ptr:loc), RET #cl_ptr; is_ReconnectingClient cl_ptr srv
  }}}.
Proof.
Admitted.

End proof.
