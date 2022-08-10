From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Export admin.
From Perennial.program_proof.grove_shared Require Import urpc_proof urpc_spec.
From Perennial.goose_lang.lib Require Import waitgroup.
From iris.base_logic Require Export lib.ghost_var mono_nat.
From iris.algebra Require Import dfrac_agree mono_list.
From Perennial.program_proof.simplepb Require Import pb_definitions.

Section admin_proof.

Context {pb_record:PBRecord}.
Notation pbG := (pbG (pb_record:=pb_record)).
Notation OpType := (pb_OpType pb_record).
Notation has_op_encoding := (pb_has_op_encoding pb_record).
Notation has_snap_encoding := (pb_has_snap_encoding pb_record).
Notation has_op_encoding_injective := (pb_has_op_encoding_injective pb_record).
Notation compute_reply := (pb_compute_reply pb_record).

Notation wp_Clerk__GetState := (wp_Clerk__GetState (pb_record:=pb_record)).
Notation wp_Clerk__SetState := (wp_Clerk__SetState (pb_record:=pb_record)).

Context `{!heapGS Σ}.
Context `{!pbG Σ}.
Lemma wp_Reconfig γ (configHost:u64) (servers:list u64) (servers_sl:Slice.t) :
  {{{
        "Hservers_sl" ∷ is_slice servers_sl uint64T 1 servers ∗
        "#Hhost" ∷ ∀ srv, ⌜srv ∈ servers⌝ → (∃ γsrv, is_pb_host γ γsrv srv)
  }}}
    EnterNewConfig #configHost (slice_val servers_sl)
  {{{
        RET #(); True
  }}}.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  wp_call.
Admitted.
