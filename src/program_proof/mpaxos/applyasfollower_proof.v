From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv Require mpaxos.
From Perennial.program_proof.grove_shared Require Import urpc_proof urpc_spec.
From Perennial.goose_lang.lib Require Import waitgroup.
From iris.base_logic Require Export lib.ghost_var mono_nat.
From iris.algebra Require Import dfrac_agree mono_list.
From Perennial.goose_lang Require Import crash_borrow.
From Perennial.program_proof Require Import marshal_stateless_proof.
From Perennial.program_proof.mpaxos Require Export definitions.

Section applyasfollower_proof.

Context `{!heapGS Σ}.
Context {mp_record:MPRecord}.
Notation OpType := (mp_OpType mp_record).
Notation has_op_encoding := (mp_has_op_encoding mp_record).
Notation next_state := (mp_next_state mp_record).
Notation compute_reply := (mp_compute_reply mp_record).
Notation is_Server := (is_Server (mp_record:=mp_record)).
Notation applyAsFollower_core_spec := (applyAsFollower_core_spec).
Notation is_singleClerk := (is_singleClerk (mp_record:=mp_record)).

Context (conf:list mp_server_names).
Context `{!mpG Σ}.

Lemma wp_singleClerk__applyAsFollower ck γ γsrv σ Q args_ptr args reply_ptr init_reply :
  {{{
        "#His_ck" ∷ is_singleClerk conf ck γ γsrv ∗
        "Hargs" ∷ applyAsFollowerArgs.own args_ptr args ∗
        "Hreply" ∷ applyAsFollowerReply.own reply_ptr init_reply 1 ∗

        "%Hσ_index" ∷ ⌜length σ = (int.nat args.(applyAsFollowerArgs.nextIndex) + 1)%nat⌝ ∗
        "%Hghost_op_σ" ∷ ⌜last σ = Some (args.(applyAsFollowerArgs.state), Q)⌝ ∗
        "%Hno_overflow" ∷ ⌜int.nat args.(applyAsFollowerArgs.nextIndex) < int.nat (word.add args.(applyAsFollowerArgs.nextIndex) 1)⌝ ∗
        "#Hprop_lb" ∷ is_proposal_lb γ args.(applyAsFollowerArgs.epoch) σ ∗
        "#Hprop_facts" ∷ is_proposal_facts conf γ args.(applyAsFollowerArgs.epoch) σ
  }}}
    singleClerk__applyAsFollower #ck #args_ptr #reply_ptr
  {{{
        reply, RET #(); applyAsFollowerReply.own reply_ptr reply 1 ∗
                                                 □if (decide (reply.(applyAsFollowerReply.err) = (U64 0))) then
                                                   is_accepted_lb γsrv args.(applyAsFollowerArgs.epoch) σ
                                                 else
                                                   True
  }}}.
Proof.
Admitted.

Lemma wp_Server__applyAsFollower (s:loc) (args_ptr reply_ptr:loc) γ γsrv args init_reply σ Q Φ Ψ :
  is_Server conf s γ γsrv -∗
  applyAsFollowerArgs.own args_ptr args -∗
  applyAsFollowerReply.own reply_ptr init_reply 1 -∗
  (∀ reply, Ψ reply -∗ applyAsFollowerReply.own reply_ptr reply 1 -∗ Φ #()) -∗
  applyAsFollower_core_spec conf γ γsrv args σ Q Ψ -∗
  WP mpaxos.Server__applyAsFollower #s #args_ptr #reply_ptr {{ Φ }}
.
Proof.
  iIntros "#HisSrv Hpre Hreply HΦ HΨ".
  iNamed "Hpre".
  iNamed "HisSrv".
  wp_call.
  wp_loadField.
  wp_apply (acquire_spec with "HmuInv").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".
  wp_pures.
  wp_loadField.
  wp_loadField.
  wp_pures.
  wp_if_destruct.
  { (* case: s.epoch ≤ args.epoch *)
    wp_loadField.
    wp_loadField.
    wp_pures.
    wp_if_destruct.
    { (* case: s.acceptedEpoch = args.epoch *)
      wp_loadField.
      wp_loadField.
      wp_if_destruct.
      { (* case: s.nextIndex == len(s.log) ≤ args.nextIndex *)
        wp_loadField.
        wp_storeField.
        wp_loadField.
        wp_storeField.
        wp_storeField.
        wp_loadField.
        admit. (* TODO: use protocol lemma *)
      }
      { (* case: args.nextIndex < s.nextIndex len(s.log) *)
        assert (int.Z (length st.(mp_log)) > int.Z args.(applyAsFollowerArgs.nextIndex))%Z as Hineq.
        { word. }
        wp_storeField.
        wp_loadField.
        admit. (* TODO: use protocol lemma *)
      }
    }
    { (* case acceptedEpoch ≠ args.epoch, which implies
         acceptedEpoch < args.epoch
       *)
      wp_loadField.
      wp_storeField.
      wp_loadField.
      wp_storeField.
      wp_loadField.
      wp_storeField.
      wp_storeField.
      wp_loadField.
      admit. (* TODO: use protocol lemma *)
    }
  }
  { (* case: s.epoch > args.epoch *)
    wp_storeField.
    wp_loadField.
    wp_apply (release_spec with "[-HΦ HΨ Hreply]").
    {
      iFrame "HmuInv Hlocked".
      iNext.
      iExists _, _, _, _, _, _.
      iFrame "∗#%".
    }
    wp_pures.
    iNamed "HΨ".
    iRight in "HΨ".
    iModIntro.
    iApply ("HΦ" with "[HΨ]").
    2:{
      instantiate (1:=applyAsFollowerReply.mkC _).
      iFrame.
    }
    {
      iApply "HΨ".
      done.
    }
  }
Admitted.

End applyasfollower_proof.
