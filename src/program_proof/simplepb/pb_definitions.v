From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Export pb.
From Perennial.program_proof.grove_shared Require Import urpc_proof urpc_spec.
From iris.base_logic Require Export lib.ghost_var mono_nat.
From iris.algebra Require Import dfrac_agree mono_list.
From Perennial.goose_lang Require Import crash_borrow.

Section pb_definitions.

Context `{!heapGS Σ, !stagedG Σ}.
Context `{!pbG Σ}.

Definition is_ApplyFn (applyFn:val) γ P : iProp Σ :=
  ∀ op_sl (epoch:u64) σ op,
  {{{
        (own_Server_ghost γ epoch σ ={⊤}=∗ own_Server_ghost γ epoch (σ++[op])) ∗
        crash_borrow (own_Server_ghost γ epoch σ ∗ P epoch σ) (
          ∃ epoch' σ',
          (own_Server_ghost γ epoch' σ' ∗ P epoch' σ')
        )
        ∗ is_slice op_sl byteT 1 op
  }}}
    applyFn (slice_val op_sl)
  {{{
        RET #();
        crash_borrow (own_Server_ghost γ epoch (σ ++ [op]) ∗ P epoch (σ ++ [op])) (
          ∃ epoch' σ',
          (own_Server_ghost γ epoch' σ' ∗ P epoch' σ')
        )
  }}}
.

Definition is_StateMachine (sm:loc) γ P : iProp Σ :=
  ∃ (applyFn:val),
  "#Happly" ∷ readonly (sm ↦[pb.StateMachine :: "Apply"] applyFn) ∗
  "#HapplySpec" ∷ is_ApplyFn applyFn γ P
.

Definition own_Server (s:loc) γ P : iProp Σ :=
  ∃ (epoch:u64) σ (nextIndex:u64) (isPrimary:bool) (sm:loc) (clerks:Slice.t),
  (* physical *)
  "Hepoch" ∷ s ↦[pb.Server :: "epoch"] #epoch ∗
  "HnextIndex" ∷ s ↦[pb.Server :: "nextIndex"] #nextIndex ∗
  "HisPrimary" ∷ s ↦[pb.Server :: "isPrimary"] #isPrimary ∗
  "Hsm" ∷ s ↦[pb.Server :: "sm"] #sm ∗
  "Hclerks" ∷ s ↦[pb.Server :: "clerks"] (slice_val clerks) ∗

  (* state-machine *)
  "#HisSm" ∷ is_StateMachine sm γ P ∗

  (* ghost-state *)
  "Hstate" ∷ crash_borrow (own_Server_ghost γ epoch σ ∗ P epoch σ) (
    ∃ epoch σ,
    own_Server_ghost γ epoch σ ∗ P epoch σ
  ) ∗

  (* primary-only *)
  "#Hclerks_rpc" ∷ True
.

Definition is_Server (s:loc) γ : iProp Σ :=
  ∃ (mu:val) P,
  "#Hmu" ∷ readonly (s ↦[pb.Server :: "mu"] mu) ∗
  "#HmuInv" ∷ is_lock pbN mu (own_Server s γ P).

Record ApplyArgsC :=
{
  epoch : u64 ;
  index : u64 ;
  op : list u8 ;
}.

Definition has_encoding_ApplyArgs (encoded:list u8) (args:ApplyArgsC) : Prop.
Admitted.

Definition has_encoding_Error (encoded:list u8) (error:u64) : Prop.
Admitted.

Program Definition ApplyAsBackup_spec γ :=
  λ (encoded_args:list u8), λne (Φ : list u8 -d> iPropO Σ) ,
  (∃ args σ,
    ⌜has_encoding_ApplyArgs encoded_args args⌝ ∗
    ⌜length σ = int.nat args.(index)⌝ ∗
    ⌜last σ = Some args.(op)⌝ ∗
    is_proposal_lb γ args.(epoch) σ ∗
    (∀ error (reply:list u8),
        ⌜has_encoding_Error reply error⌝ -∗
        (if (decide (error = 0)) then is_accepted_lb γ args.(epoch) σ else True) -∗
        Φ reply)
    )%I
.
Next Obligation.
  solve_proper.
Defined.

Context `{!urpcregG Σ}.

Definition is_pb_host γ (host:chan) :=
  handler_spec γ.(urpc_gn) host (U64 0) (ApplyAsBackup_spec γ).

Definition is_Clerk (ck:loc) γ : iProp Σ :=
  ∃ (cl:loc) srv,
  "#Hcl" ∷ readonly (ck ↦[pb.Clerk :: "cl"] #cl) ∗
  "#Hcl_rpc"  ∷ is_uRPCClient cl srv ∗
  "#Hsrv" ∷ is_pb_host γ srv
.

Lemma wpc_Server__epochFence {stk} (s:loc) γ (currEpoch epoch:u64) :
  {{{
        is_epoch_lb γ epoch ∗
        s ↦[pb.Server :: "epoch"] #currEpoch ∗
        own_epoch γ currEpoch
  }}}
    pb.Server__epochFence #s #epoch @ stk
  {{{
        RET #(bool_decide (int.nat currEpoch > int.nat epoch));
        ⌜int.nat currEpoch ≥ int.nat epoch⌝ ∗
        s ↦[pb.Server :: "epoch"] #currEpoch ∗ own_epoch γ currEpoch
  }}}
  {{{
        own_epoch γ currEpoch
  }}}
.
Proof.
Admitted.

Lemma wp_Server__ApplyAsBackup (s:loc) (args_ptr:loc) γ (epoch index:u64) (op:list u8) op_sl :
  is_Server s γ -∗
  {{{
        "HargEpoch" ∷ args_ptr ↦[pb.ApplyArgs :: "epoch"] #epoch ∗
        "HargIndex" ∷ args_ptr ↦[pb.ApplyArgs :: "index"] #index ∗
        "HargOp" ∷ args_ptr ↦[pb.ApplyArgs :: "op"] (slice_val op_sl) ∗
        "HopSl" ∷ is_slice op_sl byteT 1 op ∗
        "#HepochLb" ∷ is_epoch_lb γ epoch
  }}}
    pb.Server__ApplyAsBackup #s #args_ptr
  {{{
        RET #0; True
  }}}
  .
Proof.
  iIntros "#HisSrv" (Φ) "!# Hpre HΦ".
  iNamed "Hpre".
  iNamed "HisSrv".
  wp_call.
  wp_loadField.
  wp_apply (acquire_spec with "HmuInv").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".
  wp_pures.
  Opaque crash_borrow.
  wp_loadField.
  wp_bind (Server__epochFence _ _).
  iApply (wpc_wp _ _ _ _ True).
  iApply (wpc_crash_borrow_open with "Hstate").
  {
    econstructor.
  }
  iSplitL ""; first done.
  iIntros "[Hghost HP]".
  unfold own_Server_ghost.
  iNamed "Hghost".
  wpc_apply (wpc_Server__epochFence with "[$Hepoch $Hepoch_ghost $HepochLb]").
  iSplit.
  {
    iIntros.
    iSplitL ""; first done.
    iExists _, _; iFrame "∗#".
  }
  iNext.
  iIntros "(%Hineq & Hepoch & $)".
  iFrame "Haccepted Haccepted_rest Hghost Hproposal_lb".
  iFrame "HP".
  iIntros "Hstate".
  iSplitL ""; first done.
  wp_if_destruct.
  { (* return error: stale *)
    admit.
  }
  replace (epoch0) with (epoch) by word.

  wp_loadField.
  wp_loadField.
  wp_if_destruct.
  { (* return errror: out-of-order *)
    admit.
  }

  wp_loadField.
  wp_loadField.
  iNamed "HisSm".
  wp_loadField.

  wp_apply ("HapplySpec" with "[$Hstate $HopSl]").
  { (* prove protocol step *)
    admit.
  }
  iIntros "Hstate".
  wp_pures.
  wp_loadField.
  wp_storeField.
  wp_loadField.
  wp_apply (release_spec with "[$Hlocked $HmuInv HnextIndex HisPrimary Hsm Hclerks Hepoch Hstate]").
  {
    iNext.
    iExists _, _, _, _, _, _.
    iFrame.
    iExists _; iFrame "#".
  }
  wp_pures.
  iApply "HΦ".
  done.
Admitted.

Implicit Type σ : list (list u8).
Implicit Type epoch : u64.

Definition replyFn σ (op:list u8) : (list u8).
Admitted.

Lemma wp_Server__Apply (s:loc) γ op_sl op Q :
  {{{
        is_Server s γ ∗
        is_slice op_sl byteT 1 op ∗
        (|={⊤,∅}=> ∃ σ, own_ghost γ σ ∗ (own_ghost γ (σ ++ [op]) ={∅,⊤}=∗ Q (replyFn σ op)))
  }}}
    pb.Server__Apply #s (slice_val op_sl)
  {{{
        reply_sl σ, RET (slice_val reply_sl);
        is_slice reply_sl byteT 1 (replyFn σ op) ∗
        (Q (replyFn σ op))
  }}}
  .
Proof.
  iIntros (Φ) "[#His Hpre] HΦ".
  iNamed "His".
  wp_call.
  wp_loadField.
  wp_apply (acquire_spec with "HmuInv").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".
  wp_pures.
  wp_loadField.
  wp_if_destruct.
  { (* return error "not primary" *)
    admit.
  }
  wp_loadField.
Admitted.

End pb_definitions.
