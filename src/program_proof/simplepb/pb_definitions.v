From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Export pb.
From Perennial.program_proof.grove_shared Require Import urpc_proof urpc_spec.
From Perennial.program_proof.simplepb Require Import pb_ghost.
From Perennial.goose_lang.lib Require Import waitgroup.
From iris.base_logic Require Export lib.ghost_var mono_nat.
From iris.algebra Require Import dfrac_agree mono_list.
From Perennial.goose_lang Require Import crash_borrow.

Section pb_definitions.

Context `{!heapGS Σ, !stagedG Σ}.
Context `{!pbG (EntryType:=((list u8) * (iProp Σ))%type ) Σ}.

(* Client/RPC spec definitions *)

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

Program Definition ApplyAsBackup_spec γ γsrv :=
  λ (encoded_args:list u8), λne (Φ : list u8 -d> iPropO Σ) ,
  (∃ args σ Q,
    ⌜has_encoding_ApplyArgs encoded_args args⌝ ∗
    ⌜length σ = int.nat args.(index)⌝ ∗
    ⌜last σ = Some (args.(op), Q) ⌝ ∗
    is_proposal_lb γ args.(epoch) σ ∗
    (∀ error (reply:list u8),
        ⌜has_encoding_Error reply error⌝ -∗
        (if (decide (error = 0)) then is_accepted_lb γsrv args.(epoch) σ else True) -∗
        Φ reply)
    )%I
.
Next Obligation.
  solve_proper.
Defined.

Context `{!urpcregG Σ}.

Definition is_pb_host γ γsrv (host:chan) :=
  handler_spec γsrv.(urpc_gn) host (U64 0) (ApplyAsBackup_spec γ γsrv).

Definition is_Clerk (ck:loc) γ γsrv : iProp Σ :=
  ∃ (cl:loc) srv,
  "#Hcl" ∷ readonly (ck ↦[pb.Clerk :: "cl"] #cl) ∗
  "#Hcl_rpc"  ∷ is_uRPCClient cl srv ∗
  "#Hsrv" ∷ is_pb_host γ γsrv srv
.

(* Server-side definitions *)

Definition is_ApplyFn (applyFn:val) γ γsrv P : iProp Σ :=
  ∀ op_sl (epoch:u64) σ entry Q,
  {{{
        (own_Server_ghost γ γsrv epoch σ ={⊤}=∗ own_Server_ghost γ γsrv epoch (σ++[entry]) ∗ Q) ∗
        crash_borrow (own_Server_ghost γ γsrv epoch σ ∗ P epoch σ) (
          ∃ epoch' σ', (own_Server_ghost γ γsrv epoch' σ' ∗ P epoch' σ')
        )
        ∗ is_slice op_sl byteT 1 entry.1
  }}}
    applyFn (slice_val op_sl)
  {{{
        RET #();
        crash_borrow (own_Server_ghost γ γsrv epoch (σ ++ [entry]) ∗ P epoch (σ ++ [entry])) (
          ∃ epoch' σ',
          (own_Server_ghost γ γsrv epoch' σ' ∗ P epoch' σ')
        ) ∗
        Q
  }}}
.

Definition is_StateMachine (sm:loc) γ γsrv P : iProp Σ :=
  ∃ (applyFn:val),
  "#Happly" ∷ readonly (sm ↦[pb.StateMachine :: "Apply"] applyFn) ∗
  "#HapplySpec" ∷ is_ApplyFn applyFn γ γsrv P
.

Definition own_Server (s:loc) γ γsrv P : iProp Σ :=
  ∃ (epoch:u64) σ (nextIndex:u64) (isPrimary:bool) (sm:loc) (clerks:Slice.t),
  (* physical *)
  "Hepoch" ∷ s ↦[pb.Server :: "epoch"] #epoch ∗
  "HnextIndex" ∷ s ↦[pb.Server :: "nextIndex"] #nextIndex ∗
  "HisPrimary" ∷ s ↦[pb.Server :: "isPrimary"] #isPrimary ∗
  "Hsm" ∷ s ↦[pb.Server :: "sm"] #sm ∗
  "Hclerks" ∷ s ↦[pb.Server :: "clerks"] (slice_val clerks) ∗

  (* state-machine *)
  "#HisSm" ∷ is_StateMachine sm γ γsrv P ∗

  (* ghost-state *)
  "Hstate" ∷ crash_borrow (own_Server_ghost γ γsrv epoch σ ∗ P epoch σ) (
    ∃ epoch σ, own_Server_ghost γ γsrv epoch σ ∗ P epoch σ
  ) ∗
  "%Hσ_nextIndex" ∷ ⌜length σ = int.nat nextIndex⌝ ∗

  (* primary-only *)
  "HprimaryOnly" ∷ if isPrimary then (
            "#Hclerks_rpc" ∷ True ∗
            "Hproposal" ∷ own_proposal γ epoch σ ∗
            "#Hprop_facts" ∷ is_proposal_facts γ epoch σ
        )
                   else True
.

Definition is_Server (s:loc) γ γsrv : iProp Σ :=
  ∃ (mu:val) P,
  "#Hmu" ∷ readonly (s ↦[pb.Server :: "mu"] mu) ∗
  "#HmuInv" ∷ is_lock pbN mu (own_Server s γ γsrv P).

Lemma wpc_Server__epochFence {stk} (s:loc) γ (currEpoch epoch:u64) :
  {{{
        is_epoch_lb γ epoch ∗
        s ↦[pb.Server :: "epoch"] #currEpoch ∗
        own_epoch γ currEpoch
  }}}
    pb.Server__epochFence #s #epoch @ stk
  {{{
        RET #(bool_decide (int.Z epoch < int.Z currEpoch));
        ⌜int.nat currEpoch ≥ int.nat epoch⌝ ∗
        s ↦[pb.Server :: "epoch"] #currEpoch ∗ own_epoch γ currEpoch
  }}}
  {{{
        own_epoch γ currEpoch
  }}}
.
Proof.
  iIntros (Φ Φc) "(#Hlb & HcurrEpoch & Hepoch) HΦ".
  wpc_call.
  { iFrame. }
  { iFrame. }
  iCache with "Hepoch HΦ".
  { iLeft in "HΦ". iApply "HΦ". iFrame. }

  wpc_pures.
  wpc_loadField.
  wpc_pures.
  iDestruct (mono_nat_lb_own_valid with "Hepoch Hlb") as %[_ Hineq].

  destruct (bool_decide (int.Z currEpoch < int.Z epoch)%Z) as [] eqn:Hineq2.
  {
    apply bool_decide_eq_true in Hineq2.
    exfalso.
    word.
  }
  wpc_pures.
  wpc_loadField.
  wpc_pures.
  iRight in "HΦ".
  iModIntro.
  iApply ("HΦ").
  iFrame "∗%".
Qed.

Lemma wp_Server__ApplyAsBackup (s:loc) (args_ptr:loc) γ γsrv (epoch index:u64) σ ghost_op (op:list u8) op_sl :
  is_Server s γ γsrv -∗
  {{{
        "#HepochLb" ∷ is_epoch_lb γsrv epoch ∗
        "#Hprop_lb" ∷ is_proposal_lb γ epoch σ ∗
        "#Hprop_facts" ∷ is_proposal_facts γ epoch σ ∗
        "%Hghost_op_σ" ∷ ⌜last σ = Some ghost_op⌝ ∗
        "%Hghost_op_op" ∷ ⌜ghost_op.1 = op⌝ ∗
        "%Hσ_index" ∷ ⌜length σ = ((int.nat index) + 1)%nat⌝ ∗
        "%HnoOverflow" ∷ ⌜int.nat index < int.nat (word.add index 1)⌝ ∗

        "HargEpoch" ∷ args_ptr ↦[pb.ApplyArgs :: "epoch"] #epoch ∗
        "HargIndex" ∷ args_ptr ↦[pb.ApplyArgs :: "index"] #index ∗
        "HargOp" ∷ args_ptr ↦[pb.ApplyArgs :: "op"] (slice_val op_sl) ∗
        "HopSl" ∷ is_slice op_sl byteT 1 op
  }}}
    pb.Server__ApplyAsBackup #s #args_ptr
  {{{
        (err:u64), RET #err;
        if (decide (err = 0)) then
          is_accepted_lb γsrv epoch σ
        else
          True
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
  iFrame "Haccepted Haccepted_rest HP Hproposal_lb Hvalid".
  iIntros "Hstate".
  iSplitL ""; first done.
  wp_if_destruct.
  { (* return error: stale *)
    wp_loadField.
    wp_apply (release_spec with "[$Hlocked $HmuInv HnextIndex HisPrimary Hsm Hclerks Hepoch Hstate HprimaryOnly]").
    {
      iNext.
      iExists _, _, _, _, _, _.
      iFrame "∗#%".
    }
    wp_pures.
    iApply "HΦ".
    done.
  }
  replace (epoch0) with (epoch) by word.

  assert (isPrimary = false) as HnotPrimary by admit.
  wp_loadField.
  wp_loadField.
  wp_pures.
  destruct (bool_decide (_)) as [] eqn:Hindex; last first.
  { (* return errror: out-of-order *)
    wp_pures.
    wp_loadField.
    wp_apply (release_spec with "[$Hlocked $HmuInv HnextIndex HisPrimary Hsm Hclerks Hepoch Hstate HprimaryOnly]").
    {
      iNext.
      iExists _, _, _, _, _, _.
      iFrame "∗#%".
    }
    wp_pures.
    iApply "HΦ".
    done.
  }

  wp_pures.
  apply bool_decide_eq_true in Hindex.

  wp_loadField.
  wp_loadField.
  iNamed "HisSm".
  wp_loadField.

  wp_apply ("HapplySpec" with "[$Hstate HopSl]").
  { (* prove protocol step *)
    instantiate (1:=ghost_op).
    simpl.
    rewrite Hghost_op_op.
    iFrame "HopSl".
    iIntros "Hghost".
    assert (index = nextIndex) by naive_solver.
    iDestruct (ghost_accept_helper with "Hprop_lb Hghost") as "[Hghost %Happend]".
    { rewrite H in Hσ_index. word. }
    { done. }
    iMod (ghost_accept with "Hghost Hprop_lb Hprop_facts") as "HH".
    { done. }
    {
      rewrite H in Hσ_index.
      word.
    }
    rewrite Happend.
    iDestruct (ghost_get_accepted_lb with "HH") as "#Hlb".
    iFrame "HH".
    iModIntro.
    instantiate (1:=is_accepted_lb γsrv epoch σ).
    done.
  }
  iIntros "[Hstate #Hlb]".
  wp_pures.
  wp_loadField.
  wp_storeField.
  wp_loadField.
  wp_apply (release_spec with "[$Hlocked $HmuInv HnextIndex HisPrimary Hsm Hclerks Hepoch Hstate HprimaryOnly]").
  {
    iNext.
    iExists _, _, _, _, _, _.
    rewrite HnotPrimary.
    iFrame "Hstate ∗#".
    iSplitL "".
    { iExists _; iFrame "#". }
    iSplitL ""; last done.
    iPureIntro.
    rewrite app_length.
    rewrite Hσ_nextIndex.
    simpl.
    replace (nextIndex) with (index) by naive_solver.
    word.
  }
  wp_pures.
  iApply "HΦ".
  iFrame "Hlb".
  done.
Admitted.

Definition replyFn (σ:list (list u8))  (op:list u8) : (list u8).
Admitted.

Lemma wp_Server__Apply (s:loc) γ γsrv op_sl op ghost_op Q :
  {{{
        is_Server s γ γsrv ∗
        is_slice op_sl byteT 1 op ∗
        ⌜ghost_op.1 = op⌝ ∗
        (* FIXME: maybe have a layer below this for the Qs *)
        (|={⊤∖↑pbN,∅}=> ∃ σ, own_ghost γ σ ∗ (own_ghost γ (σ ++ [ghost_op]) ={∅,⊤∖↑pbN}=∗ Q (replyFn (map (λ x, x.1) σ) op)))
  }}}
    pb.Server__Apply #s (slice_val op_sl)
  {{{
        (err:u64) reply_sl σphys, RET (#err, slice_val reply_sl);
        if (decide (err = 0)) then
            is_slice reply_sl byteT 1 (replyFn σphys op) ∗
            (Q (replyFn σphys op))
        else
          True
  }}}
  .
Proof.
  iIntros (Φ) "[#His Hpre] HΦ".
  iDestruct "Hpre" as "(Hsl & %Hghostop_op & Hupd)".
  iNamed "His".
  wp_call.
  wp_loadField.
  wp_apply (acquire_spec with "HmuInv").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".
  wp_pure1_credit "Hcred".
  wp_pures.
  wp_loadField.
  wp_if_destruct.
  { (* return error "not primary" *)
    admit.
  }
  wp_loadField.
  iNamed "HisSm".

  (* make proposal *)
  iNamed "HprimaryOnly".
  iMod (ghost_propose with "Hproposal Hprop_facts Hcred [Hupd]") as "[Hprop #Hprop_facts2]".
  {
    iMod "Hupd".
    iModIntro.
    iDestruct "Hupd" as (?) "[Hghost Hupd]".
    iExists _; iFrame "Hghost".
    iIntros (->) "Hghost".
    iSpecialize ("Hupd" with "Hghost").
    iMod "Hupd".
    done.
  }

  iDestruct (ghost_get_propose_lb with "Hprop") as "#Hprop_lb".

  wp_loadField.

  wp_apply ("HapplySpec" with "[$Hstate $Hsl]").
  {
    iIntros "Hghost".
    iDestruct (ghost_accept_helper with "Hprop_lb Hghost") as "[Hghost %Happend]".
    { apply app_length. }
    { apply last_snoc. }
    iMod (ghost_accept with "Hghost Hprop_lb Hprop_facts2") as "HH".
    { done. }
    { rewrite app_length. word. }
    iFrame "HH".
    instantiate (1:=True%I).
    done.
  }
  iIntros "[Hstate _]".

  wp_pures.
  wp_loadField.
  wp_pures.
  wp_loadField.
  wp_storeField.
  wp_loadField.
  wp_pures.
  wp_loadField.
  wp_pures.

  wp_loadField.
  wp_apply (release_spec with "[$Hlocked $HmuInv HnextIndex HisPrimary Hsm Hclerks Hepoch Hstate Hprop]").
  {
    iNext.
    iExists _, _, _, _, _, _.
    iFrame "Hstate ∗#".
    iSplitL "".
    { iExists _; iFrame "#". }
    iFrame "Hprop".
    iPureIntro.
    (* FIXME: add no overflow assumption *)
    admit.
  }

  wp_pures.
  wp_apply (wp_NewWaitGroup).
  iIntros (wg γwg) "Hwg".
  wp_pures.
  wp_apply (wp_slice_len).
  wp_apply (wp_new_slice).
  { done. }
  iIntros (errs_sl) "Herrs_sl".
  wp_pures.
  wp_apply (wp_allocStruct).
  { econstructor; eauto. }
  iIntros (Hargs) "Hargs".
  iDestruct (struct_fields_split with "Hargs") as "HH".
  iNamed "HH".
  wp_pures.
  wp_apply (wp_forSlice (λ j, own_WaitGroup pbN wg γwg j (λ _, True%I)) with "[] [Hwg]").
  {
    iIntros (i ck).
    clear Φ.
    iIntros (Φ) "!# (Hwg & %Hi_ineq & Hlookup) HΦ".
    wp_pures.
    wp_apply (wp_WaitGroup__Add with "[$Hwg]").
    { word. }
    iIntros "[Hwg HwgTok]".
    wp_pures.
    (* use wgTok to set errs_sl *)
    admit.
  }
  {
    admit.
  }
  iIntros "[Hwg Hclerks_sl]".
  wp_pures.
Admitted.

End pb_definitions.
