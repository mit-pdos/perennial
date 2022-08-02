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
    is_proposal_facts γ args.(epoch) σ ∗
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

Lemma wp_Clerk__Apply γ γsrv ck args_ptr (epoch index:u64) σ ghost_op op_sl op :
  {{{
        "#HisClerk" ∷ is_Clerk ck γ γsrv ∗
        "#HepochLb" ∷ is_epoch_lb γsrv epoch ∗
        "#Hprop_lb" ∷ is_proposal_lb γ epoch σ ∗
        "#Hprop_facts" ∷ is_proposal_facts γ epoch σ ∗
        "%Hghost_op_σ" ∷ ⌜last σ = Some ghost_op⌝ ∗
        "%Hghost_op_op" ∷ ⌜ghost_op.1 = op⌝ ∗
        "%Hσ_index" ∷ ⌜length σ = ((int.nat index) + 1)%nat⌝ ∗
        "%HnoOverflow" ∷ ⌜int.nat index < int.nat (word.add index 1)⌝ ∗

        "#HargEpoch" ∷ readonly (args_ptr ↦[pb.ApplyArgs :: "epoch"] #epoch) ∗
        "#HargIndex" ∷ readonly (args_ptr ↦[pb.ApplyArgs :: "index"] #index) ∗
        "#HargOp" ∷ readonly (args_ptr ↦[pb.ApplyArgs :: "op"] (slice_val op_sl)) ∗
        "#HopSl" ∷ readonly (is_slice_small op_sl byteT 1 op)
  }}}
    Clerk__Apply #ck #args_ptr
  {{{
        (err:u64), RET #err; □ if (decide (err = 0)) then
                               is_accepted_lb γsrv epoch σ
                             else True
  }}}.
Proof.
Admitted.
(* How to show `if decide (err = 0) then
   SomethingPersistent else SomethingElsePersistent` is persistent? *)

(* Server-side definitions *)

Definition is_ApplyFn (applyFn:val) γ γsrv P : iProp Σ :=
  ∀ op_sl (epoch:u64) σ entry Q,
  {{{
        (own_Server_ghost γ γsrv epoch σ ={⊤}=∗ own_Server_ghost γ γsrv epoch (σ++[entry]) ∗ Q) ∗
        crash_borrow (own_Server_ghost γ γsrv epoch σ ∗ P epoch σ) (
          ∃ epoch' σ', (own_Server_ghost γ γsrv epoch' σ' ∗ P epoch' σ')
        )
        ∗
        readonly (is_slice_small op_sl byteT 1 entry.1)
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
  ∃ (epoch:u64) σ (nextIndex:u64) (isPrimary:bool) (sm:loc) (clerks_sl:Slice.t),
  (* physical *)
  "Hepoch" ∷ s ↦[pb.Server :: "epoch"] #epoch ∗
  "HnextIndex" ∷ s ↦[pb.Server :: "nextIndex"] #nextIndex ∗
  "HisPrimary" ∷ s ↦[pb.Server :: "isPrimary"] #isPrimary ∗
  "Hsm" ∷ s ↦[pb.Server :: "sm"] #sm ∗
  "Hclerks" ∷ s ↦[pb.Server :: "clerks"] (slice_val clerks_sl) ∗

  (* state-machine *)
  "#HisSm" ∷ is_StateMachine sm γ γsrv P ∗

  (* ghost-state *)
  "Hstate" ∷ crash_borrow (own_Server_ghost γ γsrv epoch σ ∗ P epoch σ) (
    ∃ epoch σ, own_Server_ghost γ γsrv epoch σ ∗ P epoch σ
  ) ∗
  "%Hσ_nextIndex" ∷ ⌜length σ = int.nat nextIndex⌝ ∗

  (* primary-only *)
  "HprimaryOnly" ∷ if isPrimary then (
            ∃ (clerks:list loc) (backups:list pb_server_names),
            "#Hconf" ∷ is_epoch_config γ epoch (γsrv :: backups) ∗
                     (* FIXME: ptrT vs refT (struct.t Clerk) *)
            "#Hclerks_sl" ∷ readonly (is_slice_small clerks_sl ptrT 1 clerks) ∗
            "#Hclerks_rpc" ∷ ([∗ list] ck ; γsrv' ∈ clerks ; backups, is_Clerk ck γ γsrv' ∗
                                                                      is_epoch_lb γsrv' epoch
                             ) ∗
            "#Hprop_facts" ∷ is_proposal_facts γ epoch σ ∗
            "Hproposal" ∷ own_proposal γ epoch σ
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

Opaque crash_borrow.
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
        readonly (is_slice_small op_sl byteT 1 op) ∗
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
  iDestruct "Hpre" as "(#Hsl & %Hghostop_op & Hupd)".
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
  wp_apply (release_spec with "[$Hlocked $HmuInv HnextIndex HisPrimary Hsm Hclerks Hepoch Hstate Hprop Hclerks_sl]").
  {
    iNext.
    iExists _, _, _, _, _, _.
    iFrame "Hstate ∗#".
    iSplitL "".
    { iExists _; iFrame "#". }
    iSplitL "".
    {
      iPureIntro.
      (* FIXME: add no overflow assumption *)
      admit.
    }
    iExists _, _; iFrame "∗#".
  }

  wp_pures.
  wp_apply (wp_NewWaitGroup_free).
  iIntros (wg) "Hwg".
  wp_pures.
  wp_apply (wp_slice_len).
  wp_apply (wp_new_slice).
  { done. }
  iIntros (errs_sl) "Herrs_sl".
  wp_pures.
  iApply fupd_wp.
  iMod (fupd_mask_subseteq (↑pbN)) as "Hmask".
  { set_solver. }
  iMod (free_WaitGroup_alloc pbN _
                             (λ i,
                               ∃ (err:u64) γsrv',
                               ⌜backups !! int.nat i = Some γsrv'⌝ ∗
                               readonly ((errs_sl.(Slice.ptr) +ₗ[uint64T] int.Z i)↦[uint64T] #err) ∗
                               if (decide (err = 0)) then
                                 is_accepted_lb γsrv' epoch0 (σ ++ [ghost_op])
                               else
                                 True
                             )%I
         with "Hwg") as (γwg) "Hwg".
  iMod "Hmask".
  iModIntro.

  wp_apply (wp_allocStruct).
  { econstructor; eauto. }
  iIntros (Hargs) "Hargs".
  iDestruct (struct_fields_split with "Hargs") as "HH".
  iNamed "HH".
  iMod (readonly_alloc_1 with "epoch") as "#Hargs_epoch".
  iMod (readonly_alloc_1 with "index") as "#Hargs_index".
  iMod (readonly_alloc_1 with "op") as "#Hargs_op".
  wp_pures.
  iMod (readonly_load with "Hclerks_sl") as (?) "Hclerks_sl2".
  wp_apply (wp_forSlice (λ j, (own_WaitGroup pbN wg γwg j _) ∗
                              (errs_sl.(Slice.ptr) +ₗ[uint64T] int.Z j)↦∗[uint64T] (replicate (int.nat clerks_sl.(Slice.sz) - int.nat j) #0)
                        )%I with "[] [Hwg Herrs_sl $Hclerks_sl2]").
  2: {
    iSplitR "Herrs_sl".
    { iExactEq "Hwg". econstructor. }
    {
      unfold slice.is_slice. unfold slice.is_slice_small.
      iDestruct "Herrs_sl" as "[[Herrs_sl %Hlen] _]".
      destruct Hlen as [Hlen _].
      rewrite replicate_length in Hlen.
      rewrite Hlen.
      iExactEq "Herrs_sl".
      simpl.
      replace (1 * int.Z _)%Z with (0%Z) by word.
      rewrite loc_add_0.
      replace (int.nat _ - int.nat 0) with (int.nat errs_sl.(Slice.sz)) by word.
      done.
    }
  }
  {
    iIntros (i ck).
    clear Φ.
    iIntros (Φ) "!# ([Hwg Herr_ptrs]& %Hi_ineq & %Hlookup) HΦ".
    wp_pures.
    wp_apply (wp_WaitGroup__Add with "[$Hwg]").
    { word. }
    iIntros "[Hwg Hwg_tok]".
    wp_pures.
    replace (int.nat clerks_sl.(Slice.sz) - int.nat i) with (S (int.nat clerks_sl.(Slice.sz) - (int.nat (word.add i 1)))) by word.
    rewrite replicate_S.
    iDestruct (array_cons with "Herr_ptrs") as "[Herr_ptr Herr_ptrs]".
    (* use wgTok to set errs_sl *)
    iDestruct (own_WaitGroup_to_is_WaitGroup with "[Hwg]") as "#His_wg".
    {
      iExactEq "Hwg". econstructor. (* FIXME: why doesn't framing work? *)
    }
    wp_apply (wp_fork with "[Hwg_tok Herr_ptr]").
    {
      iNext.
      iDestruct (big_sepL2_lookup_1_some with "Hclerks_rpc") as %[γsrv' Hlookupγ].
      { done. }
      iDestruct (big_sepL2_lookup_acc with "Hclerks_rpc") as "Hclerk_rpc".
      { done. }
      { done. }
      iDestruct "Hclerk_rpc" as "[[Hclerk_rpc Hepoch_lb] _]".
      wp_apply (wp_Clerk__Apply with "[$Hclerk_rpc $Hepoch_lb]").
      {
        iFrame "Hprop_lb Hprop_facts2 # %".
        iPureIntro.
        rewrite last_app.
        rewrite app_length.
        rewrite Hσ_nextIndex.
        simpl.
        split; eauto.
        split; eauto.
        split; first done.
        (* FIXME: add overflow check *)
        admit.
      }
      iIntros (err) "#Hpost".
      unfold SliceSet.
      wp_pures.
      unfold slice.ptr.
      wp_pures.
      wp_store.

      iMod (readonly_alloc_1 with "Herr_ptr") as "#Herr_ptr".
      wp_apply (wp_WaitGroup__Done with "[$Hwg_tok $His_wg Herr_ptr Hpost]").
      {
        iModIntro.
        iExists _, _.
        iSplitL ""; first done.
        iFrame "#".
      }
      done.
    }
    iApply "HΦ".
    iSplitL "Hwg".
    {
      iExactEq "Hwg". econstructor. (* FIXME: more framing not working *)
    }
    iExactEq "Herr_ptrs".
    f_equal.
    rewrite /ty_size //=.
    rewrite loc_add_assoc.
    f_equal.
    word.
  }
  iIntros "[[Hwg _] _]".
  wp_pures.

  wp_apply (wp_WaitGroup__Wait with "[$Hwg]").
  iIntros "Hwg_post".
  wp_pures.
  wp_apply (wp_ref_to).
  { repeat econstructor. }
  iIntros (err_ptr) "Herr".
  wp_pures.

  wp_apply (wp_ref_to).
  { do 2 econstructor. }
  iIntros (j_ptr) "Hi".
  wp_pures.

  set (conf:=(γsrv::backups)).
  iAssert (∃ (j err:u64),
              "Hj" ∷ j_ptr ↦[uint64T] #j ∗
              "Herr" ∷ err_ptr ↦[uint64T] #err ∗
              "Hrest" ∷ if (decide (err = 0)) then
                (∀ k γsrv', ⌜int.nat k ≤ int.nat j⌝ -∗ ⌜conf !! k = Some γsrv'⌝ -∗ is_accepted_lb γsrv' epoch0 (σ++[ghost_op]))
              else
                True
          )%I with "[Hi Herr]" as "Hloop".
  {
    iExists _, _.
    iFrame.
    destruct (decide (_)).
    {
      iIntros.
      (* FIXME: show that the leader has accepted *)
      admit.
    }
    {
      done.
    }
  }
  wp_forBreak_cond.
  wp_pures.
  iNamed "Hloop".
  wp_load.
  wp_apply wp_slice_len.

  wp_pures.
  wp_if_destruct.
  {
    wp_pures.
    wp_load.
    unfold SliceGet.
    wp_call.
    iDestruct (big_sepS_elem_of_acc _ _ j with "Hwg_post") as "[HH _]".
    { set_solver. }
    iDestruct "HH" as "[%Hbad|HH]".
    { exfalso. word. }
    iDestruct "HH" as (??) "(%HbackupLookup & Herr2 & Hpost)".
    wp_apply (wp_slice_ptr).
    wp_pure1.
    iEval (simpl) in "Herr2".
    iMod (readonly_load with "Herr2") as (?) "Herr3".
    wp_load.
    wp_pures.
    wp_if_destruct.
    {
      wp_store.
      wp_pures.
      wp_load; wp_store.
      iLeft.
      iModIntro.
      iSplitL ""; first done.
      admit.
    }
    {
      wp_pures.
      wp_load; wp_store.
      iLeft.
      iModIntro.
      iSplitL ""; first done.
      admit.
    }
  }
  iRight.
  iModIntro.
  iSplitL ""; first done.
  wp_pures.
  wp_load.
  wp_pures.
  iModIntro.
  (* iApply "HΦ". *)
  admit.

  }
  wp_apply (wp_forSlice (λ j,
                          ∃ (err:u64),
                          err_ptr ↦[uint64T] #err ∗
                          if (decide (err = 0)) then
                            (∀ k γsrv', ⌜int.nat k ≤ int.nat j⌝ -∗ ⌜conf !! k = Some γsrv'⌝ -∗ is_accepted_lb γsrv' epoch0 (σ++[ghost_op]))%I
                          else
                            True
           )%I with "[Herr]").
  {
    iIntros (??).
    admit.
  }
Admitted.

End pb_definitions.
