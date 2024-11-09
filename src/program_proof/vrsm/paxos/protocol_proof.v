From Perennial.program_proof Require Import grove_prelude.
From iris.base_logic Require Export lib.ghost_var mono_nat.
From iris.algebra Require Import dfrac_agree mono_list csum.
From Perennial.algebra Require Export fmlist_map.
From Perennial.Helpers Require Import ListSolver.

Record mp_system_names :=
{
  mp_proposal_gn : gname ;
  mp_state_gn : gname ;
}.

Record mp_server_names :=
{
  mp_accepted_gn : gname ;
  mp_vote_gn : gname ; (* token for granting vote to a node in a particular epoch *)
}.

Section mpaxos_protocol.

Context `{EntryType:Type}.
Local Canonical Structure EntryTypeO := leibnizO EntryType.
Local Definition logR := mono_listR EntryTypeO.

Class mpaxosG Σ := {
    #[global] mp_ghost_epochG :: mono_natG Σ ;
    #[global] mp_ghost_mapG :: fmlist_mapG Σ u64 EntryType ;
    #[global] mp_ghost_commitG :: inG Σ logR ;
    #[global] mp_proposal_escrowG :: inG Σ (gmapR (u64) (dfrac_agreeR unitO)) ;
}.

Definition mpaxosΣ :=
  #[mono_natΣ ; fmlist_mapΣ u64 EntryType ;
    GFunctor (gmapR (u64) logR) ;
    GFunctor logR ;
    GFunctor (gmapR u64 (dfrac_agreeR unitO))
    ].
Global Instance subG_mp_ghostΣ {Σ} : subG (mpaxosΣ) Σ → (mpaxosG Σ).
Proof. solve_inG. Qed.

Context `{!invGS Σ}.
Context `{!mpaxosG Σ}.

Implicit Type γsrv : mp_server_names.
Implicit Type γsys : mp_system_names.
Implicit Type σ : list EntryType.
Implicit Type epoch : u64.

Definition own_proposal γsys epoch σ : iProp Σ :=
  epoch ⤳l[γsys.(mp_proposal_gn)] σ.

Local Definition is_proposal_lb γsys epoch σ : iProp Σ :=
  epoch ⤳l[γsys.(mp_proposal_gn)]⪰ σ.

Definition own_vote_tok γsrv epoch : iProp Σ :=
  own γsrv.(mp_vote_gn) {[ epoch := to_dfrac_agree (DfracOwn 1) ()]}.

Definition own_accepted γ epoch σ : iProp Σ :=
  epoch ⤳l[γ.(mp_accepted_gn)] σ.
Definition is_accepted_lb γ epoch σ : iProp Σ :=
  epoch ⤳l[γ.(mp_accepted_gn)]⪰ σ.
Definition is_accepted_ro γ epoch σ : iProp Σ :=
  epoch ⤳l[γ.(mp_accepted_gn)]□ σ.

(* TODO: if desired, can make these exclusive by adding an exclusive token to each *)
Definition own_log γ σ : iProp Σ :=
  own γ.(mp_state_gn) (●ML{#1/2} σ).
Definition own_commit γ σ : iProp Σ :=
  own γ.(mp_state_gn) (●ML{#1/2} σ).
Definition is_log_lb γ σ : iProp Σ :=
  own γ.(mp_state_gn) (◯ML σ).

(* This definition needs to only require a quorum *)
Context `{config:list mp_server_names}.
Context {N:namespace}.
Definition committed_by epoch σ : iProp Σ :=
  ∃ (W:gset nat),
  ⌜(∀ s, s ∈ W → s < length config)⌝ ∗
  ⌜2 * (size W) > length config⌝ ∗
  ([∗ list] s0↦γsrv' ∈ config, ⌜s0 ∈ W⌝ → is_accepted_lb γsrv' epoch σ).

Notation "lhs ⪯ rhs" := (prefix lhs rhs)
(at level 20, format "lhs  ⪯  rhs") : stdpp_scope.

Definition old_proposal_max γsys epoch σ : iProp Σ := (* persistent *)
  □(∀ epoch_old σ_old,
   ⌜uint.nat epoch_old < uint.nat epoch⌝ →
   committed_by epoch_old σ_old → ⌜σ_old ⪯ σ⌝).

Definition ghostN := N .@ "ghost".

Definition sysN := ghostN .@ "sys".
Definition opN := ghostN .@ "op".

(* XXX(namespaces):
   The update for the ghost state is fired while is_repl_inv is open.
   Additionally, the update is fired while the is_valid_inv is open, so we need
   the initial mask to exclude those invariants.
*)
Definition is_valid_inv γsys σ op : iProp Σ :=
  inv opN (
    £ 1 ∗
    (|={⊤∖↑ghostN,∅}=> ∃ someσ, own_log γsys someσ ∗ (⌜someσ = σ⌝ -∗ own_log γsys (someσ ++ [op]) ={∅,⊤∖↑ghostN}=∗ True)) ∨
    is_log_lb γsys (σ ++ [op])
  )
.

Definition is_proposal_valid γ σ : iProp Σ :=
  □(∀ σ', ⌜σ' ⪯ σ⌝ → own_commit γ σ' ={⊤∖↑sysN}=∗ own_commit γ σ).

Local Definition is_proposal_facts γ epoch σ: iProp Σ :=
  old_proposal_max γ epoch σ ∗
  is_proposal_valid γ σ.

Record MPaxosState :=
  mkMPaxosState
    {
      mp_epoch:u64 ;
      mp_acceptedEpoch:u64 ;
      mp_log:list EntryType ;
    }.

Definition is_accepted_upper_bound γsrv log (acceptedEpoch newEpoch:u64) : iProp Σ :=
  ∃ logPrefix,
  ⌜logPrefix ⪯ log⌝ ∗
  is_accepted_ro γsrv acceptedEpoch logPrefix ∗
  □ (∀ epoch', ⌜uint.nat acceptedEpoch < uint.nat epoch'⌝ -∗
            ⌜uint.nat epoch' < uint.nat newEpoch⌝ -∗
            is_accepted_ro γsrv epoch' [])
.


Definition own_replica_ghost γsys γsrv (st:MPaxosState) : iProp Σ :=
  "#Hprop_lb" ∷ is_proposal_lb γsys st.(mp_acceptedEpoch) st.(mp_log) ∗
  "#Hprop_facts" ∷ is_proposal_facts γsys st.(mp_acceptedEpoch) st.(mp_log) ∗
  "#Hacc_lb" ∷ is_accepted_lb γsrv st.(mp_acceptedEpoch) st.(mp_log) ∗
  "%HepochIneq" ∷ ⌜uint.nat st.(mp_acceptedEpoch) ≤ uint.nat st.(mp_epoch)⌝ ∗

  "Hacc" ∷ own_accepted γsrv st.(mp_epoch)
                                  (if (decide (uint.nat st.(mp_acceptedEpoch) = uint.nat st.(mp_epoch))) then
                                     st.(mp_log)
                                   else []) ∗
   (* XXX: could combine this with the previous proposition *)
  "#Hacc_ub" ∷ (⌜uint.nat st.(mp_acceptedEpoch) < uint.nat st.(mp_epoch)⌝ →
                 is_accepted_upper_bound γsrv st.(mp_log) st.(mp_acceptedEpoch) st.(mp_epoch)) ∗


  "Hunused" ∷ ([∗ set] e ∈ (fin_to_set u64), (⌜uint.nat e > uint.nat st.(mp_epoch)⌝ → own_accepted γsrv e [])) ∗
  "Hvotes" ∷ ([∗ set] epoch' ∈ (fin_to_set u64), ⌜uint.nat epoch' ≤ uint.nat st.(mp_epoch)⌝ ∨ own_vote_tok γsrv epoch')
.

Definition own_leader_ghost γsys (st:MPaxosState): iProp Σ :=
  "Hprop" ∷ own_proposal γsys st.(mp_epoch) st.(mp_log) ∗
  "#Hprop_facts" ∷ is_proposal_facts γsys st.(mp_epoch) st.(mp_log)
.

Definition is_proposal γsys epoch log : iProp Σ :=
  is_proposal_lb γsys epoch log ∗
  is_proposal_facts γsys epoch log
.

Lemma ghost_leader_propose γsys st entry :
  own_leader_ghost γsys st -∗
  £ 1 -∗
  (|={⊤∖↑ghostN,∅}=> ∃ someσ, own_log γsys someσ ∗
      (⌜someσ = st.(mp_log)⌝ -∗ own_log γsys (someσ ++ [entry]) ={∅,⊤∖↑ghostN}=∗ True))
  ={↑sysN}=∗
  own_leader_ghost γsys (mkMPaxosState st.(mp_epoch) st.(mp_acceptedEpoch) (st.(mp_log) ++ [entry]))∗
  is_proposal γsys st.(mp_epoch) (st.(mp_log) ++ [entry])
.
Proof.
  iNamed 1.
  iIntros "Hlc Hupd".

  iMod (fmlist_ptsto_update (_ ++ [entry]) with "Hprop") as "Hprop".
  { by apply prefix_app_r. }
  iDestruct (fmlist_ptsto_get_lb with "Hprop") as "#Hprop_lb".
  iFrame "∗#".

  iAssert (|={↑sysN}=> is_proposal_facts γsys st.(mp_epoch) (st.(mp_log) ++ [entry]))%I with "[Hupd Hlc]" as ">#Hvalid2".
  {
    iDestruct "Hprop_facts" as "(Hmax & Hvalid)".
    iSplitL "".
    { (* old proposal max *)
      iModIntro.
      unfold old_proposal_max.
      iModIntro.
      iIntros.
      iAssert (⌜σ_old ⪯ st.(mp_log)⌝)%I as "%Hprefix".
      {
        iApply "Hmax".
        {
          done.
        }
        { iFrame "#". }
      }
      iPureIntro.
      apply prefix_app_r.
      done.
    }

    iAssert (|={↑sysN}=> is_valid_inv γsys st.(mp_log) entry)%I with "[Hupd Hlc]" as ">#Hinv".
    {
      iMod (inv_alloc with "[Hupd Hlc]") as "$".
      {
        iNext.
        iLeft.
        iFrame.
      }
      done.
    }
    (* prove is_proposal_valid γ (σ ++ [op]) *)
    iModIntro.
    iModIntro.
    iIntros (σ') "%Hσ' Hσ'".
    assert (σ' ⪯ st.(mp_log) ∨ σ' = (st.(mp_log) ++ [entry])) as [Hprefix_old|Hlatest].
    { (* TODO: list_solver. *)
      (* TODO: copy/paste from pb_ghost *)
      assert (Hlen := Hσ').
      apply prefix_length in Hlen.
      assert (length σ' = length (st.(mp_log) ++ [entry]) ∨ length σ' < length (st.(mp_log) ++ [entry])) as [|] by word.
      {
        right.
        apply list_prefix_eq; eauto.
        lia.
      }
      {
        left.
        rewrite length_app in H.
        simpl in H.
        apply list_prefix_bounded.
        { word. }
        intros.
        assert (st.(mp_log) !! i = (st.(mp_log) ++ [entry]) !! i).
        {
          rewrite lookup_app_l.
          { done. }
          { word. }
        }
        rewrite H1.
        apply list_prefix_forall.
        { done. }
        { done. }
      }
    }
    {
      iMod ("Hvalid" $! σ' Hprefix_old with "Hσ'") as "Hσ".
      iInv "Hinv" as "Hi" "Hclose".
      iDestruct "Hi" as "[Hupd|#>Hlb]"; last first.
      {
        iDestruct (own_valid_2 with "Hσ Hlb") as "%Hvalid".
        exfalso.
        rewrite mono_list_both_dfrac_valid_L in Hvalid.
        destruct Hvalid as [_ Hvalid].
        apply prefix_length in Hvalid.
        rewrite length_app in Hvalid.
        simpl in Hvalid.
        word.
      }
      iDestruct "Hupd" as "[>Hlc Hupd]".
      iMod (lc_fupd_elim_later with "Hlc Hupd" ) as "Hupd".
      iMod (fupd_mask_subseteq (⊤∖↑ghostN)) as "Hmask".
      {
        assert ((↑sysN:coPset) ⊆ (↑ghostN:coPset)).
        { apply nclose_subseteq. }
        assert ((↑opN:coPset) ⊆ (↑ghostN:coPset)).
        { apply nclose_subseteq. }
        set_solver.
      }
      iMod "Hupd".
      iDestruct "Hupd" as (?) "[Hghost Hupd]".
      iDestruct (own_valid_2 with "Hghost Hσ") as %Hvalid.
      rewrite mono_list_auth_dfrac_op_valid_L in Hvalid.
      destruct Hvalid as [_ ->].
      iCombine "Hghost Hσ" as "Hσ".
      iMod (own_update with "Hσ") as "Hσ".
      {
        apply (mono_list_update (st.(mp_log) ++ [entry])).
        by apply prefix_app_r.
      }
      iEval (rewrite -Qp.half_half) in "Hσ".
      rewrite -dfrac_op_own.
      rewrite mono_list_auth_dfrac_op.
      iDestruct "Hσ" as "[Hσ Hcommit]".
      iSpecialize ("Hupd" with "[] Hσ").
      { done. }
      iMod "Hupd".

      rewrite mono_list_auth_lb_op.
      iDestruct "Hcommit" as "[Hcommit #Hlb]".
      iMod "Hmask".
      iMod ("Hclose" with "[]").
      {
        iNext.
        iRight.
        iFrame "Hlb".
      }
      iModIntro.
      iFrame.
    }
    {
      rewrite Hlatest.
      by iFrame.
    }
  }
  iModIntro.
  iFrame "#".
Qed.

Lemma ghost_replica_get_lb γsys γsrv st :
  own_replica_ghost γsys γsrv st -∗
  is_accepted_lb γsrv st.(mp_acceptedEpoch) st.(mp_log).
Proof.
  by iNamed 1.
Qed.

(* Similar to ghost_accept in pb_ghost.v *)
Lemma ghost_replica_accept_same_epoch γsys γsrv st epoch' log' :
  uint.nat st.(mp_epoch) ≤ uint.nat epoch' →
  uint.nat st.(mp_acceptedEpoch) = uint.nat epoch' →
  length st.(mp_log) ≤ length log' →
  own_replica_ghost γsys γsrv st -∗
  is_proposal γsys epoch' log'
  ==∗
  ⌜st.(mp_epoch) = epoch'⌝ ∗
  own_replica_ghost γsys γsrv (mkMPaxosState epoch' epoch' log').
Proof.
  intros Hineq1 Hineq2 Hlen.
  iNamed 1.
  iIntros "[#Hprop_lb2 #Hprop_facts2]".
  iAssert (⌜st.(mp_epoch) = epoch'⌝)%I as "%HepochEq".
  { word. }
  iFrame "%".
  destruct (decide _); last first.
  {
    exfalso. naive_solver.
  }
  subst.
  destruct st. simpl in *.
  assert (mp_acceptedEpoch0 = mp_epoch0) by word; subst.
  iDestruct (fmlist_ptsto_lb_comparable with "Hprop_lb Hprop_lb2") as %Hcomp.

  assert (mp_log0⪯log').
  {
    destruct Hcomp as [Hbad|Hcomp]; first done.
    enough (log'=mp_log0) by naive_solver.
    by apply list_prefix_eq.
  }

  iMod (fmlist_ptsto_update log' with "Hacc") as "Hacc".
  { done. }
  iClear "Hacc_lb".
  iDestruct (fmlist_ptsto_get_lb with "Hacc") as "#Hacc_lb".
  iModIntro.
  unfold own_replica_ghost.
  simpl.
  rewrite decide_True; last done.
  iFrame "∗#".
  iSplitL; first done.
  iIntros (?).
  exfalso.
  lia.
Qed.

Lemma ghost_replica_accept_same_epoch_old γsys γsrv st epoch' log' :
  uint.nat st.(mp_epoch) ≤ uint.nat epoch' →
  uint.nat st.(mp_acceptedEpoch) = uint.nat epoch' →
  length log' ≤ length st.(mp_log) →
  own_replica_ghost γsys γsrv st -∗
  is_proposal γsys epoch' log' -∗
  is_accepted_lb γsrv epoch' log'.
Proof.
  intros Hineq1 Heq2 Hlen.
  iNamed 1.
  iIntros "#[Hprop_lb2 _]".
  iAssert (⌜st.(mp_epoch) = epoch'⌝)%I as "%HepochEq".
  { word. }
  iFrame "%".
  destruct (decide _); last first.
  {
    exfalso. naive_solver.
  }

  subst.
  replace (st.(mp_acceptedEpoch)) with (st.(mp_epoch)) by word.
  iDestruct (fmlist_ptsto_lb_comparable with "Hprop_lb Hprop_lb2") as %Hcomp.

  assert (log'⪯st.(mp_log)).
  {
    destruct Hcomp as [Hbad|Hcomp]; last done.
    enough (log'=st.(mp_log)) by naive_solver.
    symmetry.
    by apply list_prefix_eq.
  }
  by iApply fmlist_ptsto_lb_mono.
Qed.

Lemma ghost_replica_accept_new_epoch γsys γsrv st epoch' log' :
  uint.nat st.(mp_epoch) ≤ uint.nat epoch' →
  uint.nat st.(mp_acceptedEpoch) ≠ uint.nat epoch' →
  own_replica_ghost γsys γsrv st -∗
  is_proposal γsys epoch' log'
  ==∗
  own_replica_ghost γsys γsrv (mkMPaxosState epoch' epoch' log').
Proof.
  intros Hineq1 Hneq2.
  iNamed 1.
  iIntros "[#Hprop_lb2 #Hprop_facts2]".
  assert (uint.nat st.(mp_epoch) < uint.nat epoch' ∨ uint.nat st.(mp_epoch) = uint.nat epoch') as Hcases.
  { word. }
  destruct Hcases as [HnewEpoch|HcurrentEpoch].
  { (* case: mp_acceptedEpoch < mp_epoch == epoch'; get stuff out of Hunused *)
    iClear "Hacc".
    iDestruct (big_sepS_elem_of_acc_impl epoch' with "Hunused") as "[Hacc Hunused]".
    { set_solver. }
    iSpecialize ("Hacc" with "[%//]").
    iMod (fmlist_ptsto_update log' with "Hacc") as "Hacc".
    { apply prefix_nil. }
    iModIntro.
    iClear "Hacc_lb".
    iDestruct (fmlist_ptsto_get_lb with "Hacc") as "#Hacc_lb".
    unfold own_replica_ghost.
    simpl.
    destruct (decide _); last first.
    { exfalso. done. }
    iFrame "Hacc #".
    iSplitR; first done.
    iSplitR.
    { iIntros (?). exfalso. lia. }
    iSplitL "Hunused".
    {
      iApply "Hunused".
      {
        iModIntro.
        iIntros (???) "Hwand".
        iIntros (Hy).
        iApply "Hwand".
        word.
      }
      {
        iIntros.
        exfalso. lia.
      }
    }
    iApply (big_sepS_impl with "Hvotes").
    iModIntro.
    iIntros (??) "[%|$]".
    iLeft.
    word.
  }
  { (* case: mp_acceptedEpoch < mp_epoch == epoch'; use existing acc *)
    destruct (decide _).
    { exfalso. word. }

    iMod (fmlist_ptsto_update log' with "Hacc") as "Hacc".
    { apply prefix_nil. }
    iModIntro.
    iClear "Hacc_lb".
    iDestruct (fmlist_ptsto_get_lb with "Hacc") as "#Hacc_lb".
    unfold own_replica_ghost.
    assert (epoch' = st.(mp_epoch)) by word.
    subst.

    unfold own_replica_ghost.
    simpl.
    destruct (decide _); last first.
    { exfalso. done. }
    iFrame "Hacc #".
    iSplitR; first done.
    iSplitR.
    { iIntros (?). exfalso. lia. }
    iSplitL "Hunused".
    {
      iApply (big_sepS_impl with "Hunused").
      iModIntro.
      iIntros (??) "Hwand".
      iIntros (?).
      iApply "Hwand".
      word.
    }
    {
      iApply (big_sepS_impl with "Hvotes").
      iModIntro.
      iIntros (??) "[%|$]".
      iLeft.
      word.
    }
  }
Qed.

(* TODO: this is just the definition *)
Lemma establish_committed_by epoch σ (W:gset nat) :
  (∀ s, s ∈ W → s < length config) →
  2 * (size W) > length config →
  ([∗ list] s0↦γsrv' ∈ config, ⌜s0 ∈ W⌝ → is_accepted_lb γsrv' epoch σ) -∗
  committed_by epoch σ.
Proof.
  iIntros.
  iExists _; iFrame "∗#%".
Qed.

Definition is_repl_inv γsys := inv sysN
(
  ∃ σ epoch,
  own_commit γsys σ ∗
  committed_by epoch σ ∗
  is_proposal_lb γsys epoch σ ∗
  is_proposal_facts γsys epoch σ
).

(* copy/pasted almost verbatin from ghost_commit in pb_ghost.v! *)
Lemma ghost_commit γsys epoch σ :
  is_repl_inv γsys -∗
  committed_by epoch σ -∗
  is_proposal γsys epoch σ
  ={⊤}=∗ (* XXX: this is ⊤ because the user-provided fupd is fired, and it is allowed to know about ⊤ *)
  is_log_lb γsys σ.
Proof.
  iIntros "#Hinv #Hcom [#Hprop_lb #Hprop_facts]".
  iInv "Hinv" as "Hown" "Hclose".
  iDestruct "Hown" as (σcommit epoch_commit) "(>Hghost & >#Hcom_com & >#Hprop_lb_com & #Hprop_facts_com)".
  iDestruct "Hprop_facts_com" as "(>Hmax_com & Hvalid_com)".
  iDestruct "Hprop_facts" as "(Hmax & Hvalid)".
  iAssert (⌜σcommit ⪯ σ⌝ ∨ ⌜σ ⪯ σcommit⌝)%I as "%Hlog".
  {
    assert (uint.nat epoch < uint.nat epoch_commit ∨ uint.nat epoch = uint.nat epoch_commit ∨ uint.nat epoch > uint.nat epoch_commit) as [Hepoch|[Hepoch|Hepoch]]by word.
    { (* case epoch < epoch_commit: use old_proposal_max of epoch_commit. *)
      iRight.
      by iApply "Hmax_com".
    }
    { (* case epoch = epoch_commit: proposal is comparable *)
      replace (epoch) with (epoch_commit) by word.
      iDestruct (fmlist_ptsto_lb_comparable with "Hprop_lb Hprop_lb_com") as %Hcomp.
      iPureIntro.
      naive_solver.
    }
    { (* case epoch_commit < epoch: use old_proposal_max of epoch *)
      iLeft.
      by iApply "Hmax".
    }
  }

  destruct Hlog as [Hcan_update|Halready_updated].
  {
    iEval (unfold is_proposal_valid) in "Hvalid".
    iDestruct ("Hvalid" $! σcommit with "[] Hghost") as "Hghost".
    { done. }
    iMod "Hghost".
    unfold own_commit.
    iEval (rewrite mono_list_auth_lb_op) in "Hghost".
    iDestruct "Hghost" as "[Hghost $]".
    iMod ("Hclose" with "[-]").
    {
      iNext.
      iExists _, _. iFrame "∗".
      iFrame "Hcom".
      iFrame "#".
    }
    done.
  }
  {
    unfold own_commit.
    iEval (rewrite mono_list_auth_lb_op) in "Hghost".
    iDestruct "Hghost" as "[Hghost #Hlb]".
    iDestruct (own_mono with "Hlb") as "$".
    {
      by apply mono_list_lb_mono.
    }
    iMod ("Hclose" with "[-]").
    {
      iNext.
      iExists _, _. iFrame "∗#".
    }
    done.
  }
Qed.

Lemma is_accepted_upper_bound_mono_epoch γsrv log acceptedEpoch acceptedEpoch' newEpoch :
  uint.nat acceptedEpoch < uint.nat acceptedEpoch' →
  uint.nat acceptedEpoch' < uint.nat newEpoch →
  is_accepted_upper_bound γsrv log acceptedEpoch newEpoch -∗
  is_accepted_upper_bound γsrv [] acceptedEpoch' newEpoch
.
Proof.
  intros Hineq Hineq2.
  iIntros "#Hub".
  iExists [].
  iSplitL; first done.
  iSplit.
  {
    iDestruct "Hub" as (?) "(_ & _ & #Hwand)".
    iApply "Hwand".
    { done. }
    { done. }
  }
  {
    iModIntro.
    iIntros.
    iDestruct "Hub" as (?) "(_ & _ & #Hwand)".
    iApply "Hwand".
    { iPureIntro.
      word. }
    { iPureIntro.
      word. }
  }
Qed.

Lemma is_accepted_upper_bound_mono_log γsrv log log' acceptedEpoch newEpoch :
  prefix log log' →
  is_accepted_upper_bound γsrv log acceptedEpoch newEpoch -∗
  is_accepted_upper_bound γsrv log' acceptedEpoch newEpoch
.
Proof.
  intros Hle.
  iIntros "Hacc_ub".
  iDestruct "Hacc_ub" as (?) "(%Hpre & #Hro & #Hskip)".
  iExists _; iFrame "Hro".
  iSplitR.
  {
    iPureIntro.
    by transitivity log.
  }
  iModIntro.
  iIntros.
  iApply "Hskip".
  { word. }
  { word. }
Qed.

Lemma is_proposal_compare γsys log log' epoch :
  length log' ≤ length log →
  is_proposal γsys epoch log -∗
  is_proposal γsys epoch log' -∗
  ⌜prefix log' log⌝
.
Proof.
  intros Hlen.
  iIntros "[Hprop1 _] [Hprop2 _]".
  iDestruct (fmlist_ptsto_lb_longer with "Hprop2 Hprop1") as %?; done.
Qed.

Definition validSet (W:gset nat) :=
  ∀ s, s ∈ W → s < length config.

Lemma validSet_union (W1 W2:gset nat) :
  validSet W1 →
  validSet W2 →
  validSet (W1 ∪ W2).
Proof.
  intros.
  intros ??.
  apply elem_of_union in H1 as [|].
  { naive_solver. }
  { naive_solver. }
Qed.

Lemma set_size_all_lt (W : gset nat) n:
 (∀ s : nat, s ∈ W → s < n) → size W ≤ n.
Proof.
  revert W.
  induction n as [| n IHn] => W Hvalid.
  - destruct W as [| x W] using set_ind_L; auto.
    exfalso. opose proof (Hvalid x _); first by set_solver. lia.
  - transitivity (size ({[n]} ∪ (W ∖ {[n]}))).
    { apply subseteq_size. set_unfold. intros x. destruct (decide (x = n)); auto. }
    rewrite size_union ?size_singleton; last by set_solver.
    opose proof (IHn (W ∖ {[n]}) _).
    { set_unfold. intros x (Hin&?). opose proof (Hvalid x _); auto. lia. }
    lia.
Qed.

Lemma validSet_size (W:gset nat) :
  validSet W →
  size W ≤ length config.
Proof.
  rewrite /validSet. apply set_size_all_lt.
Qed.

Definition is_vote_inv γsys := inv sysN
(
  [∗ set] e ∈ (fin_to_set u64),
  (∃ (W:gset nat), ⌜validSet W⌝ ∗ ⌜2 * (size W) > length config⌝ ∗
  [∗ list] s↦γsrv ∈ config, ⌜s ∈ W⌝ → own_vote_tok γsrv e) ∨
  own_proposal γsys e []
).

Lemma quorum_overlap W1 W2 :
  validSet W1 →
  2 * (size W1) > length config →
  validSet W2 →
  2 * (size W2) > length config →
  ∃ x γsrv, x ∈ W1 ∧ x ∈ W2 ∧
            config !! x = Some γsrv
.
Proof.
  intros HW Hquorum  HW2 Hquorum2.
  destruct (decide ((W1 ∩ W2) = ∅)).
  { (* case: the proposal has already been claimed; this should be impossible *)
    exfalso.
    pose proof (size_union W1 W2) as H.
    assert (W1 ## W2).
    { set_solver. }
    apply H in H0.
    pose proof (validSet_union _ _ HW HW2) as HuValid.
    apply validSet_size in HuValid.
    word.
  }
  {
    apply set_choose_L in n.
    destruct n as [s Hs].
    apply elem_of_intersection in Hs as [HsW HsW2].
    (* get a vote out of Hvotes1 and Hvotes2, then contradiction *)
    assert (s < length config).
    { apply HW. done. }
    pose proof (list_lookup_lt _ _ H) as [γsrv' Hlookup].
    exists s, γsrv'.
    done.
  }
Qed.

Lemma get_proposal_from_votes γsys (W:gset nat) newEpoch :
  2 * (size W) > length config →
  validSet W →
  is_vote_inv γsys -∗
  ([∗ list] s↦γsrv ∈ config, ⌜s ∈ W⌝ → own_vote_tok γsrv newEpoch) ={↑sysN}=∗
  own_proposal γsys newEpoch [].
Proof.
  intros Hquorum HW.
  iIntros "#Hinv Hvotes".
  iInv "Hinv" as ">Hi" "Hclose".
  iDestruct (big_sepS_elem_of_acc_impl newEpoch with "Hi") as "[Hprop Hi]".
  { set_solver. }
  iDestruct "Hprop" as "[Hbad|Hprop]".
  {
    iDestruct "Hbad" as (W2) "(%HW2 & %Hquorum2 & Hvotes2)".
    pose proof (quorum_overlap _ _ HW Hquorum HW2 Hquorum2) as [? [? [? []]]].

    iDestruct (big_sepL_lookup_acc with "Hvotes") as "[Hvote1 _]".
    { done. }
    iSpecialize ("Hvote1" with "[%//]").
    iDestruct (big_sepL_lookup_acc with "Hvotes2") as "[Hvote2 _]".
    { done. }
    iSpecialize ("Hvote2" with "[%//]").
    iDestruct (own_valid_2 with "Hvote1 Hvote2") as %Hbad.
    exfalso.
    rewrite singleton_op in Hbad.
    rewrite singleton_valid in Hbad.
    apply dfrac_agree_op_valid_L in Hbad as [Hbad _].
    done.
  }
  iFrame "Hprop".
  iMod ("Hclose" with "[Hi Hvotes]").
  {
    iApply ("Hi" with "[] [Hvotes]").
    {
      iModIntro.
      iIntros.
      iFrame.
    }
    {
      iLeft.
      iExists _; iFrame.
      done.
    }
  }
  done.
Qed.

Lemma accepted_upper_bound_lb γsrv acceptedEpoch newEpoch log log':
  is_accepted_lb γsrv acceptedEpoch log -∗
  is_accepted_upper_bound γsrv log' acceptedEpoch newEpoch -∗
  ⌜log ⪯ log'⌝
.
Proof.
  iIntros "#Hacc_lb #Hacc_ub".
  iDestruct "Hacc_ub" as (?) "(%Hpre & #Hacc_ro & Hacc_ub)".
  iDestruct (fmlist_ptsto_lb_agree with "Hacc_ro Hacc_lb") as %Hvalid.
  iPureIntro.
  by eapply transitivity.
Qed.

Lemma accepted_upper_bound_lb2 γsrv acceptedEpoch epoch newEpoch log log':
  uint.nat acceptedEpoch < uint.nat epoch →
  uint.nat epoch < uint.nat newEpoch →
  is_accepted_lb γsrv epoch log -∗
  is_accepted_upper_bound γsrv log' acceptedEpoch newEpoch -∗
  ⌜log ⪯ log'⌝
.
Proof.
  intros Hineq Hineq2.
  iIntros "#Hacc_lb #Hacc_ub".
  iDestruct "Hacc_ub" as (?) "(%Hpre & #Hacc_ro & #Hacc_ub)".
  iSpecialize ("Hacc_ub" $! epoch with "[%//] [%//]").

  iDestruct (fmlist_ptsto_lb_agree with "Hacc_ub Hacc_lb") as %Hvalid.
  destruct Hvalid as [ ? Hvalid ]. symmetry in Hvalid.
  apply app_eq_nil in Hvalid as [-> ]. iPureIntro.
  apply prefix_nil.
Qed.

(* This is where the magic happens *)
Lemma become_leader γsys (W:gset nat) latestLog acceptedEpoch newEpoch:
  validSet W →
  2 * (size W) > length config →
  is_vote_inv γsys -∗
  ([∗ list] s↦γsrv ∈ config, ⌜s ∈ W⌝ → is_accepted_upper_bound γsrv latestLog acceptedEpoch newEpoch) -∗
  is_proposal γsys acceptedEpoch latestLog -∗
  ([∗ list] s↦γsrv ∈ config, ⌜s ∈ W⌝ → own_vote_tok γsrv newEpoch) ={↑sysN}=∗
  own_leader_ghost γsys (mkMPaxosState newEpoch newEpoch latestLog)
.
Proof.
  intros HW Hquorum.
  iIntros "#Hinv #Hacc [#Hprop_lb #Hprop_facts] Hvotes".

  iMod (get_proposal_from_votes with "Hinv Hvotes") as "Hprop".
  { done. }
  { done. }

  iMod (fmlist_ptsto_update latestLog with "Hprop") as "Hprop".
  { apply prefix_nil. }

  iFrame "Hprop".
  iDestruct "Hprop_facts" as "[Hmax Hvalid]".
  iFrame "Hvalid".

  (* establish old_proposal_max *)
  iModIntro.
  iIntros (?).
  iModIntro.
  simpl.
  iIntros (? HepochIneq) "#Hcom_old".

  destruct (decide (uint.nat epoch_old < uint.nat acceptedEpoch)).
  { (* case: epoch_old < acceptedEpoch, just use prev old_prop_max *)
    iApply "Hmax".
    { done. }
    iFrame "Hcom_old".
  }

  iDestruct "Hcom_old" as (W2) "(%HW2 & %Hquorum2 & Hcom_old)".
  (* note that W and W2 overlap *)
  pose proof (quorum_overlap _ _ HW Hquorum HW2 Hquorum2) as [? [? [? []]]].
  iDestruct (big_sepL_lookup_acc with "Hacc") as "[Hacc_ub _ ]".
  { done. }
  iSpecialize ("Hacc_ub" with "[%//]").
  iDestruct (big_sepL_lookup_acc with "Hcom_old") as "[Hacc_lb _]".
  { done. }
  iSpecialize ("Hacc_lb" with "[%//]").

  destruct (decide (uint.nat acceptedEpoch = uint.nat epoch_old)).
  { (* case: epoch_old = acceptedEpoch *)
    replace (acceptedEpoch) with (epoch_old); last first.
    {
      assert (uint.Z acceptedEpoch = uint.Z epoch_old) by word.
      naive_solver. (* XXX: why do I have to assert this Z inequalit? *)
    } (* we have uint.nat a = uint.nat b, and need to show a = b *)
    iDestruct (accepted_upper_bound_lb with "Hacc_lb Hacc_ub") as %Hineq.
    done.
  }
  { (* case: acceptedEpoch < epoch_old < newEpoch *)
    assert (uint.nat acceptedEpoch < uint.nat epoch_old) as Hineq by word.
    iDestruct (accepted_upper_bound_lb2 with "Hacc_lb Hacc_ub") as %Hineq2.
    { done. }
    { done. }
    done.
  }
Qed.

Lemma ghost_leader_get_proposal γsys st :
  own_leader_ghost γsys st -∗
  is_proposal γsys st.(mp_epoch) st.(mp_log)
.
Proof.
  iNamed 1. iFrame "#".
  iDestruct (fmlist_ptsto_get_lb with "Hprop") as "$".
Qed.

Lemma ghost_leader_proposal_ineq γsys st l :
  is_proposal γsys st.(mp_epoch) l -∗
  own_leader_ghost γsys st -∗
  ⌜ l ⪯ st.(mp_log) ⌝
.
Proof.
  iIntros "#[? ?]". iNamed 1.
  iDestruct (fmlist_ptsto_lb_agree with "[$] [$]") as "$".
Qed.

Lemma ghost_replica_leader_init γsys γsrv st1 st2 :
  uint.nat st2.(mp_epoch) ≤ uint.nat st1.(mp_epoch) →
  own_leader_ghost γsys st1 -∗
  own_replica_ghost γsys γsrv st2
  ==∗
  own_replica_ghost γsys γsrv (mkMPaxosState st1.(mp_epoch) st1.(mp_epoch) st1.(mp_log)) ∗
  own_leader_ghost γsys st1.
Proof.
  intros. iNamed 1.
  iRename "Hprop_facts" into "Hprop_facts2".
  iIntros "Hghost".
  iDestruct (fmlist_ptsto_get_lb with "Hprop") as "#Hprop_lb2".
  destruct (decide (uint.nat st1.(mp_epoch) = uint.nat st2.(mp_acceptedEpoch))).
  2:{ (* case: replica is entering new epoch *)
    iMod (ghost_replica_accept_new_epoch  with "[$] [$]") as "Hghost".
    { word. }
    { word. }
    by iFrame "∗#".
  }
  iNamed "Hghost".
  assert (st1.(mp_epoch) = st2.(mp_acceptedEpoch)) by word.
  assert (st2.(mp_epoch) = st2.(mp_acceptedEpoch)) by word.
  destruct st1, st2. simpl in *. subst.
  iDestruct (fmlist_ptsto_lb_agree with "Hprop [$]") as %Hineq.
  rewrite decide_True; last done.
  iMod (fmlist_ptsto_update with "Hacc") as "Hacc".
  { exact Hineq. }
  iClear "Hacc_lb Hprop_lb".
  iDestruct (fmlist_ptsto_get_lb with "Hacc") as "#Hacc_lb".
  iFrame "∗#".
  simpl.
  rewrite decide_True; last done.
  iFrame.
  iSplitR; first done.
  iModIntro. iIntros (?).
  iSpecialize ("Hacc_ub" with "[//]").
  iApply is_accepted_upper_bound_mono_log; last iFrame "#".
  done.
Qed.

Lemma ghost_replica_helper1 γsys γsrv st :
  own_replica_ghost γsys γsrv st -∗
  ⌜uint.nat st.(mp_acceptedEpoch) ≤ uint.nat st.(mp_epoch)⌝.
Proof.
  iNamed 1.
  iPureIntro.
  done.
Qed.

Lemma ghost_replica_enter_new_epoch γsys γsrv st newEpoch :
  uint.nat newEpoch > uint.nat st.(mp_epoch) →
  own_replica_ghost γsys γsrv st ==∗
  own_replica_ghost γsys γsrv (mkMPaxosState newEpoch st.(mp_acceptedEpoch) st.(mp_log)) ∗
  own_vote_tok γsrv newEpoch ∗
  is_accepted_upper_bound γsrv st.(mp_log) st.(mp_acceptedEpoch) newEpoch ∗
  is_proposal γsys st.(mp_acceptedEpoch) st.(mp_log)
.
Proof.
  intros Hineq.
  iNamed 1.

  (* FIXME: take points-tos out of Hunused, with e < newEpoch *)
  set (F1:=(λ e, (⌜uint.nat e > uint.nat st.(mp_epoch)⌝ → ⌜uint.nat e < uint.nat newEpoch⌝ → own_accepted γsrv e []))%I).
  set (F2:=(λ e, (⌜uint.nat e > uint.nat newEpoch⌝ → own_accepted γsrv e []))%I).
  set (F3:=(λ e, (⌜uint.nat e = uint.nat newEpoch⌝ → own_accepted γsrv e []))%I).
  iDestruct (big_sepS_impl with "Hunused []") as "Hunused".
  {
    instantiate (1:=(λ e, (F1 e ∗ F3 e) ∗ F2 e)%I).
    iModIntro.
    iIntros (??) "Hwand".
    unfold F1. unfold F2. unfold F3.
    destruct (decide (uint.nat x < uint.nat newEpoch)).
    {
      iSplitL "Hwand".
      {
        iSplitL "Hwand".
        { iIntros. iApply "Hwand". word. }
        { iIntros. exfalso. word. }
      }
      { iIntros. exfalso. word. }
    }
    {
      destruct (decide (uint.nat x = uint.nat newEpoch)).
      {
        iSplitL "Hwand".
        {
          iSplitR "Hwand".
          { iIntros. exfalso. word. }
          { iIntros. iApply "Hwand". word. }
        }
        { iIntros. exfalso. word. }
    }
    {
      assert (uint.nat x > uint.nat newEpoch) by word.
      iSplitR "Hwand".
      {
        iSplitL.
        { iIntros. exfalso. word. }
        { iIntros. exfalso. word. }
      }
      { iIntros. iApply "Hwand". word. }
    }
    }
  }
  simpl.
  iDestruct (big_sepS_sep with "Hunused") as "[Hunused HunusedNew]".
  unfold F2.
  iDestruct (big_sepS_sep with "Hunused") as "[Hunused HunusedSingle]".
  (* Now, we can do whatever we want with Hunused (F1); let's freeze it all! *)

  set (G1:=(λ (e:u64),
        |==> (⌜uint.nat e > uint.nat st.(mp_epoch)⌝
          → ⌜uint.nat e < uint.nat newEpoch⌝ -∗
          is_accepted_ro γsrv e [])%I
                  )%I).
  iDestruct (big_sepS_impl with "Hunused []") as "Hunused".
  {
    iModIntro.
    instantiate (1:=G1).
    iIntros (??) "Hwand".
    unfold F1.
    unfold G1.

    destruct (decide (uint.nat st.(mp_epoch) < uint.nat x)); last first.
    {
      iModIntro.
      iIntros. exfalso; word.
    }
    destruct (decide (uint.nat x < uint.nat newEpoch)); last first.
    {
      iModIntro.
      iIntros. exfalso; word.
    }
    iSpecialize ("Hwand" with "[%//] [%//]").

    iMod (fmlist_ptsto_persist with "Hwand") as "$"; last done.
  }
  unfold G1.
  iMod (big_sepS_bupd with "Hunused") as "#Hunused".

  iDestruct (big_sepS_elem_of_acc_impl newEpoch with "HunusedSingle") as "[Hacc2 _]".
  { set_solver. }
  iSpecialize ("Hacc2" with "[%//]").
  iDestruct (big_sepS_elem_of_acc_impl newEpoch with "Hvotes") as "[Hvote Hvotes]".
  { set_solver. }
  iDestruct "Hvote" as "[%Hbad|Hvote]".
  { exfalso. word. }

  iAssert (|==> is_accepted_upper_bound γsrv st.(mp_log) st.(mp_acceptedEpoch) newEpoch)%I with "[Hacc Hunused]" as ">#Hacc_ub2".
  {
    destruct (decide _).
    { (* case: need to freeze *)
      iMod (fmlist_ptsto_persist with "Hacc") as "#Hacc_ro".
      iModIntro.
      iExists st.(mp_log).
      iSplit; first done.
      replace st.(mp_epoch) with st.(mp_acceptedEpoch) by word.
      iFrame "#".
      iModIntro.
      iIntros.
      iDestruct (big_sepS_elem_of_acc_impl epoch' with "Hunused") as "[Hunused2 _]".
      { set_solver. }
      iApply "Hunused2".
      { word. }
      { word. }
    }
    {
      iMod (fmlist_ptsto_persist with "Hacc") as "#Hacc_ro".
      iSpecialize ("Hacc_ub" with "[%]").
      { word. }
      iDestruct "Hacc_ub" as (?) "(%Hpre & #Hacc_ro2 & #Hacc_ub)".
      iExists _.
      iModIntro.
      iSplit; first iPureIntro.
      { done. }
      iFrame "Hacc_ro2".
      iModIntro.
      iIntros.
      destruct (decide (uint.nat epoch' < uint.nat st.(mp_epoch))).
      { iApply "Hacc_ub"; done. }
      assert (uint.nat st.(mp_epoch) ≤ uint.nat epoch') by word.

      iDestruct (big_sepS_elem_of_acc_impl epoch' with "Hunused") as "[Hunused2 _]".
      { set_solver. }
      destruct (decide (uint.nat epoch' = uint.nat st.(mp_epoch))).
      {
        replace (epoch') with (st.(mp_epoch)) by word.
        iFrame "#".
      }
      iApply "Hunused2".
      { word. }
      { word. }
    }
  }

  iModIntro.
  iFrame "Hvote".
  iFrame "Hprop_lb Hprop_facts Hacc_lb".
  simpl.
  destruct (decide _).
  { exfalso. word. }
  iFrame "Hacc2".
  iFrame "#".
  iSplitR; first iPureIntro.
  { word. }
  iSplitR; first done.
  iFrame "HunusedNew".
  iApply "Hvotes".
  {
    iModIntro.
    iIntros (???) "[%|$]".
    iLeft.
    word.
  }
  {
    iLeft.
    word.
  }
Qed.

(* Right order of allocation:
  Allocate the purely local state of each server. That determines `config`.
  Set up system state and is_repl_inv.
  Finish setting up local state, how that is_repl_inv is available.
*)

Lemma alloc_const_gmap {A:cmra} (a:A) `{H:inG Σ (gmapR u64 A)} :
  (✓a) →
    ⊢ |==> ∃ γ, [∗ set] epoch ∈ (fin_to_set u64), own γ {[ epoch := a ]}
.
Proof.
  intros Havalid.
  set (m:=(gset_to_gmap a (fin_to_set u64))).
  iMod (own_alloc m) as (γ) "H".
  { intros k. rewrite lookup_gset_to_gmap option_guard_True; last by apply elem_of_fin_to_set.
    rewrite Some_valid. done. }

  iAssert ([∗ set] epoch ∈ fin_to_set u64,
            own γ {[ epoch := a ]}
          )%I with "[H]" as "H".
  {
    rewrite -(big_opM_singletons m).
    rewrite big_opM_own_1.
    replace (fin_to_set u64) with (dom m); last first.
    { rewrite dom_gset_to_gmap. done. }
    iApply big_sepM_dom.
    iApply (big_sepM_impl with "H").
    iIntros "!#" (k x). subst m.
    rewrite lookup_gset_to_gmap_Some.
    iIntros ([_ [= <-]]).
    iIntros "$".
  }
  iModIntro.
  iExists _; iFrame.
Qed.

Definition own_server_pre γsrv : iProp Σ :=
  "Haccepted" ∷ own_accepted γsrv 0 [] ∗
  "Haccepted_rest" ∷ ([∗ set] e' ∈ (fin_to_set u64), ⌜uint.nat 0 < uint.nat e'⌝ →
                                                      own_accepted γsrv e' []) ∗
  "Hvotes" ∷ ([∗ set] epoch' ∈ (fin_to_set u64), own_vote_tok γsrv epoch')
.

Lemma paxos_ghost_server_pre_init :
  ⊢ |==> ∃ γsrv, own_server_pre γsrv ∗ is_accepted_lb γsrv (W64 0) []
.
Proof.
  iMod (fmlist_map_alloc_fin []) as (γacc) "Hacc".
  iMod (mono_nat_own_alloc 0) as (γepoch) "[Hepoch Hepoch_lb]".
  iDestruct (big_sepS_elem_of_acc_impl (W64 0) with "Hacc") as "[Hacc Haccrest]".
  { set_solver. }
  iDestruct (fmlist_ptsto_get_lb with "Hacc") as "#Hacc_lb".
  iMod (alloc_const_gmap (to_dfrac_agree (DfracOwn 1) ())) as (?) "Hvotes".
  { done. }

  iExists {| mp_accepted_gn := _ ; mp_vote_gn := _ |}.
  iModIntro.
  iFrame "∗#".
  iApply "Haccrest".
  {
    iModIntro.
    iIntros.
    iFrame.
  }
  {
    iIntros. exfalso. replace (uint.nat 0%Z) with 0 in H; word.
  }
Qed.

Definition is_sys_init_witness γsys : iProp Σ :=
  is_proposal_lb γsys (W64 0) [] ∗ is_proposal_facts γsys (W64 0) [].

Lemma paxos_system_init :
length config > 0 →
(∀ γsrv, ⌜γsrv ∈ config⌝ → is_accepted_lb γsrv (W64 0) []) ={⊤}=∗
    ∃ γsys,
    is_repl_inv γsys ∗
    is_vote_inv γsys ∗
    own_log γsys [] ∗
    is_sys_init_witness γsys
.
Proof.
  intros Hlen.
  iIntros "#Hacc".
  (* allocate ghost state, and establish is_repl_inv *)
  iMod (own_alloc (●ML [])) as "Hghost".
  { apply mono_list_auth_valid. }
  iDestruct "Hghost" as (γstate) "[Hghost Hghost2]".
  iMod (fmlist_map_alloc_fin []) as (γproposal) "Hproposal".

  (* set up proposal for epoch 0 *)
  iDestruct (big_sepS_elem_of_acc_impl (W64 0) with "Hproposal") as "[Hprop Hprop_rest]".
  { set_solver. }
  iDestruct (fmlist_ptsto_get_lb with "Hprop") as "#Hprop_lb".

  set  (γsys:= {|
      mp_proposal_gn := γproposal ;
      mp_state_gn := γstate;
    |}).
  iExists γsys.
  iFrame "∗".

  iAssert (is_proposal_facts γsys 0%Z []) with "[]" as "#Hprop_facts".
  {
    iSplit.
    {
      iIntros (???).
      exfalso.
      replace (uint.nat (W64 0)) with (0) in H by word.
      lia.
    }
    iModIntro.
    iIntros (??).
    iIntros "Hcom".
    apply prefix_nil_inv in H.
    rewrite H.
    iFrame.
    done.
  }

  iMod (inv_alloc with "[Hghost]") as "#$".
  { (* establish is_repl_inv *)
    iNext.
    iExists [], (W64 0).
    simpl.
    iFrame "∗#".
    iExists (set_seq 0 (length config)); iFrame "#".
    iSplitR.
    { iPureIntro. intros. apply elem_of_set_seq in H. lia. }
    iSplitR.
    { iPureIntro. intros. rewrite size_set_seq. lia. }
    iApply big_sepL_forall.
    iIntros.
    iApply "Hacc".
    iPureIntro.
    by eapply elem_of_list_lookup_2.
  }
  iMod (inv_alloc with "[Hprop_rest Hprop]") as "#$".
  {
    iNext.
    iApply "Hprop_rest".
    { iModIntro. iIntros. iFrame. }
    iFrame "Hprop".
  }
  iModIntro.
  iFrame "∗#".
Qed.

Lemma pb_ghost_server_init γsys γsrv :
  is_sys_init_witness γsys -∗
  own_server_pre γsrv
  -∗
  own_replica_ghost γsys γsrv (mkMPaxosState 0 0 [])
.
Proof.
  iIntros "[#Hprop_lb #Hfacts] Hown".
  iNamed "Hown".
  repeat iExists _.
  iDestruct (fmlist_ptsto_get_lb with "Haccepted") as "#Hacc_lb".
  iFrame "∗#%".
  simpl.
  iSplitR; first done.
  iSplitR.
  { iIntros (?). exfalso. lia. }
  iApply (big_sepS_impl with "Hvotes").
  iModIntro. iIntros. iFrame.
Qed.

End mpaxos_protocol.
