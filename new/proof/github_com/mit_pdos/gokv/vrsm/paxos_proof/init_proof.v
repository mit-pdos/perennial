From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.grove_shared Require Import urpc_proof urpc_spec.
From Perennial Require Export paxos.definitions paxos.protocol_proof.

Section init_proof.
Context `{!gooseGlobalGS Σ}.
Context `{!paxosG Σ}.
Import paxosParams.

Context (params:paxosParams.t Σ).
Definition is_paxos_sys_init_witness γ : iProp Σ :=
  "#Hinit" ∷ is_sys_init_witness (config:=γ.(s_hosts)) (N:=N) γ.(s_mp) ∗
  "#Hhelp" ∷ is_helping_inv γ ∗
  "#Hvote" ∷ is_vote_inv (config:=γ.(s_hosts)) (N:=N) γ.(s_mp) ∗
  "#Hrepl" ∷ is_repl_inv (config:=γ.(s_hosts)) (N:=N) γ.(s_mp) ∗
  "#Hpwf" ∷ □ params.(Pwf) params.(initstate)
.

Definition is_paxos_server_prealloc_witness γsrv : iProp Σ :=
  is_accepted_lb γsrv (W64 0) [].

Lemma prealloc_paxos_server :
  ⊢ |={⊤}=> ∃ γsrv,
  is_paxos_server_prealloc_witness γsrv ∗
  (∀ γ, is_paxos_sys_init_witness γ -∗ own_file_inv γ γsrv []).
Proof.
  iMod (paxos_ghost_server_pre_init) as (γpb) "(Hpre & #?)".
  iExists _.
  iModIntro. iFrame "#".
  iIntros (?) "H". iNamed "H".
  iDestruct (pb_ghost_server_init with "[$] [$]") as "H".
  rewrite /own_file_inv.
  iExists _.
  iSplitR.
  { iPureIntro. right. done. }
  iExists _; iFrame "∗#".
  simpl.
  iPureIntro.
  done.
Qed.

Lemma alloc_paxos_helping_inv γ :
  own_log γ.(s_mp) [] -∗ own_state γ initstate
  ={⊤}=∗ is_helping_inv γ.
Proof.
  iIntros "Hprelog Hint_log".
  iMod (inv_alloc with "[-]") as "$"; last done.
  iNext.
  iExists [].
  iFrame.
  iSplitL.
  {
    iSplitR; first done.
    iApply big_sepL2_nil.
    done.
  }
  iModIntro.
  iIntros.
  exfalso.
  rewrite H0 in H.
  apply prefix_nil_inv in H.
  apply (f_equal length) in H.
  rewrite length_app /= in H.
  lia.
Qed.

Lemma alloc_paxos_last γsrvs :
  length γsrvs > 0 →
  □ params.(Pwf) params.(initstate) -∗
  (∀ γsrv, ⌜γsrv ∈ γsrvs⌝ → is_paxos_server_prealloc_witness γsrv)
  ={⊤}=∗
  ∃ γ,
   ⌜ γ.(s_hosts) = γsrvs ⌝ ∗
   is_helping_inv γ ∗
   is_vote_inv (config:=γsrvs) (N:=N) γ.(s_mp) ∗
   is_repl_inv (config:=γsrvs) (N:=N) γ.(s_mp) ∗
   own_state γ initstate ∗
   is_paxos_sys_init_witness γ
.
Proof.
  intros.
  iIntros "#Hpwf #Hpre".
  iMod (paxos_system_init (config:=γsrvs) with "[]") as (γpb) "Hpb".
  { done. }
  { iIntros. by iApply "Hpre". }
  iDestruct "Hpb" as "(#Hrep & #Hvote & Hlog & Hinit & #Hwit)".
  iMod (own_alloc (dfrac_agree.to_dfrac_agree (DfracOwn 1) (initstate : (leibnizO (list u8))))) as (γst_gn) "Hst".
  { done. }
  rewrite -Qp.half_half.
  rewrite -dfrac_op_own.
  rewrite dfrac_agree.dfrac_agree_op.
  iDestruct "Hst" as "[Hst Hst2]".

  set (γ:={| s_st:=γst_gn; s_mp := γpb ; s_hosts := γsrvs |}).
  iMod (alloc_paxos_helping_inv γ with "[$Hlog] [$Hst2]") as "#Hhelp".
  iModIntro. iExists γ.
  iFrame "∗ #".
  done.
Qed.

Definition pb_spec_list γ γsrv :=
  [ (W64 0, applyAsFollower_spec γ γsrv) ;
    (W64 1, enterNewEpoch_spec γ γsrv) ;
    (W64 2, becomeLeader_spec)
  ]
.

Lemma paxos_host_init host γsys γsrv :
  host c↦ ∅ ={⊤}=∗
  is_paxos_host host γsys γsrv.
Proof.
  iIntros "Hchan".
  iMod (alloc_is_urpc_list_pred host (pb_spec_list γsys γsrv) with "Hchan") as (γrpc) "H".
  { simpl. set_solver. }
  iModIntro.
  iExists γrpc.
  simpl.
  iDestruct "H" as "(H1 & $ & $ & $ & _)".
  iApply to_named.
  iExactEq "H1".
  f_equal.
  set_solver.
Qed.

Lemma alloc_paxos_system (hosts: list u64):
  length hosts > 0 →
  ([∗ list] h ∈ hosts, h c↦ ∅) -∗
  □ (Pwf initstate)
  ={⊤}=∗
  ∃ γ,
    ([∗ list] host ∈ hosts, ∃ γsrv, is_paxos_server_host host γ γsrv ∗
                                    own_file_inv γ γsrv []) ∗
    is_paxos_hosts hosts γ ∗
    own_state γ initstate
.
Proof.
  intros.
  iIntros "Hchan #Hwf".
  iAssert (|={⊤}=> [∗ list] h ∈ hosts,
             ∃ γsrv, is_paxos_server_prealloc_witness γsrv ∗
                     (∀ γ, is_paxos_sys_init_witness γ -∗ own_file_inv γ γsrv []))%I with "[]" as ">H".
  {
    iMod (big_sepL_fupd _ _ hosts with "[]") as "$"; last done.
    iApply (big_sepL_impl with "[]").
    { by iApply big_sepL_emp. }
    iIntros "!# * %Hlookup _".
    by iMod (prealloc_paxos_server) as "$".
  }
  iDestruct (big_sepL_exists_to_sepL2 with "H") as (γsrvs) "H".
  iDestruct (big_sepL2_sep with "H") as "[#Hwits Hsrvs]".
  iDestruct (big_sepL2_length with "Hsrvs") as %Hlength.
  iMod (alloc_paxos_last γsrvs with "[] []") as "H".
  { lia. }
  { iFrame "#". }
  {
    iIntros.
    iDestruct (big_sepL2_const_sepL_r with "Hwits") as "[_ Hwits2]".
    by iDestruct (big_sepL_elem_of with "Hwits2") as "$".
  }
  iClear "Hwits".
  iDestruct "H" as (?) "(%Heq & #Hhelp & #Hvote & #Hrepl & Hst & #HinitWits)".
  subst.
  iExists _.
  iFrame.
  iAssert (|={⊤}=> [∗ list] h ; γsrv ∈ hosts ; γ.(s_hosts), is_paxos_server_host h γ γsrv)%I
          with "[Hchan]" as ">#Hhosts".
  {
    iApply big_sepL2_fupd.
    iDestruct (big_sepL2_const_sepL_l with "[$Hchan]") as "Hchan".
    { iPureIntro. exact Hlength. }
    iApply (big_sepL2_impl with "Hchan").
    iIntros "!# * % % H".
    iFrame "#".
    by iMod (paxos_host_init with "[$]") as "$".
  }
  iDestruct (big_sepL2_sep with "[$Hsrvs $Hhosts]") as "Hsrvs".
  iDestruct (big_sepL2_to_sepL_1 with "Hsrvs") as "Hsrvs".
  iSplitL.
  2:{
    rewrite /is_paxos_hosts.
    iModIntro.
    iApply (big_sepL2_impl with "Hhosts").
    iIntros "!# * % % [? ?]". iFrame.
  }
  iApply (big_sepL_impl with "Hsrvs").
  iIntros "!> !# * % H".
  iDestruct "H" as (??) "(Hfin & Hhost)".
  iExists _; iFrame.
  iApply "Hfin". iFrame "#".
Qed.

End init_proof.

