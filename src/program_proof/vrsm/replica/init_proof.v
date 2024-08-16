From Perennial.base_logic Require Import lib.saved_prop.
From Perennial.program_proof Require Import grove_prelude.
From Perennial Require Import replica.definitions
     replica.config_protocol_proof configservice.config_proof.
From Perennial.program_proof.grove_shared Require Import urpc_proof.
From iris.algebra Require Import mono_list.

Section pb_init_proof.

Context {params:pbParams.t}.
Import pbParams.
Notation OpType := (Sm.OpType pb_record).
Notation has_op_encoding := (Sm.has_op_encoding pb_record).
Notation has_snap_encoding := (Sm.has_snap_encoding pb_record).
Notation compute_reply := (Sm.compute_reply pb_record).
Context `{!gooseGlobalGS Σ}.
Context `{!pbG Σ}.

Definition pb_spec_list γ γsrv :=
  [ (W64 0, ApplyAsBackup_spec γ γsrv) ;
    (W64 1, SetState_spec γ γsrv) ;
    (W64 2, GetState_spec γ γsrv) ;
    (W64 3, BecomePrimary_spec γ γsrv);
    (W64 4, Apply_spec γ);
    (W64 6, ApplyRo_spec γ);
    (W64 7, IncreaseCommit_spec γ γsrv)].

Lemma alloc_pb_rpcs host γsys γsrv :
  host c↦ ∅ ={⊤}=∗
  is_pb_rpcs host γsys γsrv.
Proof.
  iIntros "Hchan".
  iMod (alloc_is_urpc_list_pred host (pb_spec_list γsys γsrv) with "Hchan") as (γrpc) "H".
  { simpl. set_solver. }
  iModIntro.
  rewrite is_pb_rpcs_unfold.
  iExists γrpc.
  simpl.
  iDestruct "H" as "(H1 & $ & $ & $ & $ & $ & $ & $ & _)".
  iExactEq "H1".
  f_equal.
  set_solver.
Qed.

(* FIXME: make this global, not per-server by changing how to initialize idle replica servers *)
Definition is_pb_sys_init_witness γ γsrv : iProp Σ :=
  is_sys_init_witness γ.(s_pb) ∗
  is_in_config γ γsrv (W64 0) ∗
  is_proposal_facts_prim γ.(s_prim) 0%Z []
.

Definition is_server_prealloc_witness γsrv : iProp Σ :=
  is_accepted_lb γsrv.(r_pb) (W64 0) [] ∗ is_epoch_lb γsrv.(r_pb) 0
.

Lemma prealloc_simplepb_server :
  ⊢ |={⊤}=> ∃ γsrv,
  is_server_prealloc_witness γsrv ∗
  (∀ γ, is_pb_sys_init_witness γ γsrv -∗ own_Server_ghost_f γ γsrv (W64 0) [] false).
Proof.
  iMod (pb_ghost_server_pre_init) as (γpb) "(Hpre & #? & #?)".
  iMod (alloc_primary_protocol_server) as (γprim) "Hprim".
  iExists {| r_pb := γpb ; r_prim := γprim |}.
  iModIntro. iFrame "#".
  iIntros (?) "#(? & ? & ?)".
  iDestruct (pb_ghost_server_init with "[$] [$]") as "H".
  by iExists _; iFrame "∗#".
Qed.
(* Invariants:
   is_repl_inv
   is_preread_inv
   is_helping_inv
   is_conf_inv
 *)

Lemma alloc_helping_inv γ :
  own_pre_log γ.(s_prelog) [] -∗ own_int_log γ []
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

Lemma alloc_simplepb_last γsrvs :
  length γsrvs > 0 →
  (∀ γsrv, ⌜γsrv ∈ γsrvs⌝ → is_accepted_lb γsrv.(r_pb) (W64 0) [] ∗ is_epoch_lb γsrv.(r_pb) 0)
  ={⊤}=∗ ∃ γ,
  is_pb_system_invs γ ∗
  own_op_log γ [] ∗
  (∀ γsrv, ⌜γsrv ∈ γsrvs⌝ → is_pb_sys_init_witness γ γsrv) ∗
  pb_init_for_config γ.(s_pb) (r_pb <$> γsrvs) ∗
  primary_init_for_config γ.(s_prim) ∗
  is_proph_read_inv γ
.
Proof.
  iIntros (?) "#Hpre".
  iMod alloc_primary_protocol as (γprim) "[Hprim #HprimWit]".
  iMod (pb_system_init (r_pb <$> γsrvs) with "[]") as (γpb) "Hpb".
  { by rewrite length_fmap. }
  { iIntros.
    apply elem_of_list_fmap_2 in H0 as (? & ? & ?); subst.
    by iApply "Hpre". }
  iDestruct "Hpb" as "(#Hrep & Hlog & Hinit & #Hwit)".
  iMod (alloc_pb_preread_protocol with "Hlog") as (γprelog γreads) "[#Hpreread Hlog]".
  iMod (own_alloc (●ML [])) as (γintlog) "[Hintlog Hintlog2]".
  { apply mono_list_auth_valid. }
  iMod (own_alloc (●ML [])) as (γoplog) "[Hoplog Hoplog2]".
  { apply mono_list_auth_valid. }

  set (γ:={| s_pb:=γpb ; s_prim:=γprim ; s_prelog := γprelog ; s_internal_log := γintlog ;
             s_reads:=γreads ; s_log := γoplog
          |}).
  iMod (alloc_helping_inv γ with "Hlog Hintlog2") as "#Hhelp".
  iAssert (|={⊤}=> is_proph_read_inv γ)%I with "[Hintlog Hoplog2]" as ">#Hproph_read_inv".
  { iApply (inv_alloc with "[Hintlog Hoplog2]").
    iExists _; iFrame. }
  iModIntro. iExists γ.
  iNamed "Hinit".
  iFrame "∗ His_conf #".
  iIntros.
  iExists _. iFrame "His_conf_prop".
  iPureIntro.
  by apply elem_of_list_fmap_1.
Qed.

Lemma alloc_simplepb_system (configHostPairs: list (u64 * u64)) (extrahosts: list u64) :
  extrahosts = [] → (* FIXME: get rid of this assumption *)
  length initconf > 0 →
  length configHostPairs > 0 →
  ([∗ list] h ∈ (initconf ++ extrahosts), h c↦ ∅) -∗
  ([∗ list] h ∈ configHostPairs, h.1 c↦ ∅ ∗ h.2 c↦ ∅)
  ={⊤}=∗
  ∃ γ,
  (* committed log of operations *)
   own_op_log γ [] ∗
   is_pb_config_hosts configHostPairs.*1 γ ∗

  (* for each pb replica server:  *)
  ([∗ list] host ∈ initconf ++ extrahosts,
     ∃ γsrv,
     is_pb_host host γ γsrv ∗
     (own_Server_ghost_f γ γsrv 0 [] false)
  ) ∗

  (* for each config paxos server:  *)
  ([∗ list] configHostPair ∈ configHostPairs,
    ∃ γconf γconfsrv params,
    ⌜ params.(configParams.initconfig) = initconf ⌝ ∗
    is_config_server_host configHostPair.1 configHostPair.2 γconf γconfsrv ∗
    is_config_peers (configHostPairs.*2) γconf ∗
    (□ configParams.Pwf configParams.initconfig) ∗
    config_crash_resources γconf γconfsrv []
  )
.
Proof.
  intros.
  iIntros "Hchans HconfChans".
  subst. rewrite app_nil_r.
  iAssert (|={⊤}=> [∗ list] h ∈ initconf (* ++ extrahosts*),
             ∃ γsrv,
           is_server_prealloc_witness γsrv ∗
           (∀ γ, is_pb_sys_init_witness γ γsrv -∗ own_Server_ghost_f γ γsrv (W64 0) [] false)
           )%I with "[]" as ">Hpresrvs".
  {
    iApply big_sepL_fupd. iApply big_sepL_impl.
    { by iApply big_sepL_emp. }
    iIntros "!# * _ _".
    iMod prealloc_simplepb_server as (?) "H".
    by iExists _; iFrame.
  }
  iDestruct (big_sepL_exists_to_sepL2 with "Hpresrvs") as (γsrvs) "Hpresrvs".
  iDestruct (big_sepL2_sep with "Hpresrvs") as "[#Hwits Hpresrvs]".
  (* iDestruct (big_sepL2_app_inv_l with "Hwits") as (γsrvs ? _) "[#Hwits _]". *)
  iDestruct (big_sepL2_length with "Hwits") as %Hlength.

  iMod (alloc_simplepb_last γsrvs with "[]") as (γ) "H".
  { lia. }
  {
    iIntros.
    iDestruct (big_sepL2_const_sepL_r with "Hwits") as "[_ Hwits2]".
    by iDestruct (big_sepL_elem_of with "Hwits2") as "$".
  }

  iClear "Hwits".
  iDestruct "H" as "(#HsysInvs & Hlog & #HinitWits & Hconf & Hprim & #Hproph)".
  iDestruct (big_sepL2_impl with "Hpresrvs []") as "Hpresrvs".
  {
    iModIntro. iIntros "* % % H".
    iSpecialize ("H" $! γ).
    iAccu.
  }
  simpl.
  iDestruct (big_sepL2_wand with "[] Hpresrvs") as "Hsrvs".
  {
    iApply big_sepL2_forall.
    iSplitR; first done.
    iIntros.
    iApply "HinitWits".
    iPureIntro.
    by eapply elem_of_list_lookup_2.
  }
  iExists γ.
  iFrame "Hlog".
  rewrite sep_comm. repeat rewrite -sep_assoc.
  iAssert (|={⊤}=> [∗ list] h; γsrv ∈ params.(initconf); γsrvs, is_pb_host h γ γsrv)%I with "[Hchans]" as ">#Hrpcs".
  {
    iApply big_sepL2_fupd.
    iDestruct (big_sepL2_const_sepL_l with "[$Hchans]") as "HH".
    { done. }
    iDestruct (big_sepL2_impl with "HH []") as "$".
    iIntros "!# * % % H".
    iMod (alloc_pb_rpcs with "[$]") as "$".
    by iFrame "HsysInvs".
  }
  iSplitL "Hsrvs".
  {
    iModIntro.
    iDestruct (big_sepL2_sep with "[$Hsrvs $Hrpcs]") as "HH".
    iDestruct (big_sepL2_to_sepL_1 with "HH") as "HH".
    iApply (big_sepL_impl with "HH").
    iIntros "!# * %Hlookup H".
    iDestruct "H" as (?) "[_ [? ?]]".
    iExists _; iFrame.
  }
  set (p:=toConfigParams γ).
  iMod (alloc_config_system p configHostPairs with "HconfChans []") as "H".
  { done. }
  { iModIntro.
    simpl.
    iExists _.
    iApply big_sepL2_flip.
    iFrame "Hrpcs".
  }
  iDestruct "H" as (γconf) "(Hsrvs & #HconfHosts & Hres)".
  iSplitL "Hsrvs".
  {
    iApply (big_sepL_impl with "Hsrvs").
    iIntros "!> !# * %Hlookup H".
    iDestruct "H" as (?) "(#Hpeers & Hhost & Hcrash)".
    repeat iExists _; iFrame "∗#".
    iSplitR.
    { done. }
    iModIntro.
    simpl. iExists _.
    iApply big_sepL2_flip.
    iFrame "Hrpcs".
  }
  repeat iExists _.
  iFrame "#".
  iMod (inv_alloc with "[-]") as "$"; last done.
  iNext.
  repeat iExists _.
  iDestruct "Hres" as "(? & ? & ?)".
  iNamed "Hconf".
  rewrite /primary_init_for_config /pb_init_for_config.
  iFrame "∗ His_conf #".
  iSplitR; first done.
  iSplitR.
  {
    iApply big_sepL2_flip.
    iFrame "Hrpcs".
  }
  iSplitL "Hunused Hprim".
  {
    iDestruct (big_sepS_sep with "[$Hunused $Hprim]") as "HH".
    iApply (big_sepS_impl with "HH").
    iIntros "!# * % [H1 H2] %".
    iSpecialize ("H1" with "[//]").
    iSpecialize ("H2" with "[//]").
    iFrame.
  }
  iSplitR.
  { by iRight. }
  iIntros (???).
  exfalso. word.
Qed.

End pb_init_proof.
