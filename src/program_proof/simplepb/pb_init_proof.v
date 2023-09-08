From Perennial.base_logic Require Import lib.saved_prop.
From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Export pb.
From Perennial.program_proof.simplepb Require Export pb_protocol.
From Perennial.program_proof.simplepb Require Import pb_definitions config_protocol_proof
     clerk_proof.
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
  [ (U64 0, ApplyAsBackup_spec γ γsrv) ;
    (U64 1, SetState_spec γ γsrv) ;
    (U64 2, GetState_spec γ γsrv) ;
    (U64 3, BecomePrimary_spec γ γsrv);
    (U64 4, Apply_spec γ);
    (U64 6, ApplyRo_spec γ);
    (U64 7, IncreaseCommit_spec γ γsrv)].

Lemma pb_host_init host γsys γsrv :
  host c↦ ∅ ={⊤}=∗
  is_pb_host host γsys γsrv.
Proof.
  iIntros "Hchan".
  iMod (alloc_is_urpc_list_pred host (pb_spec_list γsys γsrv) with "Hchan") as (γrpc) "H".
  { simpl. set_solver. }
  iModIntro.
  rewrite is_pb_host_unfold.
  iExists γrpc.
  simpl.
  iDestruct "H" as "(H1 & $ & $ & $ & $ & $ & $ & $ & _)".
  iExactEq "H1".
  f_equal.
  set_solver.
Qed.

Definition is_pb_sys_init_witness γ γsrv : iProp Σ :=
  is_sys_init_witness γ.(s_pb) ∗
  is_in_config γ γsrv (U64 0) ∗
  is_proposal_facts_prim γ.(s_prim) 0%Z []
.

Definition is_server_prealloc_witness γsrv : iProp Σ :=
  is_accepted_lb γsrv.(r_pb) (U64 0) [] ∗ is_epoch_lb γsrv.(r_pb) 0
.

Lemma prealloc_simplepb_server :
  ⊢ |={⊤}=> ∃ γsrv,
  is_server_prealloc_witness γsrv ∗
  (∀ γ, is_pb_sys_init_witness γ γsrv -∗ own_Server_ghost_f γ γsrv (U64 0) [] false).
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
    iExists [].
    iFrame.
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
  rewrite app_length /= in H.
  lia.
Qed.

Lemma alloc_simplepb_system γsrvs :
  length γsrvs > 0 →
  (∀ γsrv, ⌜γsrv ∈ γsrvs⌝ → is_accepted_lb γsrv.(r_pb) (U64 0) [] ∗ is_epoch_lb γsrv.(r_pb) 0)
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
  { by rewrite fmap_length. }
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
  iExists _; iFrame "#".
  iPureIntro.
  by apply elem_of_list_fmap_1.
Qed.

End pb_init_proof.
