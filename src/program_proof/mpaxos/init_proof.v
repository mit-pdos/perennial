From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv Require mpaxos.
From Perennial.program_proof.grove_shared Require Import urpc_proof urpc_spec.
From Perennial.program_proof.mpaxos Require Export definitions protocol_proof.

Section init_proof.
Context `{!gooseGlobalGS Σ}.
Context `{!mpG Σ}.

Definition is_mpaxos_sys_init_witness γ config N : iProp Σ :=
  is_sys_init_witness (config:=config) (N:=N) γ.(s_mp)
.

Definition is_mpaxos_server_prealloc_witness γsrv : iProp Σ :=
  is_accepted_lb γsrv (U64 0) [].

Lemma prealloc_mpaxos_server :
  ⊢ |={⊤}=> ∃ γsrv,
  is_mpaxos_server_prealloc_witness γsrv ∗
  (∀ γ (p:mpaxosParams.t Σ),
     is_mpaxos_sys_init_witness γ p.(mpaxosParams.config) p.(mpaxosParams.N) -∗
        own_file_inv γ γsrv []).
Proof.
  (* iMod (pb_ghost_server_pre_init) as (γpb) "(Hpre & #? & #?)".
  iMod (alloc_primary_protocol_server) as (γprim) "Hprim".
  iExists {| r_pb := γpb ; r_prim := γprim |}.
  iModIntro. iFrame "#".
  iIntros (?) "#(? & ? & ?)".
  iDestruct (pb_ghost_server_init with "[$] [$]") as "H".
  by iExists _; iFrame "∗#". *)
Admitted.

(* Invariants:
   is_repl_inv
   is_vote_inv
   is_helping_inv
 *)

Lemma alloc_mpaxos_helping_inv {p:mpaxosParams.t Σ} γ :
  own_log γ.(s_mp) [] -∗ own_state γ p.(mpaxosParams.initstate)
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

Lemma alloc_mpaxos_system γsrvs init N Pwf :
  length γsrvs > 0 →
  (∀ γsrv, ⌜γsrv ∈ γsrvs⌝ → is_mpaxos_server_prealloc_witness γsrv)
  ={⊤}=∗
  let params:=(mpaxosParams.mk Σ γsrvs init Pwf N) in
  ∃ γ,
   is_helping_inv γ ∗
   is_vote_inv (config:=γsrvs) (N:=N) γ.(s_mp) ∗
   is_repl_inv (config:=γsrvs) (N:=N) γ.(s_mp) ∗
   own_state γ init ∗
   is_mpaxos_sys_init_witness γ γsrvs N
.
Proof.
  (* iIntros (?) "#Hpre".
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
  by apply elem_of_list_fmap_1. *)
Admitted.

Context `{Hparams:!mpaxosParams.t Σ}.
Import mpaxosParams.

Definition pb_spec_list γ γsrv :=
  [ (U64 0, applyAsFollower_spec γ γsrv) ;
    (U64 1, enterNewEpoch_spec γ γsrv) ;
    (U64 2, becomeLeader_spec)
  ]
.

Lemma mpaxos_host_init host γsys γsrv :
  host c↦ ∅ ={⊤}=∗
  is_mpaxos_host host γsys γsrv.
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

End init_proof.
