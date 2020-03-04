From Perennial.goose_lang.examples Require Import append_log.
From Perennial.goose_lang.lib Require Import encoding crash_lock.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof Require Import disk_lib.
From Perennial.program_proof Require Import marshal_proof.
From Perennial.program_proof Require Import append_log_proof.
From Perennial.goose_lang.ffi Require Import append_log_ffi.
From Perennial.program_logic Require Import ghost_var.

Canonical Structure log_stateO := leibnizO log_state.

Section hocap.
Context `{!heapG Σ}.
Context `{!crashG Σ}.
Context `{!lockG Σ, stagedG Σ}.
Context `{Hin: inG Σ (authR (optionUR (exclR log_stateO)))}.

Implicit Types v : val.
Implicit Types z : Z.
Implicit Types s : Slice.t.
Implicit Types (stk:stuckness) (E: coPset).

Context (Nlog: namespace).

Context (P: log_state -> iProp Σ).
Context (PHasOpened: iProp Σ).
(*
Context (Pinit_token: iProp Σ).
Context (Popen_token: iProp Σ).
Context (Pinit_non_open: ∀ l bs, P (Opened bs l) ∗ Pinit_token ={⊤}=∗ False).
Context (Pinit_non_closed: ∀ bs, P (Closed bs) ∗ Pinit_token ={⊤}=∗ False).
Context (Popen_non_uninit: P (UnInit) ∗ Popen_token ={⊤}=∗ False).
*)

Definition N1 := Nlog.@"lock".
Definition N2 := Nlog.@"crash".
Definition N := Nlog.@"inv".

Definition log_init : iProp Σ :=
  (P UnInit ∗ uninit_log) ∨ (∃ vs, P (Closed vs) ∗ crashed_log vs).

Definition log_state_to_crash (s: log_state) :=
  match s with
  | UnInit => uninit_log
  | Initing => (uninit_log ∨ crashed_log [])
  | Closed vs => crashed_log vs
  | Opening vs => (crashed_log vs)
  | Opened vs l => (crashed_log vs)
  end%I.

Definition log_crash_cond : iProp Σ :=
  ∃ (s: log_state), log_state_to_crash s ∗ P s.

Definition log_inv_inner k γ1 : iProp Σ :=
             (crash_inv_full N2 k ⊤ γ1 (log_crash_cond) (log_crash_cond) ∨ PHasOpened)%I.

Definition log_inv k :=
  (∃ γ1, inv N (log_inv_inner (LVL k) γ1))%I.

Lemma append_log_crash_inv_obligation e (Φ: val → iProp Σ) Φc E k k':
  (k' < k)%nat →
  log_init -∗
  (log_inv k' -∗ (WPC e @ NotStuck; LVL k; ⊤; E {{ Φ }} {{ Φc }})) -∗
  WPC e @ NotStuck; (LVL (S k)); ⊤; E {{ Φ }} {{ Φc ∗ log_crash_cond }}%I.
Proof.
  iIntros (?) "Hinit Hwp".
  iMod (crash_inv_alloc N2 (LVL k') ⊤ ⊤ (log_crash_cond) (log_crash_cond) with "[Hinit]") as
      (γ1) "(Hfull&Hpending)".
  { rewrite /log_init/log_crash_cond.
    iDestruct "Hinit" as "[(HP&Hinit)|Hinit]".
    - iSplitL "HP Hinit".
      { iNext. iExists _. iFrame => //=. }
      iAlways. iIntros. eauto.
    - iDestruct "Hinit" as (?) "(HP&Hinit)".
      iSplitL "HP Hinit".
      { iNext. iExists _. iFrame => //=. }
      iAlways. iIntros. eauto.
  }
  iApply (wpc_crash_inv_init _ k k' N2 ⊤ E with "[-]"); try assumption.
  { set_solver +. }
  iFrame.
  iMod (inv_alloc N _ (log_inv_inner _ _) with "[Hfull]") as "#?".
  { iIntros "!>". rewrite /log_inv_inner. iLeft. iFrame. }
  iApply ("Hwp" with "[]").
  { iExists _. eauto. }
Qed.

Definition is_log (k: nat) (l: loc) : iProp Σ :=
  ∃ lk,
  log_inv k ∗
  inv Nlog (∃ q, l ↦[Log.S :: "m"]{q} lk) ∗
  (∃ γlk, is_crash_lock N1 N2 (LVL k) γlk lk
                                (∃ bs, ptsto_log l bs ∗ P (Opened bs l))
                                (∃ bs, crashed_log bs ∗ (P (Opened bs l) ∨ P (Closed bs)))).

Instance is_log_persistent: Persistent (is_log k l).
Proof. apply _. Qed.

(* XXX: For these crash hocap specs, P (Closed bs) might be slightly
   confusing...  It is not yet "crashed", merely halted? *)

Theorem wpc_Log__Reset k k' E2 l Q Qc:
  ↑N ⊆ E2 →
  (S k < k')%nat →
  {{{ is_log k' l ∗
     ((∀ bs, (P (Opened bs l) ={⊤ ∖↑ N2}=∗ P (Opened [] l) ∗ Q) ∧
             (P (Opened bs l) ={∅}=∗ P (Closed []) ∗ Qc)) ∧ Qc) ∗
     □ (Q -∗ Qc)
  }}}
    Log__Reset #l @ NotStuck; (LVL (S (S k))); ⊤; E2
  {{{ RET #() ; Q }}}
  {{{ Qc }}}.
Proof.
  iIntros (?? Φ Φc) "(His_log&Hvs&#HQ_to_Qc) HΦ".
  iDestruct "His_log" as (?) "H".
  iDestruct "H" as "(#Hlog_inv&Hm&His_lock)".
  iMod (inv_readonly_acc _ with "Hm") as (q) "Hm"; first by set_solver+.
  iDestruct "His_lock" as (γlk) "His_lock".
  rewrite /Log__Reset.
  wpc_pures; auto.
  { iDestruct "Hvs" as "(_&$)". }

  wpc_bind (struct.loadF _ _ _).
  wpc_frame "HΦ Hvs".
  { iIntros "((H&_)&(_&Hvs))". by iApply "H". }
  wp_loadField.
  iIntros "(HΦ&Hvs)".

  wpc_bind (lock.acquire _).
  wpc_frame "HΦ Hvs".
  { iIntros "((H&_)&(_&Hvs))". by iApply "H". }
  wp_apply (crash_lock.acquire_spec with "His_lock"); first by set_solver+.
  iIntros "H". iDestruct "H" as (Γ) "Hcrash_locked".
  iIntros "(HΦ&Hvs)".

  wpc_pures; auto.
  { iDestruct "Hvs" as "(_&$)". }
  wpc_bind (Log__reset _).
  replace E2 with (∅ ∪ E2) by set_solver.
  iApply (use_crash_locked with "[$]"); eauto.
  iSplit.
  { iDestruct "Hvs" as "(_&H)". iDestruct "HΦ" as "(HΦ&_)".
    by iApply "HΦ". }

  iIntros "H". iDestruct "H" as (bs) "(Hpts&HP)".
  iApply wpc_fupd.
  iApply wpc_fupd_crash_shift'.
  wpc_apply (wpc_Log__reset with "[$] [-]").
  iSplit.
  { iIntros "H".
    iDestruct "H" as "[H|H]".
    * iDestruct "Hvs" as "(_&Hvs)".
      iModIntro.
      iSplitL "HΦ Hvs".
      ** iDestruct "HΦ" as "(H&_)". by iApply "H".
      ** iExists bs. iFrame.
    * iDestruct "Hvs" as "(Hvs&_)".
      iDestruct ("Hvs" $! bs) as "(_&Hvs)".
      iMod ("Hvs" with "[$]") as "(Hclo&HQc)".
      iModIntro.
      iSplitL "HΦ HQc".
      ** iDestruct "HΦ" as "(H&_)". by iApply "H".
      ** iExists []. iFrame.
  }
  iNext. iIntros "Hpts".
  (* Linearization point *)
  iDestruct "Hvs" as "(Hvs&_)".
  iDestruct ("Hvs" $! bs) as "(Hvs&_)".
  iMod ("Hvs" with "[$]") as "(HP&HQ)".
  iSplitR "Hpts HP"; last first.
  { iExists _; iFrame. eauto. }
  iModIntro. iIntros.
  iSplit; last first.
  { iApply "HΦ"; by iApply "HQ_to_Qc". }
  wpc_pures.
  { by iApply "HQ_to_Qc". }

  wpc_frame "HQ HΦ".
  { iIntros "(?&H)"; iApply "H". by iApply "HQ_to_Qc". }

  wp_bind (struct.loadF _ _ _).
  wp_loadField.
  wp_apply (crash_lock.release_spec with "[$]"); eauto.
  iIntros "(HQ&HΦ)".
  by iApply "HΦ".
Qed.

(*
Definition is_pre_log (k: nat) : iProp Σ :=
  ∃ γ γ', staged_inv Npre (LVL k) (⊤ ∖ ↑Npre) (⊤ ∖ ↑Npre) γ γ' log_crash_inner ∗
          inv Ntok (staged_value Npre γ (P UnInit ∗ uninit_log) True).

Lemma alloc_pre_lock_uninit k k' E Φ Φc e:
  (k' < k)%nat →
  Φc ∗
  P UnInit ∗
  uninit_log ∗
  (Φc -∗ is_pre_log k' -∗ WPC e @ (LVL k); ⊤; E {{ Φ }} {{ Φc }}) -∗
  WPC e @ (LVL (S k)); ⊤; E {{ Φ }} {{ Φc ∗ ((P UnInit ∗ uninit_log) ∨ (∃ bs, P (Closed bs) ∗ crashed_log bs))}}.
Proof.
  iIntros (?) "(HΦc&HP&Hlog&Hwp)".
  iMod (staged_inv_alloc Npre (LVL k') ⊤ (⊤ ∖ ↑Npre) log_crash_inner (P UnInit ∗ uninit_log)
                         True%I with "[HP Hlog]") as
      (γ1 γ2) "(#Hstaged_inv&Hstaged_val&Hpending)".
  { rewrite /log_crash_inner. iFrame. iAlways. iIntros.
    iFrame. }
  iApply (wpc_ci_inv _ k k' Npre ⊤ E with "[-]"); try assumption.
  { set_solver +. }
  iFrame. iFrame "Hstaged_inv".
  iMod (inv_alloc Ntok _ (staged_value Npre γ1 (P UnInit ∗ uninit_log) True)%I
          with "[Hstaged_val]").
  { iFrame. }
  iApply ("Hwp" with "[$]").
  iExists _, _. iFrame "Hstaged_inv". iFrame.
Qed.
*)

(*
Theorem wpc_Open' k k' E2 Qc:
  (S k < k')%nat →
  {{{ log_inv k' ∗ ((∀ (s: log_state), ⌜ s ≠ UnInit ⌝ -∗ P s ={⊤}=∗ False) ∧ (PHasOpened ={⊤ ∖ ↑N}=∗ False) ∧
                     (P UnInit ={⊤ ∖ ↑N2}=∗ P Initing ∗ (∀ vs l, P Initing ={⊤ ∖ ↑N2}=∗ P (Opened l vs)))) }}}
    Open #() @ NotStuck; LVL (S (S k)); ⊤; E2
  {{{ lptr, RET #lptr; is_log k' lptr }}}
  {{{ Qc }}}.
Proof.
  iIntros (? Φ Φc) "(#Hlog_inv&Hvs) HΦ".
  iApply wpc_fupd.
  rewrite /log_inv.
  iDestruct "Hlog_inv" as (γ1 γ2) "(#Hc_inv&#Hinv)".
  iApply wpc_step_fupd'; first done.
  iInv "Hinv" as "Hinner" "Hclo".
  iMod (fupd_intro_mask' _ ∅) as "Hclo'"; first by set_solver+.
  iModIntro. iNext.
  iMod "Hclo'" as "_".
  rewrite /log_inv_inner.
  iDestruct "Hinner" as "[Hval|Hfalse]"; last first.
  {
    iDestruct "Hvs" as "(_&(Hbad&_))".
    by iMod ("Hbad" with "[$]").
  }
  iMod (staged_inv_open with "[Hval]") as "Hclo'"; [ | | iFrame "Hc_inv"; iFrame | ].
  { solve_ndisj. }
  { eauto. }
  iDestruct "Hclo'" as "[?|?]"; last first.
  {
    iMod
  (* XXX need more laters here... *)
Abort.

(* XXX: but this seems too weak, because it doesn't say that by initializing, the
   caller no longer has to prove crashed_log *)
Theorem wpc_Open' vs k k' E2 Qc:
  (S k < k')%nat →
  {{{ crashed_log vs ∗ ((∀ l, |={⊤}=> P (Opened vs l) ∗ Qc) ∧ Qc)}}}
    Open #() @ NotStuck; k; ⊤; E2
  {{{ lptr, RET #lptr; is_log k' lptr }}}
  {{{ crashed_log vs ∗ Qc }}}.
Proof.
  iIntros (? Φ Φc) "(Hc&Hvs) HΦ".
  iApply wpc_fupd.
  wpc_apply (wpc_Open with "Hc").
  iSplit.
  { iIntros. iApply "HΦ". iFrame. iDestruct ("Hvs") as "(_&$)". }
  iNext. iIntros (?) "(Hlog&Hm)".
  iDestruct "Hm" as (?) "(Hm&Hlock)".
Abort.
*)

End hocap.
