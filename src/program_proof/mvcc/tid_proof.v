From Perennial.base_logic Require Import ghost_map saved_prop.
From Perennial.program_proof Require Import std_proof.
From Perennial.program_proof.mvcc Require Import mvcc_prelude mvcc_ghost.
From Goose.github_com.mit_pdos.go_mvcc Require Import tid.

Local Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Section program.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

Definition gentid_ns := nroot .@ "gentid".

Local Definition sid_of (ts: u64) : u64 := word.modu ts (U64 N_TXN_SITES).

Local Definition gentid_au (γ : mvcc_names) (sid : u64) (Φ : val → iProp Σ) : iProp Σ :=
  (|NC={⊤ ∖ ∅,∅}=>
    ∃ ts : nat, ts_auth γ ts ∗
       ((∃ ts' : nat, ts_auth γ ts' ∗ ⌜(ts < ts')%nat⌝) -∗
         |NC={∅,⊤ ∖ ∅}=> ∀ tid : u64, ⌜int.nat tid = ts⌝ ∗ sid_own γ sid -∗ Φ #tid)).

Local Definition reserved_inv γ now (ts : u64) γr : iProp Σ :=
  ∃ Φ, let sid := sid_of ts in
    saved_pred_own γr DfracDiscarded Φ ∗
    sid_own γ sid ∗
    if bool_decide (int.nat ts ≤ now)%nat then
      (* This ts has already happened *)
      sid_own γ sid -∗ Φ #ts
    else
      (* This ts is still in the future *)
      gentid_au γ sid Φ
    .

Local Definition gentid_inv (γ : mvcc_names) now : iProp Σ :=
  ∃ (reserved : gmap u64 gname),
    ts_auth γ now ∗ tsc_lb now ∗
    ghost_map_auth γ.(mvcc_gentid_reserved) 1 reserved ∗
    [∗ map] ts ↦ 'γr ∈ reserved,
      reserved_inv γ now ts γr.

Definition have_gentid (γ : mvcc_names) : iProp Σ :=
  inv gentid_ns (∃ now, gentid_inv γ now).

Local Definition tid_reserved γ γr ts (Φ : val → iProp Σ) : iProp Σ :=
  ghost_map_elem γ.(mvcc_gentid_reserved) ts (DfracOwn 1) γr ∗
  saved_pred_own γr DfracDiscarded Φ.

Global Instance have_gentid_persistent γ : Persistent (have_gentid γ).
Proof. apply _. Qed.

Lemma init_GenTID γ E :
  mvcc_gentid_init γ -∗
  |={E}=> have_gentid γ.
Proof.
  iIntros "[Hts Hres]".
  iMod tsc_lb_0.
  iApply inv_alloc. iNext. iExists _, ∅.
  iFrame. rewrite big_sepM_empty. done.
Qed.

Local Lemma gentid_reserve γ now sid Φ :
  gentid_inv γ now -∗
  sid_own γ sid -∗
  gentid_au γ sid Φ -∗
  |==> tsc_lb now ∗
    (* The user can pick a timestamp with the right sid, but only gets something
    out of this if they pick one that is strictly greater than [clock]. *)
    (∀ ts, ⌜sid = sid_of ts⌝ ==∗
       (if decide (now < int.Z ts) then ∃ γr, tid_reserved γ γr ts Φ else True) ∗
       gentid_inv γ now).
Proof. Admitted.

Local Lemma gentid_inc_clock γ now :
  gentid_inv γ now -∗
  tsc_lb (now+1) -∗
  |==> gentid_inv γ (now+1).
Proof. Admitted.

Local Lemma gentid_completed γ γr clock ts Φ :
  gentid_inv γ clock -∗
  tid_reserved γ γr ts Φ -∗
  tsc_lb (int.nat ts) -∗
  |==> ∃ clock', gentid_inv γ clock' ∗ sid_own γ (sid_of ts) ∗ gentid_au γ (sid_of ts) Φ.
Proof. Admitted.

(**
 * [int.nat tid = ts] means no overflow, which we would have to assume.
 * It takes around 120 years for TSC to overflow on a 4-GHz CPU.
 *)
(*****************************************************************)
(* func GenTID(sid uint64) uint64                                *)
(*****************************************************************)
Theorem wp_GenTID (sid : u64) γ :
  int.Z sid < N_TXN_SITES →
  ⊢ have_gentid γ -∗
    {{{ sid_own γ sid }}}
    <<< ∀∀ (ts : nat), ts_auth γ ts >>>
      GenTID #sid @ ∅
    <<< ∃ ts', ts_auth γ ts' ∗ ⌜(ts < ts')%nat⌝ >>>
    {{{ (tid : u64), RET #tid; ⌜int.nat tid = ts⌝ ∗ sid_own γ sid }}}.
Proof.
  iIntros "%Hsid #Hinv !>" (Φ) "Hsid HAU".
  wp_call.

  (***********************************************************)
  (* var tid uint64                                          *)
  (***********************************************************)
  wp_apply wp_ref_of_zero; first done.
  iIntros (tidRef) "Htid".
  wp_pure1_credit "LC".
  wp_pures.

  (***********************************************************)
  (* tid = GetTSC()                                          *)
  (***********************************************************)
  wp_apply (wp_GetTSC).
  iInv "Hinv" as "Hgentid" "Hclose".
  iMod (lc_fupd_elim_later with "LC Hgentid") as (clock) "Hgentid".
  iMod (gentid_reserve with "Hgentid Hsid HAU") as "[Hclock Hcont]".
  iApply ncfupd_mask_intro.
  { solve_ndisj. }
  iIntros "Hclose2".
  iExists _. iFrame "Hclock".
  iIntros (clock2) "[%Hclock Hclock2]".
  iMod "Hclose2" as "_".
  set inbounds := bool_decide (int.Z clock2 + 64 < 2^64).
  set clock2_boundsafe := if inbounds then clock2 else 0.
  feed pose proof (u64_round_up_spec clock2_boundsafe (U64 64)) as H.
  { subst clock2_boundsafe inbounds. case_bool_decide; word. }
  { word. }
  move:H.
  set rounded_ts := u64_round_up clock2_boundsafe (U64 64).
  intros (Hmod & Hbound1 & Hbound2).
  set reserved_ts := word.add rounded_ts sid.
  assert ((int.Z rounded_ts + int.Z sid) `mod` 64 = int.Z sid) as Hsidmod.
  { rewrite Z.add_mod. 2:lia.
    rewrite Hmod. rewrite [int.Z sid `mod` _]Z.mod_small. 2:split;[word|done].
    rewrite Z.mod_small. 1:lia. split;[word|done]. }
  assert (int.Z (sid_of reserved_ts) = int.Z sid) as Hsid_of.
  { rewrite /sid_of /reserved_ts.
    rewrite word.unsigned_modu. 2:done.
    rewrite word.unsigned_add. rewrite (wrap_small (_+_)). 2:word.
    rewrite wrap_small. 1:done.
    split.
    - apply Z_mod_nonneg_nonneg. all:try word. all:done.
    - trans (int.Z N_TXN_SITES). 2:done. apply Z.mod_pos_bound. done.
  }
  iMod ("Hcont" $! reserved_ts with "[]") as "[Hreserved Hgentid]".
  { iPureIntro. rewrite /sid_of /reserved_ts. apply word.unsigned_inj. done. }
  iMod ("Hclose" with "[Hgentid]") as "_".
  { eauto. }
  iIntros "!> _".

  (************************************************************************)
  (* tid = ... *)
  (************************************************************************)
  wp_store.
  wp_load.
  wp_apply wp_SumAssumeNoOverflow. iIntros (Hoverflow).
  assert (inbounds = true) as ->.
  { subst inbounds. rewrite bool_decide_true; first done. word. }
  subst clock2_boundsafe.
  wp_store.
  wp_pures.

  set tid := (word.add _ _).
  assert (tid = reserved_ts) as -> by done.

  (***********************************************************)
  (* for GetTSC() <= tid {                                   *)
  (* }                                                       *)
  (***********************************************************)
  set P := λ (b : bool), (if b then True else tsc_lb (int.nat reserved_ts))%I.
  wp_apply (wp_forBreak_cond P).
  { admit. }
  { done. }
  iIntros "HP". unfold P. clear P.
  wp_load.

  (***********************************************************)
  (* return tid                                              *) 
  (***********************************************************)
Admitted.

End program.

Global Typeclasses Opaque have_gentid.
