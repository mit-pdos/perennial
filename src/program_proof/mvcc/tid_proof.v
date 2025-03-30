From Perennial.base_logic Require Import ghost_map saved_prop mono_nat.
From Perennial.program_proof Require Import std_proof.
From Perennial.program_proof.mvcc Require Import mvcc_prelude mvcc_ghost.
From Goose.github_com.mit_pdos.vmvcc Require Import tid.

Local Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Section program.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

Local Definition sid_of (ts: u64) : u64 := word.modu ts (W64 N_TXN_SITES).

Local Definition gentid_au (γ : mvcc_names) (sid : u64) (Φ : val → iProp Σ) : iProp Σ :=
  (|NC={⊤ ∖ ↑mvccNTID,∅}=>
    ∃ ts : nat, ts_auth γ ts ∗
       (∀ ts' : nat, ts_auth γ ts' ∗ ⌜(ts < ts')%nat⌝ -∗
         |NC={∅,⊤ ∖ ↑mvccNTID}=> ∀ tid : u64, ⌜uint.nat tid = ts'⌝ ∗ sid_own γ sid -∗ Φ #tid)).

Local Definition reserved_inv γ γr now (ts : u64): iProp Σ :=
  ∃ Φ, let sid := sid_of ts in
    saved_pred_own γr DfracDiscarded Φ ∗
    sid_own γ sid ∗
    if bool_decide (uint.nat ts ≤ now)%nat then
      (* This ts has already happened *)
      sid_own γ sid -∗ Φ #ts
    else
      (* This ts is still in the future *)
      gentid_au γ sid Φ
    .

Local Definition gentid_inv (γ : mvcc_names) now : iProp Σ :=
  ∃ prev (reserved : gmap u64 gname),
    ⌜prev ≤ now⌝%nat ∗ ts_auth γ prev ∗ tsc_lb now ∗
    ghost_map_auth γ.(mvcc_gentid_reserved) 1 reserved ∗
    [∗ map] ts ↦ 'γr ∈ reserved,
      reserved_inv γ γr now ts.

Definition have_gentid (γ : mvcc_names) : iProp Σ :=
  inv mvccNTID (∃ now, gentid_inv γ now).

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
  iApply inv_alloc. iNext. iExists _, 0%nat, ∅.
  iFrame. rewrite big_sepM_empty. eauto.
Qed.

Local Lemma gentid_reserve γ now sid Φ :
  gentid_inv γ now -∗
  sid_own γ sid -∗
  gentid_au γ sid Φ -∗
  |==> tsc_lb now ∗
    (* The user can pick a timestamp with the right sid, but only gets something
    out of this if they pick one that is strictly greater than [clock]. *)
    (∀ ts, ⌜sid = sid_of ts⌝ ==∗
       (if bool_decide (now < uint.Z ts) then ∃ γr, tid_reserved γ γr ts Φ else True) ∗
       gentid_inv γ now).
Proof.
  iIntros "(%last & %reserved & %Hlast & Hts & #Htsc & Hreserved_map & Hreserved) Hsid HAU".
  iFrame "Htsc". iIntros "!> %ts %Hsid".
  iAssert (⌜reserved !! ts = None⌝)%I as %Hfresh.
  { destruct (reserved !! ts) as [γr|] eqn:Hts; last done. iExFalso.
    iDestruct (big_sepM_lookup _ _ _ _ Hts with "Hreserved") as (Φ2) "(_ & Hsid2 & _)".
    rewrite -Hsid.
    iDestruct (own_valid_2 with "Hsid Hsid2") as %Hval. iPureIntro. move:Hval.
    rewrite singleton_op singleton_valid. done. }
  case_bool_decide; last first.
  { (* They gave us an outdated timestamp. *)
    iSplitR; first done. eauto with iFrame. }
  iMod (saved_pred_alloc Φ DfracDiscarded) as (γr) "#HΦ"; first done.
  iMod (ghost_map_insert ts γr with "Hreserved_map") as "[Hreserved_map Hreserved_ts]"; first done.
  iSplitL "Hreserved_ts".
  { rewrite /tid_reserved. eauto. }
  iExists last, _. iFrame "Hreserved_map Hts". iSplitR; first done.
  iApply big_sepM_insert; first done.
  iFrame. rewrite /reserved_inv. rewrite bool_decide_false; last lia.
  iExists Φ. iFrame "HΦ". rewrite -Hsid. iFrame. done.
Qed.

Local Lemma reserved_inc_clock γ now reserved :
  reserved !! (W64 (S now)) = None →
  ([∗ map] ts↦γr ∈ reserved, reserved_inv γ γr now ts) -∗
  [∗ map] ts↦γr ∈ reserved, reserved_inv γ γr (S now) ts.
Proof.
  intros Hnotnow.
  iIntros "Hm". iApply (big_sepM_impl with "Hm").
  iIntros "!> %ts %γr %Hts (%Φ & HΦ & Hsid & HAU)".
  assert (uint.nat ts ≠ S now).
  { intros Heq. rewrite -Heq in Hnotnow.
    replace (W64 (uint.nat ts)) with ts in Hnotnow by word. congruence. }
  iExists _. iFrame.
  case_bool_decide.
  - rewrite bool_decide_true. 2:lia. done.
  - rewrite bool_decide_false. 2:lia. done.
Qed.

Local Lemma gentid_inc_clock γ old now :
  (old ≤ now)%nat →
  (now < 2^64) →
  gentid_inv γ old -∗
  tsc_lb now -∗
  |NC={⊤∖↑mvccNTID}=> gentid_inv γ now.
Proof.
  induction 1 using le_ind.
  { eauto. }
  iIntros (?) "Hgentid #Htsc".
  iDestruct (IHle with "Hgentid [Htsc]") as ">Hgentid".
  { lia. }
  { iApply tsc_lb_weaken; last done. lia. }
  iDestruct "Hgentid" as "(%last & %reserved & %Hlast & Hts & _ & Hreserved_map & Hreserved)".
  set ts := S m.
  destruct (reserved !! (W64 ts)) as [γr|] eqn:Hts; last first.
  { (* Nothing reserved at this timestamp, not much to do. *)
    iExists _, _. iFrame. iSplitR; first by eauto with lia.
    iFrame "Htsc".
    iApply reserved_inc_clock; done. }
  (* Bump our timestamp. *)
  iExists ts, _. iFrame. iFrame "Htsc".
  iSplitR; first done.
  rewrite !(big_sepM_delete _ _ _ _ Hts).
  iDestruct "Hreserved" as "[Hthis Hreserved]".
  rewrite !assoc. iSplitR "Hreserved"; last first.
  { iApply reserved_inc_clock; last done.
    rewrite lookup_delete. done. }
  iDestruct "Hthis" as (Φ) "(HΦ & Hsid & HAU)".
  rewrite bool_decide_false. 2:word.
  iMod "HAU" as (ts') "[Hts' Hclose]".
  rewrite /ts_auth.
  iDestruct (mono_nat_auth_own_agree with "Hts Hts'") as %[_ <-].
  iCombine "Hts Hts'" as "Hts".
  iMod (mono_nat_own_update ts with "Hts") as "[[Hts $] _]".
  { lia. }
  iMod ("Hclose" with "[Hts]") as "Hfin".
  { iFrame. eauto with lia. }
  iModIntro. iExists _. iFrame. rewrite bool_decide_true.
  2:word.
  iIntros "Hsid". iApply "Hfin". iFrame. word.
Qed.

Local Lemma gentid_completed γ γr clock ts Φ :
  £1 -∗
  gentid_inv γ clock -∗
  tid_reserved γ γr ts Φ -∗
  tsc_lb (uint.nat ts) -∗
  |NC={⊤∖↑mvccNTID}=> ∃ clock', gentid_inv γ clock' ∗ Φ #ts.
Proof.
  iIntros "LC Hgentid Hreserved Htsc".
  set clock' := max clock (uint.nat ts).
  iAssert (|NC={⊤∖↑mvccNTID}=> gentid_inv γ clock')%I with "[Htsc Hgentid]" as ">Hgentid".
  { destruct (decide (clock <= uint.nat ts)%nat); last first.
    { replace clock' with clock by lia. done. }
    iMod (gentid_inc_clock with "Hgentid Htsc") as "Hgentid"; first done.
    { word. }
    replace clock' with (uint.nat ts) by lia. done.
  }
  iDestruct "Hgentid" as "(%last & %reserved & %Hlast & Hts & #Htsc & Hreserved_map & Hreserved_all)".
  iExists clock'.
  iDestruct "Hreserved" as "[Hmap HΦ]".
  iDestruct (ghost_map_lookup with "Hreserved_map Hmap") as %Hts.
  iMod (ghost_map_delete with "Hreserved_map Hmap") as "Hreserved_map".
  iDestruct (big_sepM_delete _ _ _ _ Hts with "Hreserved_all") as "[Hreserved Hreserved_all]".
  iDestruct "Hreserved" as (Φ') "(HΦ' & Hsid & HAU)".
  iDestruct (saved_pred_agree _ _ _ _ _ (#ts) with "HΦ HΦ'") as "EQ".
  iMod (lc_fupd_elim_later with "LC EQ") as "EQ".
  iRewrite "EQ". clear Φ.
  rewrite bool_decide_true.
  2:lia.
  iModIntro. iSplitR "Hsid HAU".
  - iExists _, _. iFrame. eauto.
  - iApply "HAU". done.
Qed.

Local Hint Unfold u64_round_up : word.

(**
 * [uint.nat tid = ts] means no overflow, which we would have to assume.
 * It takes around 120 years for TSC to overflow on a 4-GHz CPU.
 *)
(*****************************************************************)
(* func GenTID(sid uint64) uint64                                *)
(*****************************************************************)
Theorem wp_GenTID (sid : u64) γ :
  uint.Z sid < N_TXN_SITES →
  ⊢ have_gentid γ -∗
    {{{ sid_own γ sid }}}
    <<< ∀∀ (ts : nat), ts_auth γ ts >>>
      GenTID #sid @ ↑mvccNTID
    <<< ∃∃ ts', ts_auth γ ts' ∗ ⌜(ts < ts')%nat⌝ >>>
    {{{ (tid : u64), RET #tid; ⌜uint.nat tid = ts'⌝ ∗ sid_own γ sid }}}.
Proof.
  iIntros "%Hsid #Hinv !>" (Φ) "Hsid HAU".
  wp_rec. wp_pures.

  (***********************************************************)
  (* var tid uint64                                          *)
  (***********************************************************)
  wp_apply wp_ref_of_zero; first done.
  iIntros (tidRef) "Htid".
  wp_pure_credit "LC".
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
  set inbounds := bool_decide (uint.Z clock2 + 32 < 2^64).
  set clock2_boundsafe := if inbounds then clock2 else 0.
  (*opose proof (u64_round_up_spec clock2_boundsafe (W64 32) _ _) as H.
  { subst clock2_boundsafe inbounds. case_bool_decide; word. }
  { word. } *)
  (* move:H. *)
  set rounded_ts := u64_round_up clock2_boundsafe (W64 32).
  (* intros (Hmod & Hbound1 & Hbound2). *)
  set reserved_ts := word.add rounded_ts sid.
  assert ((uint.Z rounded_ts + uint.Z sid) `mod` 32 = uint.Z sid) as Hsidmod.
  { subst rounded_ts reserved_ts. word. }
  assert (uint.Z (sid_of reserved_ts) = uint.Z sid) as Hsid_of.
  { rewrite /sid_of /reserved_ts. word. }
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
  wp_store.
  wp_pures.

  assert (inbounds = true) as ->.
  { subst inbounds. rewrite bool_decide_true; first done. word. }
  subst clock2_boundsafe.
  rewrite bool_decide_true.
  2:{ subst reserved_ts rounded_ts. word. }
  iDestruct "Hreserved" as (γr) "Hreserved".

  set tid := (word.add _ _).
  assert (tid = reserved_ts) as -> by done.

  (***********************************************************)
  (* for GetTSC() <= tid {                                   *)
  (* }                                                       *)
  (***********************************************************)
  set P := λ (b : bool), (tidRef ↦[uint64T] #(reserved_ts : u64) ∗
     if b then True else tsc_lb (uint.nat reserved_ts))%I.
  wp_apply (wp_forBreak_cond P with "[] [Htid]").
  { clear Φ. iIntros "!> %Φ [Htid _] HΦ".
    wp_apply (wp_GetTSC).
    iMod tsc_lb_0 as "Htsc".
    iApply ncfupd_mask_intro.
    { solve_ndisj. }
    iIntros "Hclose".
    iExists _. iFrame "Htsc".
    iIntros (new_time) "[%Htime Htsc]". iMod "Hclose" as "_".
    iIntros "!> _". wp_load. wp_pures.
    case_bool_decide; wp_pures; iApply "HΦ"; unfold P; iFrame "Htid".
    - done.
    - iApply tsc_lb_weaken; last done. lia.
  }
  { unfold P. iFrame. }
  iIntros "HP". unfold P. clear P. iDestruct "HP" as "[Htid Htsc]".

  wp_pure_credit "LC1". wp_pure_credit "LC2".
  iApply ncfupd_wp.
  iInv "Hinv" as "Hgentid" "Hclose".
  iMod (lc_fupd_elim_later with "LC1 Hgentid") as (clock3) "Hgentid".
  iMod (gentid_completed with "LC2 Hgentid Hreserved Htsc") as (clock4) "(Hgentid & HΦ)".
  iMod ("Hclose" with "[Hgentid]") as "_".
  { eauto. }
  iModIntro.

  (***********************************************************)
  (* return tid                                              *) 
  (***********************************************************)
  wp_load. iApply "HΦ".
Qed.

End program.

Global Typeclasses Opaque have_gentid.
