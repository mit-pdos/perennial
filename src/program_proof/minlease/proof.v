From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang Require Export ffi.grove_prelude.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.base_logic.lib Require Import ghost_var mono_nat.
From Goose.github_com.mit_pdos.gokv Require Import minlease.
From iris.bi.lib Require Import fixpoint_mono.
From Perennial.base_logic Require Import lib.saved_prop.
From Perennial.program_proof Require Import std_proof.

Section proof.

Context `{!heapGS Σ}.
Context `{!ghost_varG Σ u64}.
Context `{!ghost_varG Σ ()}.
Context `{!savedPropG Σ }.

(* Q is the lease obligation *)
Definition underLease (N:namespace) (leaseExpiration:u64) (P:iProp Σ) (Q:iProp Σ) : iProp Σ :=
  ∃ γprop γpostLeastTok,
  saved_prop_own γprop (DfracOwn (1/2)) P ∗
  inv N (∃ P',
    saved_prop_own γprop (DfracOwn (1/2)) P' ∗
    (P' ∗ (P' -∗ Q) ∨ is_time_lb leaseExpiration ∗ ghost_var γpostLeastTok 1 ())
  ).

(* Doesn't seem useful
Lemma underLease_mono P' P Q e N :
  (P -∗ P') -∗
  (P' -∗ Q) -∗
  underLease N e P Q -∗
  underLease N e P' Q
.
Proof.
Admitted. *)

Lemma lease_acc_update N e P Q :
  underLease N e P Q -∗
  £ 1 -∗
  £ 1 -∗
  ∀ (t:u64),
  ⌜uint.nat t < uint.nat e⌝ →
  own_time t ={↑N,∅}=∗
  (P ∗ (∀ P', P' -∗ (P' -∗ Q) ={∅,↑N}=∗ own_time t ∗ underLease N e P' Q))
.
Proof.
  iIntros "Hlease Hlc Hlc2".
  iIntros (?) "%Hineq Htime".
  iDestruct "Hlease" as (γprop ?) "[Hprop #Hinv]".
  iInv "Hinv" as "Hi" "Hclose".
  iMod (lc_fupd_elim_later with "Hlc Hi") as "Hi".
  iDestruct "Hi" as (?) "[Hprop2 Hi]".
  iDestruct (saved_prop_agree with "Hprop Hprop2") as "#Hagree1".
  iMod (lc_fupd_elim_later with "Hlc2 Hagree1") as "#Hagree".
  replace (↑N ∖ ↑N) with (∅:coPset) by set_solver.
  iModIntro.
  iDestruct "Hi" as "[[HP HQwand]|[Hbad HpostLeastTok]]"; last first.
  {
    iDestruct (mono_nat_lb_own_valid with "Htime Hbad") as %[_ Hbad].
    exfalso.
    word.
  }
  iSplitL "HP".
  {
    by iRewrite "Hagree".
  }
  iIntros (R) "HR HRwandQ".
  iMod (saved_prop_update_2 R with "Hprop Hprop2") as "[Hprop Hprop2]".
  { apply Qp.half_half. }
  iFrame "Htime".
  iMod ("Hclose" with "[HRwandQ HR Hprop2]").
  {
    iNext.
    iExists _; iFrame "Hprop2".
    iLeft.
    iFrame.
  }
  iModIntro.
  iExists _, _; iFrame "∗#".
Qed.

Definition postLease (N:namespace) (leaseExpiration:u64) (Q:iProp Σ) : iProp Σ :=
  is_time_lb leaseExpiration ={↑N}=∗ ▷ Q
.

Lemma lease_alloc e Q N P :
  P -∗ (P -∗ Q) ={↑N}=∗
  underLease N e P Q ∗
  postLease N e Q
.
Proof.
  iIntros "HP Hwand".
  iMod (saved_prop_alloc P (DfracOwn 1)) as (γprop) "[Hprop Hprop2]".
  { done. }
  iMod (ghost_var_alloc ()) as (γpostLeaseTok) "HpostLeaseTok".
  iAssert (|={↑N}=>
  inv N (∃ P',
    saved_prop_own γprop (DfracOwn (1/2)) P' ∗
    (P' ∗ (P' -∗ Q) ∨ is_time_lb e ∗ ghost_var γpostLeaseTok 1 ())
  ))%I with "[HP Hwand Hprop2]" as ">#Hinv".
  {
    iMod (inv_alloc with "[-]") as "$"; last done.
    iNext.
    iExists _; iFrame "Hprop2".
    iLeft. iFrame.
  }
  iModIntro.
  iSplitL "Hprop".
  {
    iExists _, _; iFrame "∗#".
  }
  iIntros "Hlb".
  iInv "Hinv" as "Hi" "Hclose".
  iDestruct "Hi" as (?) "[Hprop HP]".
  iDestruct "HP" as "[HP |[_ >Hbad]]"; last first.
  {
    iDestruct (ghost_var_valid_2 with "Hbad HpostLeaseTok") as %[Hbad _].
    exfalso.
    done.
  }
  iDestruct "HP" as "[HP HPwand]".
  iDestruct (later_wand with "HPwand") as "HPwand".
  iMod ("Hclose" with "[Hprop HpostLeaseTok Hlb]").
  {
    iExists _; iFrame.
    iRight.
    iFrame.
  }
  iApply "HPwand".
  done.
Qed.

(* P are resources you can access and modify at the moment you check that the
   lease is unexpired.
 *)

Definition own_Server s γ : iProp Σ :=
  ∃ (v:u64),
  "Hval" ∷ s ↦[Server :: "val"] #v ∗
  "Hauth" ∷ ghost_var γ (1/2) v
.


Definition LEASE_EXP := W64 10.

Definition minleaseN := nroot .@ "minlease".

Definition is_Server s γ : iProp Σ :=
  ∃ mu,
  "#Hmu" ∷ readonly (s ↦[Server :: "mu"] mu) ∗
  "#HleaseExpiration" ∷ readonly (s ↦[Server :: "leaseExpiration"] #LEASE_EXP) ∗
  "#HmuInv" ∷ is_lock minleaseN mu (own_Server s γ)
.

Lemma wp_Put s (v:u64) γ Φ :
is_Server s γ -∗
(|={⊤,∅}=> ∃ (oldv:u64), ghost_var γ (1/2) oldv ∗
(ghost_var γ (1/2) v ={∅,⊤}=∗ Φ #()) )-∗
  WP Server__Put #s #v {{ Φ }}
.
Proof.
  iIntros "Hsrv Hupd".
  iNamed "Hsrv".
  wp_rec.
  wp_pures.
  wp_loadField.
  wp_apply (wp_Mutex__Lock with "HmuInv").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".
  wp_pures.
  wp_storeField.
  wp_loadField.

  iApply fupd_wp.
  iMod "Hupd" as (?) "[Hval2 Hupd]".
  iMod (ghost_var_update_2 with "Hauth Hval2") as "[Hauth Hval2]".
  { apply Qp.half_half. }
  iMod ("Hupd" with "Hval2") as "HΦ".
  iModIntro.
  wp_apply (wp_Mutex__Unlock with "[-HΦ]").
  {
    iFrame "HmuInv Hlocked".
    iNext.
    repeat iExists _; iFrame "∗#%".
  }
  wp_pures.
  by iFrame.
Qed.

Lemma wp_Get s γ Φ :
is_Server s γ -∗
(|={⊤,∅}=> ∃ (v:u64), ghost_var γ (1/2) v ∗
(ghost_var γ (1/2) v ={∅,⊤}=∗ Φ #v) )-∗
  WP Server__Get #s {{ Φ }}
.
Proof.
  iIntros "Hsrv Hupd".
  iNamed "Hsrv".
  wp_rec.
  wp_pures.
  wp_loadField.
  wp_apply (wp_Mutex__Lock with "HmuInv").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".
  wp_pures.
  wp_loadField.
  wp_loadField.

  iApply fupd_wp.
  iMod "Hupd" as (?) "[Hval2 Hupd]".
  iDestruct (ghost_var_valid_2 with "Hauth Hval2") as %[_ ->].
  iMod ("Hupd" with "Hval2") as "HΦ".
  iModIntro.
  wp_apply (wp_Mutex__Unlock with "[-HΦ]").
  {
    iFrame "HmuInv Hlocked".
    iNext.
    repeat iExists _; iFrame "∗#%".
  }
  wp_pures.
  by iFrame.
Qed.

Lemma wp_StartServer γ :
  {{{
      "Hlease" ∷ underLease minleaseN LEASE_EXP (ghost_var γ (1/2) (W64 0)) (∃ (v:u64), (ghost_var γ (1/2) v)) ∗
      "Hauth" ∷ ghost_var γ (1/2) (W64 0)
  }}}
    StartServer #()
  {{{
        s, RET #s; is_Server s γ
  }}}
.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  wp_rec.
  wp_apply (wp_allocStruct).
  { repeat constructor. }
  iIntros (?) "Hl".
  iDestruct (struct_fields_split with "Hl") as "HH".
  iNamed "HH".
  wp_pures.
  wp_apply (wp_new_free_lock).
  iIntros (mu) "HmuInv".
  wp_storeField.
  wp_storeField.
  wp_storeField.
  iMod (readonly_alloc_1 with "mu") as "#Hmu".
  iMod (readonly_alloc_1 with "leaseExpiration") as "#HleaseExpiration".

  iAssert (|={⊤}=> is_Server l γ)%I with "[-HΦ Hlease]" as ">#Hsrv".
  {
    repeat iExists _.
    iFrame "∗#%".
    iDestruct (alloc_lock with "HmuInv [-]") as "$".
    iNext.
    repeat iExists _; iFrame "∗#%".
  }

  wp_apply (wp_fork with "[-HΦ]").
  {
    iNext.
    wp_pure_credit "Hlc1".
    wp_pure_credit "Hlc2".
    wp_pures.
    iAssert  ( ∃ v,
      "Hlease" ∷ underLease minleaseN LEASE_EXP (ghost_var γ (1 / 2) v%Z)
               (∃ v' : u64, ghost_var γ (1 / 2) v')
               )%I with "[Hlease]" as "HH" .
    { iExists _. iFrame. }
    wp_forBreak_cond.
    wp_pures.
    wp_rec.
    iClear "Hmu HleaseExpiration".
    iNamed "Hsrv".
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "HmuInv").
    iIntros "[Hlocked Hown]".
    wp_pures.
    wp_apply (wp_GetTimeRange).
    iIntros (low high t) "%Hineq1 %Hineq2 Htime".
    iNamed "HH".

    destruct (decide (uint.nat LEASE_EXP <= uint.nat high)).
    2:{ (* case: lease is not expired *)
      iDestruct (lease_acc_update with "Hlease Hlc1 Hlc2") as "HH".
      iDestruct ("HH" $! t with "[%] Htime") as "HH".
      { word. }
      iMod (fupd_mask_subseteq _) as "Hmask"; last iMod "HH".
      { set_solver. }
      iNamed "Hown".
      iDestruct "HH" as "[Hval2 HcloseLease]".
      iDestruct (ghost_var_valid_2 with "Hauth Hval2") as %[_ ->].
      iMod (ghost_var_update_2 (word.add v 1) with "Hauth Hval2") as "[Hauth Hval2]".
      { apply Qp.half_half. }

      iMod ("HcloseLease" $!_ with "Hval2 []") as "[Htime Hlease]".
      {
        iIntros. iExists _; iFrame.
      }
      iMod "Hmask".
      iModIntro.
      iFrame "Htime".
      wp_pure_credit "Hlc1".
      wp_pure_credit "Hlc2".
      wp_loadField.
      wp_pures.
      wp_bind (If (#(bool_decide _)) _ _).
      wp_if_destruct.
      1:{
        exfalso.
        word.
      }
      wp_loadField.
      wp_apply (wp_SumAssumeNoOverflow).
      iIntros "%Hoverflow".
      wp_storeField.
      wp_loadField.
      wp_apply (wp_Mutex__Unlock with "[-Hlease Hlc1 Hlc2]").
      {
        iFrame "HmuInv Hlocked".
        repeat iExists _; iFrame "∗#%".
      }
      wp_pures.
      iLeft.
      iModIntro.
      iSplitR; first done.
      iFrame.
    }
    (* Otherwise, lease has expired *)
    iModIntro.
    iFrame.
    wp_pures.
    wp_loadField.
    wp_pures.
    wp_bind (If (#(bool_decide _)) _ _).
    wp_if_destruct.
    2:{ exfalso. word. }
    wp_loadField.
    wp_apply (wp_Mutex__Unlock with "[-Hlease]").
    {
      iFrame "HmuInv Hlocked". iFrame.
    }
    wp_pures.
    iRight.
    iModIntro.
    done.
  }
  wp_pures.
  iModIntro.
  iApply "HΦ".
  done.
Qed.

Lemma wp_client s γ :
  {{{
      "#Hsrv" ∷ is_Server s γ ∗
      "HpostLease" ∷ postLease minleaseN LEASE_EXP (∃ (v':u64), ghost_var γ (1/2) v')
  }}}
    client #s
  {{{
      RET #(); True
  }}}
.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  wp_rec. wp_pures.
  wp_forBreak.
  wp_pures.
  wp_apply (wp_GetTimeRange).
  iIntros (low high t Hineq1 Hineq) "Htime".

  iAssert (_) with "Hsrv" as "Hsrv2".
  iNamed "Hsrv2".

  destruct (decide (uint.nat LEASE_EXP < uint.nat low)).
  {
    iDestruct (mono_nat_lb_own_get with "Htime") as "#Hlb".
    unfold postLease.
    iMod (fupd_mask_subseteq _) as "Hmask";
      last iMod ("HpostLease" with "[Hlb]") as "HpostLease".
    { set_solver. }
    { unfold is_time_lb. destruct goose_groveGS. simpl.
      iApply mono_nat_lb_own_le; last iFrame "#". word. }
    iMod "Hmask" as "_".
    iModIntro.
    iFrame "Htime".
    wp_pures.
    iDestruct "HpostLease" as (?) "Hghost".
    wp_loadField.
    wp_pures.
    wp_if_destruct.
    2:{ exfalso. word. }
    iModIntro.
    iRight.
    iSplitR; first done.
    wp_pures.
    wp_apply (wp_Get with "Hsrv").
    iApply fupd_mask_intro.
    { set_solver. }
    iIntros "Hmask".
    iExists _; iFrame.
    iIntros "Hvar".
    iMod "Hmask" as "_".
    iModIntro.
    wp_pures.
    wp_apply wp_SumAssumeNoOverflow.
    iIntros (HnoOverflow).
    wp_pures.
    wp_apply (wp_Put with "Hsrv").
    iApply fupd_mask_intro.
    { set_solver. }
    iIntros "Hmask".
    iExists _; iFrame.
    iIntros "Hvar".
    iMod "Hmask" as "_".
    iModIntro.
    wp_pures.
    wp_apply (wp_Get with "Hsrv").
    iApply fupd_mask_intro.
    { set_solver. }
    iIntros "Hmask".
    iExists _; iFrame.
    iIntros "Hvar".
    iMod "Hmask" as "_".
    iModIntro.
    wp_pures.
    wp_apply (wp_Assert).
    { apply bool_decide_true. done. }
    wp_pures.
    iModIntro.
    by iApply "HΦ".
  }
  { (* loop and wait for server's lease to expire *)
    iFrame "Htime".
    iModIntro.
    wp_pures.
    wp_loadField.
    wp_pures.
    wp_if_destruct.
    { exfalso. word. }
    wp_loadField.
    wp_apply wp_Sleep.
    wp_pures.
    iLeft.
    iFrame.
    done.
  }
Qed.

Lemma wp_main :
  {{{
       True
  }}}
    main #()
  {{{
        RET #(); True
  }}}
.
Proof using Type*.
  iIntros (Φ) "_ HΦ".
  wp_rec.
  iMod (ghost_var_alloc (W64 0)) as (γ) "[Hvar Hvar2]".
  iApply fupd_wp.
  iMod (fupd_mask_subseteq (↑minleaseN)) as "Hmask".
  { set_solver. }
  iMod (lease_alloc LEASE_EXP (∃ v:u64, ghost_var γ (1/2) v) with "Hvar2 []") as "[Hlease HpostLease]".
  { iIntros. iExists _; iFrame. }
  iMod "Hmask".
  iModIntro.
  wp_apply (wp_StartServer with "[$Hlease $Hvar]").
  iIntros (s) "#Hsrv".
  wp_pures.
  wp_apply (wp_client with "[$Hsrv $HpostLease]").
  wp_pures.
  iModIntro.
  by iApply "HΦ".
Qed.

End proof.
