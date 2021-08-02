From iris.algebra Require Import gmap auth agree gset coPset excl csum.
From Perennial.program_logic Require Import staged_invariant.
From Perennial.goose_lang Require Import crash_modality lifting wpr_lifting.
From Perennial.goose_lang Require Import wpc_proofmode.
From Perennial.base_logic.lib Require Import saved_prop.
From Perennial.Helpers Require Import Qextra.


Section crash_borrow_def.
Context `{ext:ffi_syntax}.
Context `{ffi_sem: ffi_semantics}.
Context `{!ffi_interp ffi}.

Context `{!heapGS Σ}.
Context `{!stagedG Σ}.

Global Instance later_tokG_heap : later_tokG (heapG_irisG).
Proof.
  refine {| later_tok := cred_frag 1 |}.
  - iIntros (g ns mj D κ) "(Hg&Hfrag)".
    iDestruct "Hg" as "(Hffi&Hinv&Hcred&Htok)".
    iMod (cred_interp_decr with "[$]") as (ns' ->) "(Hauth&Hfrag)".
    iExists ns'. iModIntro; iSplit; first done.
    iFrame. iDestruct "Hauth" as "($&_)".
  - iIntros (g ns mj D κ) "Hg".
    iDestruct "Hg" as "(Hffi&Hinv&(Hcred&H0)&Htok)".
    iMod (cred_interp_incr with "[$]") as "(Hauth&Hfrag)".
    iFrame. eauto.
  - intros n1 n2 Hlt => /=.
    transitivity (3 ^ (1 + (n1 + 1)))%nat; last first.
    { apply Nat.pow_le_mono_r; lia. }
    rewrite [a in _ _ a]Nat.pow_add_r.
    rewrite [a in _ _ a]/=.
    transitivity (2 + 3^(n1 + 1) + 3^(n1 + 1))%nat; first by lia.
    rewrite plus_0_r -plus_assoc.
    apply plus_le_compat_r.
    clear.
    transitivity (2 ^ 1)%nat; first by auto.
    etransitivity; last eapply (Nat.pow_le_mono_r _ 1); try (simpl; lia).
  - intros n1 n2 Hlt => /=. lia.
  - intros n1 n2 Hlt => /=. lia.
  - intros n1 => /=. lia.
Defined.

Lemma ownfCP_inf_le1 γ (q : Qp) (E : coPset) :
  ownfCP_inf γ q E -∗ ⌜ q ≤ 1 ⌝%Qp.
Proof.
  iDestruct 1 as "(%Hinf&Hown)".
  iDestruct (own_valid with "Hown") as %Hval.
  iPureIntro.
  destruct Hval as (Hval&Hdom).
  specialize (Hval (coPpick E)).
  rewrite /= decide_True in Hval => //=.
  apply coPpick_elem_of.
  intros ?. apply set_not_infinite_finite in Hinf; eauto.
Qed.

Lemma ownfCP_disj1 γ q1 D E :
  ownfCP γ q1 D ∗ ownfCP_inf γ 1 E -∗ ⌜ E ## D ⌝.
Proof.
  iIntros. iDestruct (ownfCP_disj with "[$]") as %Hcases. iPureIntro.
  destruct Hcases as [Hdisj|Hbad]; auto. exfalso.
  move: Hbad. rewrite frac_valid Qp_le_ngt => Hnlt. apply Hnlt.
  apply Qp_lt_add_r.
Qed.

Lemma ownfCP_disj_gt2 γ q D E :
  (/2 < q)%Qp →
  ownfCP γ q D ∗ ownfCP_inf γ q E -∗ ⌜ E ## D ⌝.
Proof.
  iIntros. iDestruct (ownfCP_disj with "[$]") as %Hcases. iPureIntro.
  destruct Hcases as [Hdisj|Hbad]; auto. exfalso.
  move: Hbad. rewrite frac_valid Qp_le_ngt => Hnlt. apply Hnlt.
  rewrite -Qp_inv_half_half.
  apply Qp_add_lt_mono; auto.
Qed.

Global Instance pri_invG_heap : pri_invG (heapG_irisG).
Proof.
  refine {| pri_inv_tok := λ q E, pinv_tok_inf q E |}; rewrite /pinv_tok_inf.
  - iIntros (??) "($&?)".
  - iIntros (???) "H". by rewrite ownfCP_inf_op_plus.
  - iIntros (???). rewrite ownfCP_inf_op_plus. by iIntros "$ $".
  - iIntros (q E) "H". by iApply (ownfCP_inf_le1).
  - iIntros (?????) "Hg". iDestruct "Hg" as "(?&?&?&?&?)". eauto.
  - iIntros (??????) "%Hlt Hg". iDestruct "Hg" as "(?&?&?&%Hle2&Hp)".
    iDestruct (ownfCP_op_plus with "Hp") as "(Hp1&$)".
    iFrame. iSplit.
    { iPureIntro. split; auto. transitivity (q1 + q2)%Qp; last by naive_solver.
      apply Qp_le_add_r. }
    iIntros (???) "Hg". iDestruct "Hg" as "(?&?&?&%Hle2'&Hp)".
    iFrame. iSplit; first auto.
    iApply ownfCP_op_plus. iFrame.
  - iIntros (?????) "%Hlt (Hg&Hp')". iDestruct "Hg" as "(?&?&?&%Hle2&Hp)".
    iFrame. iDestruct "Hp'" as "(%Hinf&Hp')".
    iDestruct (ownfCP_op_plus with "[$Hp' $Hp]") as "Hp".
    iDestruct (ownfCP_inf_le1 with "[$Hp //]") as %Hle3.
    iFrame. iPureIntro.
    split; auto. transitivity q2; first naive_solver.
    apply Qp_lt_add_r.
  - iIntros (g ns q D κ) "Hg".
    iMod (ownfCP_inf_init (coPset_name credit_cr_names)) as (E) "H".
    iDestruct "Hg" as "($&$&$&$&Hp)".
    iDestruct "H" as "(%Hinf&H)".
    iExists E.
    iDestruct (ownfCP_disj1 with "[$Hp H]") as %Hdisj.
    { iFrame; eauto. }
    iFrame. eauto.
  - iIntros (E g ns q D κ) "(Hp&Hg)".
    iDestruct "Hg" as "($&$&$&%Hle&Hp')".
    iFrame "%".
    iDestruct (ownfCP_disj_gt2 with "[$Hp $Hp']") as %Hdisj; first naive_solver.
    iDestruct "Hp" as "(Hinf&Hp)".
    iModIntro. iApply ownfCP_op_union; auto.
    iFrame.
  - iIntros (E g ns q D κ) "((%Hdisj&%Hinf)&Hg)".
    iDestruct "Hg" as "($&$&$&$&Hp)".
    iDestruct (ownfCP_op_union with "Hp") as "($&$)"; auto.
  - iIntros (g ns q1 q2 D κ E) "(Hg&Hp')".
    iDestruct "Hg" as "(?&?&?&%Hle&Hp)".
    iApply (ownfCP_disj with "[$]").
Qed.

Definition pre_borrow : iProp Σ :=
  (later_tok ∗ later_tok ∗ later_tok ∗ later_tok).

Definition pre_borrowN (n: nat) := Nat.iter n (λ P, pre_borrow ∗ P)%I True%I.

Global Instance pre_borrowN_timeless n :
  Timeless (pre_borrowN n).
Proof. induction n; apply _. Qed.

Lemma cred_frag_to_pre_borrowN n :
  cred_frag (n * 4) -∗ pre_borrowN n.
Proof.
  induction n.
  - rewrite //=. eauto.
  - replace (S n * 4) with (4 + (n * 4)) by auto.
    iIntros "H". iDestruct (cred_frag_split with "H") as "(H&IH)".
    iDestruct (IHn with "IH") as "IH". simpl. iFrame.
    replace 4 with (1 + 1 + 1 + 1) by auto.
    repeat (iDestruct (cred_frag_split with "H") as "(H&?)").
    iFrame.
Qed.

Lemma pre_borrowN_split n1 n2 :
  pre_borrowN (n1 + n2) -∗ pre_borrowN n1 ∗ pre_borrowN n2.
Proof.
  rewrite /pre_borrowN Nat_iter_add.
  induction n1 => //=.
  - iIntros "$".
  - iIntros "($&H)". by iApply IHn1.
Qed.

Lemma pre_borrowN_to_cred_frag n :
  pre_borrowN (S n) -∗ cred_frag ((S n) * 4).
Proof.
  induction n.
  - rewrite //=.
    replace 4 with (1 + 1 + 1 + 1) by auto.
    iIntros "((?&?&?&?)&_)".
    repeat (iApply cred_frag_join; iFrame).
  - iIntros "H". iDestruct (pre_borrowN_split 1 with "H") as "(H&Hrest)".
    iDestruct (IHn with "Hrest") as "IH".
    replace (S (S n) * 4) with (4 + (S n * 4)) by lia.
    iApply cred_frag_join; iFrame.
    replace 4 with (1 + 1 + 1 + 1) by auto.
    iDestruct "H" as "((?&?&?&?)&_)".
    repeat (iApply cred_frag_join; iFrame).
Qed.

Lemma pre_borrowN_global_interp_le n1 g n2 mj E κs :
  pre_borrowN n1 -∗ global_state_interp g n2 mj E κs -∗
  ⌜ 4 * n1 <= n2 ⌝.
Proof.
  destruct n1; first by (iIntros; iPureIntro; lia).
  iIntros "Hpre Hg".
  iDestruct "Hg" as "(_&_&Hinterp&_)".
  iDestruct (pre_borrowN_to_cred_frag with "Hpre") as "Hcred_frag".
  iDestruct (cred_interp_invert with "[$]") as (?) "%Heq". subst.
  iPureIntro; lia.
Qed.

Lemma pre_borrowN_big_sepM `{Countable K} {A} n (m : gmap K A) :
  size m = n →
  pre_borrowN n -∗ [∗ map] _ ↦ _ ∈ m, pre_borrow.
Proof.
  iInduction m as [| x m] "IH" using map_ind forall (n).
  - iIntros (_) "_". rewrite //=.
  - iIntros (Hsize) "H".
    rewrite big_sepM_insert //.
    rewrite map_size_insert_None // in Hsize.
    inversion Hsize; subst.
    iDestruct (pre_borrowN_split 1 with "H") as "(($&_)&H)".
    iApply "IH"; eauto.
Qed.

Definition crash_borrow Ps Pc : iProp Σ :=
 (∃ Ps' Pc', □ (Ps -∗ Pc) ∗
             ▷ (Ps' -∗ Ps) ∗
             ▷ □ (Pc -∗ Pc') ∗
             staged_value_idle ⊤ Ps' True%I Pc' ∗ later_tok ∗ later_tok).

Lemma crash_borrow_init_cancel P Pc :
  pre_borrow -∗ P -∗ □ (P -∗ Pc) -∗ init_cancel (crash_borrow P Pc) Pc.
Proof.
  iIntros "H HP #Hwand".
  iDestruct "H" as "(Hlt1&H)".
  iDestruct "H" as "(Hlt2&Hlt3)".
  iDestruct (staged_value_init_cancel P Pc with "[$]") as "H".
  iApply (init_cancel_wand with "H [-] []").
  { iIntros "H". iExists _, _. iFrame "# ∗". iSplitL; eauto. }
  eauto.
Qed.

Lemma big_sepM_crash_borrow_init_cancel `{Countable A} {B} (P: A → B → iProp Σ) Q m:
  ([∗ map] _ ↦ _ ∈ m, pre_borrow) -∗
  ([∗ map] a ↦ obj ∈ m, Q a obj) -∗
  ([∗ map] a ↦ obj ∈ m, □ (Q a obj -∗ P a obj)) -∗
   init_cancel ([∗ map] a ↦ obj ∈ m, crash_borrow (Q a obj) (P a obj)) ([∗ map] a ↦ obj ∈ m, P a obj).
Proof.
  iIntros "Hpres HQs #Hstatuses".
  iInduction m as [|i x m] "IH" using map_ind.
  { iApply init_cancel_intro; rewrite !big_sepM_empty; eauto. }
  iDestruct (big_sepM_insert with "Hpres") as "[Hpre Hpres]";
    first by assumption.
  iDestruct (big_sepM_insert with "HQs") as "[HQ HQs]";
    first by assumption.
  iDestruct (big_sepM_insert with "Hstatuses") as "[Hstatus Hstatuses']";
    first by assumption.
  iDestruct ("IH" with "Hstatuses' Hpres HQs") as "Hcancel".
  iDestruct (crash_borrow_init_cancel with "Hpre HQ Hstatus")
    as "Hcrash".
  iDestruct (init_cancel_sep with "Hcrash Hcancel") as "Hcancel".
  iApply (init_cancel_wand with "Hcancel"); iIntros "H"; iApply big_sepM_insert; eauto.
Qed.

Lemma wpc_crash_borrow_inits s k e Φ Φc P Pc :
  pre_borrow -∗
  P -∗
  □ (P -∗ Pc) -∗
  (crash_borrow P Pc -∗ WPC e @ s; k; ⊤ {{ Φ }} {{ Pc -∗ Φc }}) -∗
  WPC e @ s; k; ⊤ {{ Φ }} {{ Φc }}.
Proof.
  iIntros "H HP #Hwand Hwpc".
  iDestruct (crash_borrow_init_cancel with "[$] HP [$]") as "Hcb".
  iApply (init_cancel_elim with "[$]"). eauto.
Qed.

Lemma wpc_crash_borrow_generate_pre s k e Φ Φc :
  language.to_val e = None →
  WPC e @ s; k; (⊤ ∖ (↑borrowN : coPset))
                  {{ v, pre_borrow -∗ Φ v }} {{ Φc }} -∗
  WPC e @ s; k; ⊤ {{ Φ }} {{ Φc }}.
Proof.
  iIntros (Hnv) "Hwpc".
  iApply wpc_borrow_inv.
  iIntros "#Hinv". rewrite wpc_eq. iIntros (mj).
  iSpecialize ("Hwpc" $! mj).
  rewrite ?wpc0_unfold.
  iSplit; last first.
  { iIntros. iDestruct "Hwpc" as "(_&H)".
    iSpecialize ("H" with "[$] [$]").
    iApply (step_fupd2N_inner_wand with "H"); auto. }
  rewrite Hnv.
  iIntros (q σ g1 ns D κ κs nt) "Hσ Hg HNC".
  iInv "Hinv" as ">H" "Hclo".
  rewrite /crash_borrow_ginv_number.
  iDestruct (cred_frag_split 1 _ with "H") as "(Hlt1&H)".
  iDestruct (cred_frag_split 1 _ with "H") as "(Hlt2&H)".
  iDestruct (cred_frag_split 1 _ with "H") as "(Hlt3&H)".
  iDestruct (cred_frag_split 1 _ with "H") as "(Hlt4&H)".
  iDestruct (cred_frag_split 1 _ with "H") as "(Hlt5&H)".
  iDestruct ("Hwpc") as "(Hwpc&_)".
  rewrite Hnv.
  iMod (later_tok_decr with "[$]") as (ns' Heq) "Hg".
  iMod ("Hwpc" with "[$] [$] [$]") as "Hwpc".
  iModIntro.
  iApply (step_fupd_extra.step_fupd2N_le (S (num_laters_per_step ns')) (num_laters_per_step ns) with "[-]").
  { assert (Hlt: ns' < ns) by lia.
    apply num_laters_per_step_lt in Hlt. lia.
  }
  iApply (step_fupd2N_wand with "Hwpc").
  iIntros "($&H)".
  iIntros. iMod ("H" with "[//]") as "(Hσ&Hg&Hwp&$)".
  iFrame.
  iMod (later_tok_incrN 10 with "[$]") as "(Hg&Htoks)".
  iMod (global_state_interp_le _ ((step_count_next ns)) _ _ with "Hg") as "Hg".
  { by apply step_count_next_add. }
  iFrame.
  iMod ("Hclo" with "[Htoks]").
  { iNext.
    repeat (iDestruct "Htoks" as "(?&Htoks)").
    repeat (rewrite -(cred_frag_join (S 0)); iFrame). }
  iModIntro.
  iApply (wpc0_strong_mono with "Hwp"); auto.
  { destruct (to_val e2); eauto. }
  iSplit; last eauto.
  iIntros (?) "H". iModIntro.
  iApply "H". iFrame.
Qed.

Lemma wp_crash_borrow_generate_pre s e Φ :
  language.to_val e = None →
  WP e @ s; (⊤ ∖ (↑borrowN : coPset))
                  {{ v, pre_borrow -∗ Φ v }} -∗
  WP e @ s; ⊤ {{ Φ }}.
Proof.
  iIntros (?) "H".
  iApply (wpc_wp _ 0 _ _ _ True%I).
  iApply wpc_crash_borrow_generate_pre; auto.
  iApply (wp_wpc). iApply "H".
Qed.

Lemma wpc_crash_borrow_init_ctx'' s k e Φ Φc P Pc K `{!LanguageCtx K} :
  language.to_val e = None →
  P -∗
  □ (P -∗ Pc) -∗
  (∀ mj, wpc_crash_modality ⊤ mj Φc) ∧ (crash_borrow P Pc -∗
        WPC e @ s; k; (⊤ ∖ (↑borrowN : coPset))
                 {{ λ v, WPC K (of_val v) @ s; k ; ⊤ {{ Φ }} {{ Φc }} }}
                 {{ Φc }}) -∗
  WPC K e @ s; k; ⊤ {{ Φ }} {{ Φc ∗ Pc }}.
Proof.
  iIntros (Hnv) "HP #Hwand Hwpc".
  iApply wpc_borrow_inv.
  iIntros "#Hinv". rewrite wpc_eq. iIntros (mj).
  iApply wpc0_bind.
  rewrite Hnv.
  rewrite wpc0_unfold.
  iSplit; last first.
  { iIntros. iDestruct "Hwpc" as "(H&_)".
    iSpecialize ("H" $! mj).
    rewrite /wpc_crash_modality.
    iSpecialize ("H" with "[$] [$]").
    iApply (step_fupd2N_inner_wand with "H"); auto.
    iIntros "($&$)". iApply "Hwand". iFrame.
  }
  rewrite Hnv.
  iIntros (q σ g1 ns D κ κs nt) "Hσ Hg HNC".
  iInv "Hinv" as ">H" "Hclo".
  rewrite /crash_borrow_ginv_number.
  iDestruct (cred_frag_split 1 _ with "H") as "(Hlt1&H)".
  iDestruct (cred_frag_split 1 _ with "H") as "(Hlt2&H)".
  iDestruct (cred_frag_split 1 _ with "H") as "(Hlt3&H)".
  iDestruct (cred_frag_split 1 _ with "H") as "(Hlt4&H)".
  iDestruct (cred_frag_split 1 _ with "H") as "(Hlt5&_)".
  iDestruct "Hwpc" as "(_&Hwpc)".

  iMod (pri_inv_tok_alloc with "[$]") as (Einv Hdisj) "(Hitok&Hg)".
  iDestruct (pri_inv_tok_global_valid with "[$]") as %(Hgt&Hle).

  (* Create the invariant *)

  iMod (saved_prop_alloc P) as (γprop) "#Hsaved".
  iMod (saved_prop_alloc True%I) as (γprop') "#Hsaved'".
  iMod (own_alloc (● (Excl' (γprop, γprop')) ⋅ ◯ (Excl' (γprop, γprop')))) as (γ) "[H1 H2]".
  { apply auth_both_valid_2; [econstructor | reflexivity]. }
  iMod (pending_alloc) as (γ') "Hpending".
  iMod (own_alloc (● (Excl' idle) ⋅ ◯ (Excl' idle))) as (γstatus) "[Hstat1 Hstat2]".
  { apply auth_both_valid_2; [econstructor | reflexivity]. }

  iDestruct (pri_inv_tok_infinite with "Hitok") as %Hinf.
  destruct (Qp_plus_inv_2_gt_1_split mj) as (mj_ikeep&mj_ishare&Heq_mj&Hinvalid); first auto.
  iEval (rewrite -Qp_inv_half_half) in "Hitok".
  iDestruct (pri_inv_tok_split with "Hitok") as "(Hitok_u&Hitok_i)".
  iEval (rewrite -Heq_mj) in "Hitok_i".
  iDestruct (pri_inv_tok_split with "Hitok_i") as "(Hitok_ikeep&Hitok_ishare)".
  iMod (pri_inv_alloc Einv _ _ (staged_inv_inner ⊤ Einv mj mj_ishare γ γ' γstatus Pc) with "[HP H1 Hitok_ishare Hstat1]") as
      "#Hpri_inv"; auto.
  { iNext. rewrite staged_inv_inner_unfold. iExists _, _, idle, P, True%I. iFrame "∗ #".
    iLeft. iSplit; first iFrame. iIntros "HC". iDestruct ("Hwand" with "[$]") as "$"; eauto.
  }

  iAssert (crash_borrow P Pc)%I with "[Hlt1 Hlt2 Hlt5 H2 Hstat2 Hitok_u]"  as "Hborrow".
  {
    iFrame "# ∗". iExists P, Pc.
    iSplitR; first eauto.
    iSplitR; first eauto.
    iExists _, _, _, _, _, _. iFrame "∗". iFrame "Hsaved Hsaved'".
    iExists _, _. iFrame "Hpri_inv". eauto.
  }

  iAssert (staged_inv_cancel ⊤ mj Pc)%I with "[Hitok_ikeep Hpending Hlt3]" as "Hcancel".
  {
    iExists _, _, _, _, _, _, _. iFrame "%". iFrame. eauto.
  }
  iSpecialize ("Hwpc" with "[$]").
  iSpecialize ("Hwpc" $! mj).
  rewrite wpc0_unfold.
  iDestruct ("Hwpc") as "(Hwpc&_)".
  rewrite Hnv.
  iMod (later_tok_decr with "[$]") as (ns' Heq) "Hg".
  iMod ("Hwpc" with "[$] [$] [$]") as "Hwpc".
  iModIntro.
  iApply (step_fupd_extra.step_fupd2N_le (S (num_laters_per_step ns')) (num_laters_per_step ns) with "[-]").
  { assert (Hlt: ns' < ns) by lia.
    apply num_laters_per_step_lt in Hlt. lia.
  }
  iApply (step_fupd2N_wand with "Hwpc").
  iIntros "($&H)".
  iIntros. iMod ("H" with "[//]") as "(Hσ&Hg&Hwp&$)".
  iFrame.
  iMod (later_tok_incrN 10 with "[$]") as "(Hg&Htoks)".
  iMod (global_state_interp_le _ ((step_count_next ns)) _ _ with "Hg") as "Hg".
  { by apply step_count_next_add. }
  iFrame.
  iMod ("Hclo" with "[Htoks]").
  { iNext.
    repeat (iDestruct "Htoks" as "(?&Htoks)").
    repeat (rewrite -(cred_frag_join (S 0)); iFrame). }
  iModIntro.
  iApply (wpc0_staged_inv_cancel with "[$]").
  { destruct (to_val e2); eauto. }
  { auto. }
  iApply (wpc0_strong_mono with "Hwp"); auto.
  { destruct (to_val e2); eauto. }
  iSplit; last first.
  { iIntros "H !>"; eauto. }
  iIntros (v) "Hwpc". iModIntro. iIntros "Hcancel".

  iApply (wpc0_staged_inv_cancel with "[$]").
  { destruct (to_val (K _)); eauto. }
  { auto. }

  iApply (wpc0_strong_mono with "Hwpc"); auto.
  { destruct (to_val (K _)); auto. }
Qed.

Lemma wpc_crash_borrow_init_ctx' s k e Φ Φc P Pc K `{!LanguageCtx K} :
  language.to_val e = None →
  P -∗
  □ (P -∗ Pc) -∗
  Φc ∧ (crash_borrow P Pc -∗
        WPC e @ s; k; (⊤ ∖ (↑borrowN : coPset))
                 {{ λ v, WPC K (of_val v) @ s; k ; ⊤ {{ Φ }} {{ Φc }} }}
                 {{ Φc }}) -∗
  WPC K e @ s; k; ⊤ {{ Φ }} {{ Φc ∗ Pc }}.
Proof.
  iIntros (Hnv) "HP HPC Hwpc".
  iApply (wpc_crash_borrow_init_ctx'' with "HP HPC"); auto.
  iSplit.
  - iIntros. iApply wpc_crash_modality_intro. iLeft in "Hwpc". eauto.
  - iRight in "Hwpc". eauto.
Qed.

Lemma wpc_crash_borrow_init_ctx s k e Φ Φc P Pc K `{!LanguageCtx K} :
  language.to_val e = None →
  P -∗
  □ (P -∗ Pc) -∗
  (Pc -∗ Φc) ∧ (crash_borrow P Pc -∗
        WPC e @ s; k; (⊤ ∖ (↑borrowN : coPset))
                 {{ λ v, WPC K (of_val v) @ s; k ; ⊤ {{ Φ }} {{ Pc -∗ Φc }} }}
                 {{ Pc -∗ Φc }}) -∗
  WPC K e @ s; k; ⊤ {{ Φ }} {{ Φc }}.
Proof.
  iIntros (Hnv) "HP HPC Hwpc".
  iPoseProof (wpc_crash_borrow_init_ctx'' _ _ e Φ (Pc -∗ Φc) with "HP HPC [Hwpc]") as "H"; auto.
  {  iSplit.
     - iIntros. iApply wpc_crash_modality_intro. iLeft in "Hwpc". eauto.
     - iRight in "Hwpc". eauto. }
  iApply (wpc_mono with "H"); auto.
  iIntros "(H1&HP)". iApply "H1". eauto.
Qed.

Lemma crash_borrow_later_conseq P Pc P' Pc' :
  □ (P' -∗ Pc') -∗
  ▷ (P -∗ P') -∗
  ▷ □ (Pc' -∗ Pc) -∗
  crash_borrow P Pc -∗ crash_borrow P' Pc'.
Proof.
  iIntros "#Hw1' Hw2' #Hw3'".
  iIntros "Hborrow".
  iDestruct "Hborrow" as (P0 Pc0) "(#Hw1&Hw2&#H3&Hinv&Htok&Htok')".
  rewrite /crash_borrow.
  iExists P0, Pc0. iSplit; first eauto. iFrame "Hinv Htok Htok'".
  iSplitL "Hw2 Hw2'".
  - iNext. iIntros. iApply "Hw2'". iApply "Hw2". done.
  - iNext. iIntros. iModIntro. iIntros. iApply "H3". iApply "Hw3'". done.
Qed.

Lemma crash_borrow_conseq P Pc P' Pc' :
  □ (P' -∗ Pc') -∗
  (P -∗ P') -∗
  □ (Pc' -∗ Pc) -∗
  crash_borrow P Pc -∗ crash_borrow P' Pc'.
Proof.
  iIntros "#Hw1' Hw2' #Hw3'".
  iIntros "Hborrow".
  iDestruct "Hborrow" as (P0 Pc0) "(#Hw1&Hw2&#H3&Hinv&Htok&Htok')".
  rewrite /crash_borrow.
  iExists P0, Pc0. iSplit; first eauto. iFrame "Hinv Htok Htok'".
  iSplitL "Hw2 Hw2'".
  - iNext. iIntros. iApply "Hw2'". iApply "Hw2". done.
  - iNext. iIntros. iModIntro. iIntros. iApply "H3". iApply "Hw3'". done.
Qed.

Lemma wpc_crash_borrow_split' k E e Φ Φc P Pc P1 P2 Pc1 Pc2 :
  language.to_val e = None →
  ▷ crash_borrow P Pc -∗
  ▷▷ (P -∗ P1 ∗ P2) -∗
  ▷▷ □ (P1 -∗ Pc1) -∗
  ▷▷ □ (P2 -∗ Pc2) -∗
  ▷▷ (Pc1 ∗ Pc2 -∗ Pc) -∗
  WPC e @ NotStuck; k; E {{ λ v, (crash_borrow P1 Pc1 ∗ crash_borrow P2 Pc2) -∗  (Φc ∧ Φ v) }} {{ Φc }} -∗
  WPC e @ NotStuck; k; E {{ Φ }} {{ Φc }}.
Proof.
  iIntros (Hnval) "Hborrow Hshift #Hwand1 #Hwand2 Hwandc Hwpc".
  iDestruct "Hborrow" as (??) "(#Hw1&Hw2&Hw3&Hinv&>Htok&>Htok')".
  iApply (wpc_later_tok_use2 with "[$]"); first done.
  iNext. iNext.
  iApply (wpc_staged_inv_inuse); first done.
  iFrame "Hinv".
  iSplit.
  { iIntros. rewrite wpc_unfold. iDestruct ("Hwpc" $! _) as "(_&Hwpc)".
    iApply (wpc_crash_modality_wand with "Hwpc").
    iIntros "$". eauto. }
  iIntros "HP".
  iDestruct ("Hshift" with "[HP Hw2]") as "(HP1&HP2)".
  { iApply "Hw2". eauto. }
  iIntros (mj Hlt).
  iApply wpc_fupd2.
  iApply (wpc_pri_inv_tok_res).
  iIntros (E1') "Hitok1".
  iApply (wpc_pri_inv_tok_res).
  iIntros (E2') "Hitok2".
  iApply (wpc_later_tok_invest with "[$]"); first done.
  rewrite wpc_eq. iIntros (mj').
  iApply (wpc0_strong_mono with "Hwpc"); auto.
  iSplit; last first.
  { iIntros "$ !>". iSplitR; first eauto. iApply "Hw3". iApply "Hwandc". iSplitL "HP1".
    - iApply "Hwand1". eauto.
    - iApply "Hwand2". eauto.
  }
  iIntros (v) "Hc !> Htok".

  (* create staged inv for first crash borrow *)
  iDestruct ("Htok") as "(Htok1&Htok)".
  iDestruct ("Htok") as "(Htok2&Htok)".
  iMod (staged_inv_create _ _ P1 Pc1 ⊤ _ mj with "[$] [$] Hitok1 [$] [$]") as "(Hval1&Hcancel1)".
  { auto. }

  (* create staged inv for second crash borrow *)
  iDestruct ("Htok") as "(Htok1&Htok)".
  iDestruct ("Htok") as "(Htok2&Htok)".
  iMod (staged_inv_create _ _ P2 Pc2 ⊤ _ mj with "[$] [$] Hitok2 [$] [$]") as "(Hval2&Hcancel2)".
  { auto. }

  iDestruct ("Htok") as "(Htok1&Htok)".
  iDestruct ("Htok") as "(Htok2&Htok)".
  iDestruct ("Htok") as "(Htok3&Htok)".
  iDestruct ("Htok") as "(Htok4&Htok)".
  iSpecialize ("Hc" with "[Htok1 Htok2 Htok3 Htok4 Hval1 Hval2]").
  { iSplitL "Htok1 Htok2 Hval1".
    - iExists P1, Pc1. iFrame "Hval1". iFrame "#". iFrame. iSplitL; eauto.
    - iExists P2, Pc2. iFrame "Hval2". iFrame "#". iFrame. iSplitL; eauto.
  }
  iDestruct (staged_inv_cancel_wpc_crash_modality with "Hcancel1") as "Hcancel1".
  iDestruct (staged_inv_cancel_wpc_crash_modality with "Hcancel2") as "Hcancel2".

  iDestruct ("Htok") as "(Htok1&Htok)".
  iDestruct (wpc_crash_modality_combine with "[$] [$] [$]") as "Hcombined".
  iModIntro. iSplitR "Hc".
  {
    iApply (wpc_crash_modality_wand with "Hcombined").
    iIntros "(?&?) !>". iApply "Hw3". iApply "Hwandc". by iFrame.
  }
  iSplit.
  - iDestruct "Hc" as "(Hc&_)".
    iApply (wpc_crash_modality_intro). auto.
  - iDestruct "Hc" as "(_&$)". eauto.
Qed.

Lemma wpc_crash_borrow_split k E e Φ Φc P Pc P1 P2 Pc1 Pc2 :
  language.to_val e = None →
  ▷ crash_borrow P Pc -∗
  ▷ (P -∗ P1 ∗ P2) -∗
  ▷ □ (P1 -∗ Pc1) -∗
  ▷ □ (P2 -∗ Pc2) -∗
  ▷ (Pc1 ∗ Pc2 -∗ Pc) -∗
  WPC e @ NotStuck; k; E {{ λ v, (crash_borrow P1 Pc1 ∗ crash_borrow P2 Pc2) -∗  (Φc ∧ Φ v) }} {{ Φc }} -∗
  WPC e @ NotStuck; k; E {{ Φ }} {{ Φc }}.
Proof.
  iIntros (Hnval) "Hborrow Hshift #Hwand1 #Hwand2 Hwandc Hwpc".
  iApply (wpc_crash_borrow_split' with "[$] [$] [$] [$] [$]"); eauto.
Qed.

Lemma wpc_crash_borrow_combine' k E e Φ Φc P Pc P1 P2 Pc1 Pc2 :
  language.to_val e = None →
  ▷ crash_borrow P1 Pc1 -∗
  ▷ crash_borrow P2 Pc2 -∗
  ▷▷ □ (P -∗ Pc) -∗
  ▷▷ (Pc -∗ (Pc1 ∗ Pc2)) -∗
  ▷▷ (P1 ∗ P2 ==∗ P) -∗
  WPC e @ NotStuck; k; E {{ λ v, (crash_borrow P Pc) -∗ (Φc ∧ Φ v) }} {{ Φc }} -∗
  WPC e @ NotStuck; k; E {{ Φ }} {{ Φc }}.
Proof.
  iIntros (Hnval) "Hborrow1 Hborrow2 #Hc Hwandc12 HwandP Hwpc".

  iDestruct "Hborrow1" as (??) "(#Hw1&Hw2&Hw3&Hinv1&Htok1&>Htok2)".
  iApply (wpc_later_tok_use2 with "[$]"); first done.
  iNext.
  iNext.
  iApply (wpc_staged_inv_inuse2); first done.
  iFrame "Htok1 Hinv1".
  iSplit.
  { iIntros. rewrite wpc_unfold. iDestruct ("Hwpc" $! _) as "(_&Hwpc)".
    iApply (wpc_crash_modality_wand with "Hwpc").
    iIntros "$". eauto. }
  iIntros "HP1". iIntros (mj_wp1 Hlt1).

  iDestruct "Hborrow2" as (??) "(#Hw1'&Hw2'&Hw3'&Hinv2&Htok2&_)".
  iApply (wpc_staged_inv_inuse); first done.
  iFrame "Hinv2".
  iSplit.
  { iIntros. rewrite wpc_unfold. iDestruct ("Hwpc" $! _) as "(_&Hwpc)".
    iApply (wpc_crash_modality_wand with "Hwpc").
    iIntros "HΦc".
    iModIntro. iFrame. iSplitR; first eauto.
    iApply wpc_crash_modality_intro. iApply "Hw3". iApply "Hw1". iApply "Hw2". iFrame. }

  iIntros "HP2". iIntros (mj_wp2 Hlt2).
  iApply wpc_fupd2.
  iApply (wpc_later_tok_invest with "[$]"); first done.
  iApply (wpc_pri_inv_tok_res).
  iIntros (Enew) "Hitok_new".
  iApply (wpc_pri_inv_tok_res).
  iIntros (Esplit) "Hitok_split".
  rewrite wpc_eq. iIntros (mj').

  iApply (wpc0_strong_mono with "Hwpc"); auto.
  iSplit; last first.
  { iIntros "$ !>". iSplitL "HP1 Hw3 Hw2".
    - iSplitR; first eauto. iApply wpc_crash_modality_intro. iApply "Hw3". iApply "Hw1". iApply "Hw2". eauto.
    - iApply "Hw3'". iApply "Hw1'". iApply "Hw2'". eauto.
  }
  iIntros (v) "Hc' !> Htok".

  iDestruct ("Htok") as "(Htok1&Htok)".
  iDestruct ("Htok") as "(Htok2&Htok)".
  iMod ("HwandP" with "[HP1 HP2 Hw2 Hw2']") as "HP".
  { iSplitL "HP1 Hw2".
    - iApply "Hw2". eauto.
    - iApply "Hw2'". eauto. }
  assert (∃ mj0, /2 < mj0 ∧ mj0 < mj_wp1 `min` mj_wp2)%Qp as (mj0&Hmj0).
  {
    apply Qp_lt_densely_ordered.
    apply Qp_min_glb1_lt; auto.
  }

  iMod (staged_inv_create _ _ P Pc ⊤ _ mj0 with "[$] [$] Hitok_new [$] [$]") as "(Hval&Hcancel)".
  { naive_solver. }

  iDestruct (staged_inv_cancel_wpc_crash_modality with "Hcancel") as "Hcancel".
  iDestruct ("Htok") as "(Htok1&Htok)".
  iDestruct ("Htok") as "(Htok2&Htok)".
  iAssert (wpc_crash_modality ⊤ mj0 (Pc1 ∗ Pc2))%I with "[Hwandc12 Hcancel]" as "Hcancel".
  { iApply (wpc_crash_modality_wand with "Hcancel"). iIntros "? !>".
    by iApply "Hwandc12". }
  iDestruct (wpc_crash_modality_split _ _ _ (mj_wp1 `min` mj_wp2) with "[$] [$] [$] [$]") as "Hcancel".
  { auto. }

  iMod (fupd2_mask_subseteq ∅ ∅) as "Hclo"; try set_solver+.
  iMod "Hcancel" as "(Hcancel1&Hcancel2)".
  iMod "Hclo" as "_". iModIntro.

  iSplitL "Hcancel2 Hw3'".
  { iApply (wpc_crash_modality_strong_wand with "Hcancel2"); auto; last first.
    { iIntros. iModIntro. iApply "Hw3'". iFrame. }
    split.
    - apply Qp_min_glb1_lt; auto.
    - apply Qp_le_min_r.
  }

  iDestruct ("Htok") as "(Htok1&Htok)".
  iDestruct ("Htok") as "(Htok2&Htok)".
  iSpecialize ("Hc'" with "[Hval Htok1 Htok2]").
  { iExists _, _. iFrame "Hval Htok1 #".
    iFrame. iSplitL; eauto. }

  iSplit.
  { iApply wpc_crash_modality_intro.
    iDestruct "Hc'" as "($&_)".
    iSplitR; first eauto.
    iApply (wpc_crash_modality_strong_wand with "Hcancel1"); auto.
    { split.
      - apply Qp_min_glb1_lt; auto.
      - apply Qp_le_min_l.
    }
    { iIntros. iModIntro. iApply "Hw3". iFrame. }
  }

  iSplitL "Hcancel1 Hw3".
  { iApply (wpc_crash_modality_strong_wand with "Hcancel1"); auto.
    { split.
      - apply Qp_min_glb1_lt; auto.
      - apply Qp_le_min_l.
    }
    { iIntros. iModIntro. iApply "Hw3". iFrame. }
  }

 iSplit.
 - iDestruct "Hc'" as "(Hc'&_)". iApply wpc_crash_modality_intro. auto.
 - iDestruct "Hc'" as "(_&$)". eauto.
Qed.

Lemma wpc_crash_borrow_combine k E e Φ Φc P Pc P1 P2 Pc1 Pc2 :
  language.to_val e = None →
  ▷ crash_borrow P1 Pc1 -∗
  ▷ crash_borrow P2 Pc2 -∗
  ▷ □ (P -∗ Pc) -∗
  ▷ (Pc -∗ (Pc1 ∗ Pc2)) -∗
  ▷ (P1 ∗ P2 ==∗ P) -∗
  WPC e @ NotStuck; k; E {{ λ v, (crash_borrow P Pc) -∗ (Φc ∧ Φ v) }} {{ Φc }} -∗
  WPC e @ NotStuck; k; E {{ Φ }} {{ Φc }}.
Proof.
  iIntros (Hnval) "Hborrow1 Hborrow2 #Hc Hwandc12 HwandP Hwpc".
  iApply (wpc_crash_borrow_combine' with "[$Hborrow1] [$Hborrow2] [$] [$Hwandc12] [$HwandP]"); eauto.
Qed.

Lemma wpc_crash_borrow_open_modify k E1 e Φ Φc P Pc:
  to_val e = None →
  crash_borrow P Pc -∗
  (Φc ∧ (P -∗ WPC e @ k; E1
                    {{λ v, ∃ P', P' ∗ □ (P' -∗ Pc) ∗ (crash_borrow P' Pc -∗ (Φc ∧ Φ v))}}
                    {{ Φc ∗ Pc }})) -∗
  WPC e @ k; E1 {{ Φ }} {{ Φc }}.
Proof.
  iIntros (Hnv) "H1 Hwp".
  iDestruct "H1" as (??) "(#Hw1&Hw2&#Hw3&Hval&Hltok1&Hltok2)".
  iApply (wpc_later_tok_use2 with "[$]"); first done.
  iNext. iNext.
  iApply (wpc_staged_inv with "[$Hval Hwp Hltok1 Hw2]").
  { auto. }
  iSplit.
  { iDestruct "Hwp" as "($&_)". eauto. }
  iIntros "HP".
  iDestruct "Hwp" as "(_&Hwp)".
  iSpecialize ("Hwp" with "[HP Hw2]").
  { iApply "Hw2". eauto. }
  iApply (wpc_strong_mono with "Hwp"); auto.
  { iSplit; last first.
    { iIntros "($&?) !>". iSplitR; first eauto. iApply "Hw3". eauto. }
    iIntros (?). iDestruct 1 as (P') "(HP&#Hwand&H)". iModIntro.
    iExists (P' ∧ Pc')%I. iSplitL "HP Hw3".
    { iSplit; iFrame. iApply "Hw3". iApply "Hwand". eauto. }
    iSplitL "".
    { iIntros "(_&$)". eauto. }
    iIntros "Hs".
    iSplit.
    * iIntros "Hltok". iDestruct ("H" with "[-]") as "($&_)".
      iExists _, _. iFrame "Hs # ∗". iNext. iIntros "($&_)".
    * iIntros "Hltok". iDestruct ("H" with "[-]") as "(_&$)".
      iExists _, _. iFrame "Hs # ∗". iNext. iIntros "($&_)".
  }
Qed.

Lemma crash_borrow_crash_wand P Pc:
  crash_borrow P Pc -∗ □ (P -∗ Pc).
Proof. iDestruct 1 as (??) "($&_)". Qed.

Lemma crash_borrow_wpc_nval' E Pc P P' R :
  crash_borrow P Pc -∗
  ▷ (P -∗ wp_nval E (□ (P' -∗ Pc) ∗ P' ∗ R)) -∗
  wpc_nval E (R ∗ crash_borrow P' Pc).
Proof.
  iIntros "Hborrow Hwand".
  iDestruct "Hborrow" as (??) "(#Hw1&Hw2&#Hw3&Hval&Hltok1&Hltok2)".
  iApply (wp_nval_wpc_nval with "[$]"). iNext.
  iApply (wp_nval_strong_mono with "[-Hltok1]").
  { iApply (staged_inv_wp_nval _ _ _ P' (□ (P' -∗ Pc) ∗ R) with "[$Hval]"); auto.
    iNext. iIntros "HPs'". iDestruct ("Hw2" with "[$]") as "HP".
    iDestruct ("Hwand" with "[$]") as "H".
    iApply (wp_nval_strong_mono with "H").
    iIntros "(#Hshift&$&$)".
    iModIntro. iFrame "#".
    { iModIntro. iIntros "?". iApply "Hw3". iApply "Hshift". iFrame. }
  }
  iIntros "((#Hw4&HR)&Hval)".
  iModIntro. iIntros "Hltok2".
  iDestruct "Hval" as (??????) "(?&?&?&?&?&?&?)".
  iFrame "HR".
  iExists P', Pc'.
  iFrame "#".
  iSplitR; first eauto.
  iFrame.
  iExists _, _, _, _, _, _. iFrame "∗".
Qed.

Lemma crash_borrow_wpc_nval E Pc P P' R :
  crash_borrow P Pc -∗
  ▷ (P -∗ |NC={E}=> □ (P' -∗ Pc) ∗ P' ∗ R) -∗
  wpc_nval E (R ∗ crash_borrow P' Pc).
Proof.
  iIntros "Hborrow Hwand".
  iApply (crash_borrow_wpc_nval' with "[$]"). iNext. iIntros "HP".
  iApply (ncfupd_wp_nval). iMod ("Hwand" with "[$]") as "(#Hwand&HP'&HR)".
  iModIntro. iApply wp_nval_intro.
  iFrame. eauto.
Qed.

Lemma crash_borrow_wp_nval E Pc P P' R :
  crash_borrow P Pc -∗
  ▷ (P -∗ wp_nval E (□ (P' -∗ Pc) ∗ P' ∗ R)) -∗
  wp_nval E (R ∗ crash_borrow P' Pc).
Proof.
  iIntros "Hborrow Hwand".
  iDestruct "Hborrow" as (??) "(#Hw1&Hw2&#Hw3&Hval&Hltok1&Hltok2)".
  iApply (wp_nval_strong_mono with "[-Hltok2 Hltok1]").
  { iApply (staged_inv_wp_nval _ _ _ P' (□ (P' -∗ Pc) ∗ R) with "[$Hval]"); auto.
    iNext. iIntros "HPs'". iDestruct ("Hw2" with "[$]") as "HP".
    iDestruct ("Hwand" with "[$]") as "H".
    iApply (wp_nval_strong_mono with "H").
    iIntros "(#Hshift&$&$)".
    iModIntro. iFrame "#".
    { iModIntro. iIntros "?". iApply "Hw3". iApply "Hshift". iFrame. }
  }
  iIntros "((#Hw4&HR)&Hval)".
  iModIntro.
  iDestruct "Hval" as (??????) "(?&?&?&?&?&?&?)".
  iFrame "HR".
  iExists P', Pc'.
  iFrame "#".
  iSplitR; first eauto.
  iFrame.
  iExists _, _, _, _, _, _. iFrame "∗".
Qed.

Lemma crash_borrow_wp_nval_sepM `{Countable A} {B} E (P: A → B → iProp Σ) Q Q' R m:
  ([∗ map] i ↦ x ∈ m, crash_borrow (Q i x) (P i x)) -∗
  (([∗ map] i ↦ x ∈ m, Q i x) -∗
   wp_nval E  (□ ([∗ map] i ↦ x ∈ m, ((Q' i x) -∗ (P i x))) ∗
              ([∗ map] i ↦ x ∈ m, (Q' i x)) ∗ R)) -∗
  wp_nval E (R ∗ ([∗ map] i ↦ x ∈ m, crash_borrow (Q' i x) (P i x))).
Proof.
  revert R.
  induction m as [|i x m] using map_ind.
  {
    iIntros (?) "_ Hrestore".
    iDestruct ("Hrestore" with "[]") as "H";
      first by (iApply big_sepM_empty; trivial).
    iApply (wp_nval_strong_mono with "H"). iIntros "(_&_&R)". iModIntro.
    rewrite big_sepM_empty; trivial. iFrame.
  }
  iIntros (?) "Hcrash_invs Hrestores".
  iDestruct (big_sepM_insert with "Hcrash_invs")
    as "[Hcrash_inv Hcrash_invs]";
    first by assumption.
  iDestruct (IHm (crash_borrow (Q' i x) (P i x) ∗ R)%I with "Hcrash_invs [Hrestores Hcrash_inv]") as "H".
  {
    iIntros "HQs".
    iDestruct (
      crash_borrow_wp_nval _ _ _ _
      (
        ([∗ map] i↦x ∈ m, Q' i x) ∗
        □ ([∗ map] i↦x ∈ m, (Q' i x -∗ P i x)) ∗
        R
      )%I
      with "Hcrash_inv [Hrestores HQs]"
    ) as "H".
    {
      iNext.
      iIntros "HQ".
      iDestruct ("Hrestores" with "[HQs HQ]") as "H".
      {
        iApply big_sepM_insert; first by assumption.
        iFrame.
      }
      iApply (wp_nval_strong_mono with "H").
      iIntros "(#Hstatuses&HQ's&HR)".
      iDestruct (big_sepM_insert with "HQ's")
        as "[HQ' HQ's]";
        first by assumption. iModIntro.
      iDestruct (big_sepM_insert with "Hstatuses")
        as "[Hstatus Hstatuses']";
        first by assumption.
      iFrame "∗ #".
      trivial.
    }
    iApply (wp_nval_strong_mono with "H"). iIntros "((?&?&?)&?)".
    iFrame.
    trivial.
  }
  iApply (wp_nval_strong_mono with "H").
  iIntros "((?&?)&?)".
  iModIntro.
  iFrame.
  iApply big_sepM_insert; first by assumption.
  iFrame.
Qed.

Lemma wpc_crash_borrow_open k E1 e Φ Φc P Pc:
  to_val e = None →
  crash_borrow P Pc -∗
  (Φc ∧ (P -∗ WPC e @ k; E1
                    {{λ v, P ∗ (crash_borrow P Pc -∗ (Φc ∧ Φ v))}}
                    {{ Φc ∗ Pc }})) -∗
  WPC e @ k; E1 {{ Φ }} {{ Φc }}.
Proof.
  iIntros (Hnv) "H1 Hwp".
  iDestruct (crash_borrow_crash_wand with "[$]") as "#Hw".
  iApply (wpc_crash_borrow_open_modify with "[$] [Hwp]"); auto.
  iSplit; first by iDestruct "Hwp" as "($&_)".
  iIntros "HP".
  iDestruct "Hwp" as "(_&Hwp)".
  iSpecialize ("Hwp" with "[$]").
  iApply (wpc_strong_mono with "Hwp"); auto.
  { iSplit; last first.
    { eauto. }
    iIntros (?) "(HP&H)". iModIntro.
    iExists P. iFrame. eauto. }
Qed.

Lemma wpc_crash_borrow_open_cancel k E1 e Φ Φc P Pc:
  to_val e = None →
  crash_borrow P Pc -∗
  (Φc ∧ (P -∗ ∀ mj, ⌜ (/2 < mj)%Qp ⌝ -∗ WPC e @ k; E1
                    {{λ v, wpc_crash_modality ⊤ mj Pc ∗ (Φc ∧ Φ v)}}
                    {{ Φc ∗ Pc }})) -∗
  WPC e @ k; E1 {{ Φ }} {{ Φc }}.
Proof.
  iIntros (Hnv) "H1 Hwp".
  iDestruct "H1" as (??) "(#Hw1&Hw2&#Hw3&Hval&Hltok1&Hltok2)".
  iApply (wpc_later_tok_use2 with "[$]"); first done.
  iNext. iNext.
  iApply (wpc_staged_inv_inuse2 with "[$Hval Hwp Hltok1 Hw2]").
  { auto. }
  iFrame.
  iSplit.
  { iIntros (?). iApply wpc_crash_modality_intro. iDestruct "Hwp" as "($&_)". eauto. }
  iIntros "HP".
  iDestruct "Hwp" as "(_&Hwp)".
  iSpecialize ("Hwp" with "[HP Hw2]").
  { iApply "Hw2". eauto. }
  iIntros (mj Hlt).
  iSpecialize ("Hwp" $! mj Hlt).
  iApply (wpc_strong_mono with "Hwp"); auto.
  { iSplit; last first.
    { iIntros "($&?) !>". iSplitR; first eauto. iApply wpc_crash_modality_intro. iApply "Hw3". eauto. }
    iIntros (?).
    iIntros "(Hwpc&HΦ)".
    iModIntro.
    iSplitL "Hwpc".
    { iApply (wpc_crash_modality_wand with "Hwpc"). iIntros "H". iApply "Hw3". eauto. }
    iSplit.
    { iApply wpc_crash_modality_intro. iIntros. iDestruct "HΦ" as "($&_)". }
    iIntros "Hltok". iDestruct "HΦ" as "(_&$)". }
Qed.

Opaque crash_borrow.
Lemma crash_borrow_wpc_nval_sepM `{Countable A} {B} E (P: A → B → iProp Σ) Q Q' R m:
  ([∗ map] i ↦ x ∈ m, crash_borrow (Q i x) (P i x)) -∗
  (([∗ map] i ↦ x ∈ m, Q i x) -∗
   |NC={E}=> (□ [∗ map] i ↦ x ∈ m, ((Q' i x) -∗ (P i x))) ∗ ([∗ map] i ↦ x ∈ m, (Q' i x)) ∗ R) -∗
  wpc_nval E (R ∗ ([∗ map] i ↦ x ∈ m, crash_borrow (Q' i x) (P i x))).
Proof.
  iInduction m as [| i x m Hnin] "_"  using map_ind.
  - iIntros "_ H".
    iApply ncfupd_wpc_nval.
    iMod ("H" with "[]") as "(_&_&R)".
    { by rewrite big_sepM_empty. }
    iModIntro. iApply wpc_nval_intro; eauto.
  - iIntros "H Hwand".
    iDestruct (big_sepM_insert with "H") as "(H&Hrest)"; auto.
    iDestruct (crash_borrow_wpc_nval' E _ _ (Q' i x) (R ∗ [∗ map] i ↦ x ∈ m, crash_borrow (Q' i x) (P i x))
                 with "H [Hrest Hwand]") as "H".
    { iNext. iIntros "HQ".
      iDestruct (crash_borrow_wp_nval_sepM E P Q Q' (□ (Q' i x -∗ P i x) ∗ R ∗ (Q' i x))
                   with "Hrest [Hwand HQ]") as "H".
      { iIntros "H".
        iApply (ncfupd_wp_nval).
        iMod ("Hwand" with "[HQ H]") as "(#H1&H2&?)".
        { iApply big_sepM_insert; auto; iFrame. }
        iModIntro. iApply wp_nval_intro. iFrame.
        iDestruct (big_sepM_insert with "H1") as "($&$)"; auto.
        iDestruct (big_sepM_insert with "H2") as "($&$)"; auto.
      }
      iApply (wp_nval_strong_mono with "H"). by iIntros "(($&$&$)&$)".
    }
    iApply (wpc_nval_strong_mono with "H"). iIntros "!> (($&H1)&H2)".
    iModIntro. iApply big_sepM_insert; auto; iFrame.
Qed.


End crash_borrow_def.

Opaque crash_borrow.
