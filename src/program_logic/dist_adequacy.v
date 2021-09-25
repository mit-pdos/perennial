From iris.proofmode Require Import tactics.
From iris.algebra Require Import gmap auth agree gset coPset.
From Perennial.base_logic.lib Require Import wsat.
From Perennial.program_logic Require Export weakestpre.
From Perennial.program_logic Require Export crash_lang recovery_weakestpre dist_weakestpre.
From Perennial.program_logic Require Import crash_adequacy.
Import uPred.

Set Default Proof Using "Type".

Section distributed_adequacy.
Context `{!irisGS Λ Σ}.
Context (CS : crash_semantics Λ).

Context (mj: fracR).
(* The IH of the theorems here requires working with some fixed choice of mj in the wpc0 form,
   instead of wpc. So, we introduce here a notation to insert the mj explicitly to porting these proofs easier *)
Local Notation "'WPC' e @ E1 {{ Φ } } {{ Φc } }" := (wpc0 NotStuck mj E1 e%E Φ Φc)
  (at level 20, e, Φ, Φc at level 200, only parsing) : bi_scope.
Local Notation "'WPC' e @ s ; E1 {{ Φ } } {{ Φc } }" := (wpc0 s mj E1 e%E Φ Φc)
  (at level 20, e, Φ, Φc at level 200, only parsing) : bi_scope.
Local Notation "'WPC' e @ s ; E1 {{ Φ } } {{ Φc } }" := (wpc0 s mj E1 e%E Φ Φc)
  (at level 20, e, Φ, Φc at level 200, only parsing) : stdpp_scope.

Implicit Types s : stuckness.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types Φinv : generationGS Λ Σ → iProp Σ.
Implicit Types Φc : generationGS Λ Σ → val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.

Definition wptp (gen : generationGS Λ Σ) s tpool :=
  ([∗ list] ef ∈ tpool, WPC ef @ s; ⊤ {{ fork_post }} {{ True }})%I.

Definition wpnode (gen : generationGS Λ Σ) (dn: dist_node) :=
  (match tpool dn with
  | [] => False%I
  | e :: tp =>
    ∃ Φ Φinv Φr,
    wpr0 CS NotStuck mj gen ⊤ e (boot dn) Φ Φinv Φr (* to be used after a reboot *) ∗
    wptp gen NotStuck tp
  end)%I.

Definition stwpnode (gen : generationGS Λ Σ) (dn: dist_node) : iProp Σ :=
  (state_interp (local_state dn) (pred (length (tpool dn))) ∗
   NC 1) ∗
  wpnode gen dn.

Definition stwpnodes (dns: list dist_node) : iProp Σ :=
  [∗ list] dn ∈ dns, ∃ gen, stwpnode gen dn.

Lemma stwpnode_step gen eb t1 σ1 g1 D t2 σ2 g2 κ κs ns:
  step (t1, (σ1,g1)) κ (t2, (σ2,g2)) →
  global_state_interp g1 ns mj D (κ ++ κs) -∗
  stwpnode gen {| boot := eb; tpool := t1; local_state := σ1 |} -∗
  ||={⊤|⊤,∅|∅}=> ||▷=>^(S $ num_laters_per_step ns) ||={∅|∅, ⊤|⊤}=>
  global_state_interp g2 (step_count_next ns) mj D κs ∗
  stwpnode gen {| boot := eb; tpool := t2; local_state := σ2 |}.
Proof.
  iIntros (Hstep) "Hg Hnode".
  iDestruct "Hnode" as "((Hσ&HNC)&Hwptp)".
  destruct t1; first done. simpl.
  iDestruct "Hwptp" as (Φ Φinv Φr) "(Hwpr&Hwptp)". simpl.
  iPoseProof (crash_adequacy.wptp_step with "[$Hσ] [Hg] [Hwpr] [Hwptp] [HNC]") as "H"; eauto.
  { rewrite wpr0_unfold/wpr0_pre. eauto. }
  iMod "H" as (e2 t2' ->) "H".
  iMod "H". iModIntro. simpl. iMod "H". iModIntro. iNext.
  iApply (step_fupd2N_wand with "H"). iIntros "H".
  iMod "H" as "(Hσ&Hg&Hwpr&Hwptp&HNC)".
  iFrame. iModIntro.
  simpl. iExists Φ, Φinv, Φr.
  rewrite wpr0_unfold/wpr0_pre. eauto.
Qed.

Lemma stwpnode_crash gen eb t1 σ1 g σ2 κs ns D:
  crash_prim_step CS σ1 σ2 →
  global_state_interp g ns mj D κs -∗
  stwpnode gen {| boot := eb; tpool := t1; local_state := σ1 |} -∗
  ||={⊤|⊤, ∅|∅}=> ||▷=>^(num_laters_per_step ns) ||={∅|∅,⊤|⊤}=> ▷ |={⊤}=> ∃ gen',
  global_state_interp g (step_count_next ns) mj D κs ∗
  stwpnode gen' {| boot := eb; tpool := [eb]; local_state := σ2 |}.
Proof.
  iIntros (Hstep) "Hg Hnode".
  iDestruct "Hnode" as "((Hσ&HNC)&Hwptp)".
  destruct t1; first done. simpl.
  iDestruct "Hwptp" as (Φ Φinv Φr) "(Hwpr&Hwptp)".
  iMod (NC_upd_C with "HNC") as "#HC".
  rewrite wpr0_unfold/wpr0_pre.
  iPoseProof (@fupd2_mask_subseteq _ _ ⊤ ⊤ ⊤ (⊤ ∖ D)) as "Hclo"; try set_solver+.
  iMod ("Hclo").
  iMod (wpc0_crash with "Hwpr [Hg] []") as "H".
  { eauto. }
  { iFrame "#". }
  iModIntro.
  iApply (step_fupd2N_wand with "H"). iIntros "H".
  iMod "H" as "(Hg&H)". iMod "Hclo".
  iMod ("H" with "[//] [$] [Hg]") as "H".
  { eauto. }
  iModIntro. iNext.
  iClear "HC".
  unshelve (iMod NC_alloc as (Hc') "HNC").
  { constructor. apply _. }
  iSpecialize ("H" with "HNC").
  iMod "H".
  iDestruct "H" as (p') "(Hσ&Hg&(_&Hwpr)&HNC)".
  iModIntro.
  iFrame.
  iExists (generation_from_params Hc' p'). iFrame.
  rewrite /wpnode/=.
  iExists _, _, _. iFrame. rewrite /wptp. rewrite big_sepL_nil. eauto.
Qed.

Lemma stwpnodes_step dns1 g1 ns D dns2 g2 κ κs :
  dist_step (CS := CS) (dns1, g1) κ (dns2, g2) →
  global_state_interp g1 ns mj D (κ ++ κs) -∗
  stwpnodes dns1 -∗
  ||={⊤|⊤,∅|∅}=> ||▷=>^(S $ num_laters_per_step ns) ||={∅|∅, ⊤|⊤}=>
  global_state_interp g2 (step_count_next ns) mj D κs ∗
  stwpnodes dns2.
Proof.
  iIntros (Hstep) "Hg Hnodes".
  inversion Hstep as [ρ1 κs' ρ2 m eb t1 σ1 t2 σ2 Hlookup1 Hlookup2 Hprim |
                      ρ1 ρ2 m eb σ1 σ2 tp Hlookup1 Heq1 Heq2 Hcrash].
  - subst. rewrite /stwpnodes.
    iDestruct (big_sepL_insert_acc with "Hnodes") as "(Hdn&Hnodes)"; first eassumption.
    iDestruct "Hdn" as (ct) "Hdn".
    iDestruct (stwpnode_step with "[$] [$]") as "H"; first eassumption.
    iApply (step_fupd2N_inner_wand with "H"); auto.
    iIntros "($&Hnode)".
    simpl in Hlookup2. rewrite Hlookup2.
    iApply "Hnodes". iExists _. eauto.
  - subst. rewrite /stwpnodes.
    iDestruct (big_sepL_insert_acc with "Hnodes") as "(Hdn&Hnodes)"; first eassumption.
    iDestruct "Hdn" as (ct) "Hdn".
    iDestruct (stwpnode_crash with "[$] [$]") as "H"; first eassumption.
    rewrite Nat_iter_S_r.
    iMod "H". iModIntro. iApply (step_fupd2N_wand with "H"). iIntros "H".
    iMod "H". iMod (fupd2_mask_subseteq ∅ ∅) as "Hclo"; auto.
    iModIntro. iNext. iModIntro. iMod "Hclo".
    iApply (fupd_fupd2).
    iMod "H" as (ct') "(Hg&Hnode)". rewrite app_nil_l.
    simpl in Heq2. rewrite Heq2. iFrame.
    iModIntro.
    simpl in Heq1. rewrite Heq1.
    iApply "Hnodes". iExists _. eauto.
Qed.

Local Fixpoint steps_sum (num_laters_per_step step_count_next : nat → nat) (start ns : nat) : nat :=
  match ns with
  | O => 0
  | S ns =>
    S $ num_laters_per_step start + steps_sum num_laters_per_step step_count_next (step_count_next start) ns
  end.

Lemma stwpnodes_steps n dns1 g1 ns D dns2 g2 κs κs' :
  dist_nsteps (CS := CS) n (dns1, g1) κs (dns2, g2) →
  global_state_interp g1 ns mj D (κs ++ κs') -∗
  stwpnodes dns1 -∗
  ||={⊤|⊤,∅|∅}=> ||▷=>^(steps_sum num_laters_per_step step_count_next ns n) ||={∅|∅, ⊤|⊤}=>
  global_state_interp g2 (Nat.iter n step_count_next ns) mj D κs' ∗
  stwpnodes dns2.
Proof.
  revert dns1 dns2 κs κs' g1 ns g2.
  induction n as [|n IH]=> dns1 dns2 κs κs' g1 ns g2 /=.
  { inversion_clear 1; iIntros "? ?" => /=.
    iFrame. by iApply fupd2_mask_subseteq. }
  iIntros (Hsteps) "Hσ He". inversion_clear Hsteps as [|?? [t1' σ1']].
  rewrite -(assoc_L (++)) Nat_iter_add.
  iMod (stwpnodes_step with "Hσ He") as "H"; first eauto; simplify_eq.
  iModIntro. iApply step_fupd2N_S_fupd2. iApply (step_fupd2N_wand with "H").
  iIntros ">(Hσ & He)". iMod (IH with "Hσ He") as "IH"; first done. iModIntro.
  iApply (step_fupd2N_wand with "IH"). iIntros ">IH".
  iDestruct "IH" as "[??]".
  rewrite -Nat_iter_S_r //=.
  iFrame. eauto.
Qed.

Lemma stwpnodes_strong_adequacy n dns1 g1 ns D dns2 g2 κs κs' :
  dist_nsteps (CS := CS) n (dns1, g1) κs (dns2, g2) →
  global_state_interp g1 ns mj D (κs ++ κs') -∗
  (|={⊤}=> stwpnodes dns1) -∗
  ||={⊤|⊤,∅|∅}=> ||▷=>^(steps_sum num_laters_per_step step_count_next ns n) ||={∅|∅, ⊤|⊤}=>
  (▷^(S (S (num_laters_per_step (Nat.iter n step_count_next ns))))
      (⌜ ∀ dn e, dn ∈ dns2 → e ∈ tpool dn → not_stuck e (local_state dn) g2 ⌝)) ∗
  global_state_interp g2 (Nat.iter n step_count_next ns) mj D κs' ∗
  stwpnodes dns2.
Proof.
  iIntros (Hstep) "Hg >Ht".
  iMod (stwpnodes_steps with "Hg Ht") as "Hgt"; first done.
  iModIntro. iApply (step_fupd2N_wand with "Hgt").
  iMod 1 as "(Hg & Ht)".
  iMod (fupd2_plain_keep_l ⊤ ⊤
    (▷^(S (S (num_laters_per_step ((Nat.iter n step_count_next ns)))))
      (⌜ ∀ dn e, dn ∈ dns2 → e ∈ tpool dn → not_stuck e (local_state dn) g2 ⌝))%I
    (global_state_interp g2 (Nat.iter n step_count_next ns) mj D κs' ∗
    stwpnodes dns2)%I
    with "[$Hg $Ht]") as "(Hsafe&Hg&Ht)".
  { iIntros "(Hg & Ht)" (dn e' Hin1 Hin2).
    rewrite /stwpnodes.
    eapply elem_of_list_lookup_1 in Hin1 as (i&Hlookup1).
    iDestruct (big_sepL_lookup with "Ht") as "Hdn"; first eassumption.
    iDestruct "Hdn" as (ct) "Hnode".
    rewrite /stwpnode.
    iDestruct "Hnode" as "((Hσ&HNC)&Hwptp)".
    rewrite /wpnode. destruct (tpool dn) as [| hd tp]; first done.
    iDestruct "Hwptp" as (???) "(Hwpr&Ht)".
    apply elem_of_cons in Hin2 as [<-|(t1''&t2''&->)%elem_of_list_split].
    - rewrite wpr0_unfold/wpr0_pre.
      iPoseProof (wpc_safe with "Hσ [Hg] Hwpr") as "H".
      { eauto. }
      iMod ("H" with "[HNC]") as "H".
      { iFrame. }
      iModIntro. iNext. iNext. iNext. eauto.
    - iDestruct "Ht" as "(_ & He' & _)".
      iPoseProof (wpc_safe with "Hσ [Hg] He'") as "H".
      { eauto. }
      iMod ("H" with "[HNC]") as "H".
      { iFrame. }
      iModIntro. iNext. iNext. iNext. eauto.
  }
  iModIntro. iFrame.
Qed.

End distributed_adequacy.

Theorem wpd_strong_adequacy Σ Λ CS `{!invGpreS Σ} `{!crashGpreS Σ}
  nsinit (ebσs : list node_init_cfg) g1 n κs dns2 g2 φ f1 f2 :
  (∀ `(Hinv : !invGS Σ),
     ⊢ |={⊤}=> ∃
       (global_stateI : global_state Λ → nat → fracR → coPset → list (observation Λ) → iProp Σ)
       (fork_post : val Λ → iProp Σ) Hpf1a Hpf1b,
       let HI := IrisGS Λ Σ Hinv (global_stateI) (fork_post) f1 f2 Hpf1a Hpf1b in
       global_stateI g1 nsinit 1%Qp ∅ κs  ∗
       wpd CS ⊤ ebσs ∗
       (⌜ ∀ dn, dn ∈ dns2 → not_stuck_node dn g2 ⌝ -∗
         global_stateI g2 (Nat.iter n f2 nsinit) 1%Qp ∅ [] -∗
         (* Under these assumptions, and while opening all invariants, we
         can conclude [φ] in the logic. After opening all required invariants,
         one can use [fupd_mask_subseteq] to introduce the fancy update. *)
         |={⊤,∅}=> ⌜ φ ⌝ )) →
  dist_nsteps (CS := CS) n (starting_dist_cfg ebσs g1) κs (dns2, g2) →
  (* Then we can conclude [φ] at the meta-level. *)
  φ.
Proof.
  intros Hwp ?.
  apply (step_fupd2N_soundness_strong _ (steps_sum f1 f2 nsinit n
         + S (S (f1 (Nat.iter n f2 nsinit))))) => Hinv HEQ.
(*  (Nat.iter (steps_sum n)) (S (S (f1 (Nat.iter n f2 nsinit)))))) => Hinv HEQ. *)
  rewrite Nat_iter_add.
  iMod Hwp as (global_stateI fork_post) "Hwp".
  iDestruct "Hwp" as (Hpf1a Hpf1b) "(Hg & Hwp & Hφ)".
  set (HI := IrisGS Λ Σ Hinv (global_stateI) (fork_post) f1 f2 Hpf1a Hpf1b).
  iMod (stwpnodes_strong_adequacy _
               1%Qp n _ _ nsinit _ _ _ _ []
    with "[Hg] [Hwp]") as "H"; first done.
  { rewrite app_nil_r /=. iExact "Hg". }
  { rewrite /stwpnodes/wpd.
    iApply big_sepL_fmap.
    iApply big_sepL_fupd.
    iApply (big_sepL_impl with "Hwp").
    iIntros "!#" (i ρ Hlookup) "H".
    iMod NC_alloc as (Hc) "HNC".
    iMod ("H" $! Hc) as (stateI Φ Φrx Φinv) "(Hσ&Hwp)".
    set (HG := GenerationGS Λ Σ Hc stateI). iExists HG.
    rewrite /stwpnode.
    rewrite /=. iFrame "HNC Hσ".
    rewrite /wpnode/=.
    iModIntro. iExists Φ, Φinv, Φrx.
    rewrite /wptp big_sepL_nil right_id.
    by iApply wpr0_wpr.
  }
  iModIntro.
  iApply (step_fupd2N_wand with "H").
  iIntros "H".
  iApply step_fupd2N_S_fupd2. simpl. iMod "H".
  iMod (fupd2_mask_subseteq ∅ ∅) as "Hclo"; try set_solver+.
  iModIntro. iNext. iModIntro.
  iApply (step_fupd2N_later); first auto.
  iModIntro. iNext. iModIntro.
  iNext. iMod "Hclo" as "_".
  iDestruct "H" as "(%Hnotstuck&Hg&_)".
  iMod (fupd2_mask_subseteq ⊤ ∅) as "Hclo"; try set_solver+.
  iApply (fupd_fupd2).
  iApply ("Hφ" with "[] [$]").
  { iPureIntro. intros dn Hin e Hin'. eapply Hnotstuck; eauto. }
Qed.

Record dist_adequate {Λ CS} (ρs: list (@node_init_cfg Λ)) (g : global_state Λ)
    (φinv: global_state Λ → Prop)  := {
  dist_adequate_not_stuck dns' g' dn :
   rtc (erased_dist_step (CS := CS)) (starting_dist_cfg ρs g) (dns', g') →
   dn ∈ dns' → not_stuck_node dn g';
  dist_adequate_inv dns' g' :
   rtc (erased_dist_step (CS := CS)) (starting_dist_cfg ρs g) (dns', g') →
   φinv g'
}.

Lemma dist_adequate_alt {Λ CS} ebσ g1 φinv :
  dist_adequate (Λ := Λ) (CS := CS) ebσ g1 φinv ↔ ∀ dns2 g2,
    rtc (erased_dist_step (CS := CS)) (starting_dist_cfg ebσ g1) (dns2, g2) →
      (∀ dn, dn ∈ dns2 → not_stuck_node dn g2) ∧
      (φinv g2).
Proof.
  split.
  - intros [] ???; naive_solver.
  - constructor; naive_solver.
Qed.

Corollary wpd_dist_adequacy_inv Σ Λ CS `{!invGpreS Σ} `{!crashGpreS Σ} nsinit
          ebσs g φinv f1 f2:
  (∀ `(Hinv : !invGS Σ) κs,
     ⊢ |={⊤}=> ∃
       (global_stateI : global_state Λ → nat → fracR → coPset → list (observation Λ) → iProp Σ)
       (fork_post : val Λ → iProp Σ) Hpf1a Hpf1b,
       let HI := IrisGS Λ Σ Hinv (global_stateI) (fork_post) f1 f2 Hpf1a Hpf1b in
       global_stateI g nsinit 1%Qp ∅ κs  ∗
       wpd CS ⊤ ebσs ∗
       (∀ g κs ns, global_stateI g ns 1%Qp ∅ κs -∗ |={⊤, ∅}=> ⌜ φinv g ⌝)) →
  dist_adequate (CS := CS) ebσs g (λ g, φinv g).
Proof.
  intros Hwp.
  apply dist_adequate_alt.
  intros dns2 g2 Hsteps.
  apply erased_dist_steps_nsteps in Hsteps as [n [κs Hsteps]].
  eapply (wpd_strong_adequacy Σ _ _); [| by eauto ] => ?.
  iMod Hwp as (global_stateI fork_post) "Hwp".
  iDestruct "Hwp" as (Hpf1a Hpf1b) "(Hg&Hwp&Hφ)".
  iModIntro. iExists global_stateI, fork_post.
  iExists Hpf1a, Hpf1b.
  iFrame. iIntros "%Hns Hg". iMod ("Hφ" with "[$]") as %Hφ. iPureIntro; eauto.
Qed.
