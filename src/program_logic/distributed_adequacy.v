From iris.proofmode Require Import tactics.
From iris.algebra Require Import gmap auth agree gset coPset.
From Perennial.base_logic.lib Require Import wsat.
From Perennial.program_logic Require Export weakestpre.
From Perennial.program_logic Require Export crash_lang recovery_weakestpre distributed_weakestpre.
From Perennial.program_logic Require Import crash_adequacy.
Import uPred.

Set Default Proof Using "Type".

Section distributed_adequacy.
Context `{!perennialG Λ CS T Σ}.
Context `{!groveG Λ CS Σ}.

Context (mj: nat).
(* The IH of the theorems here requires working with some fixed choice of mj in the wpc0 form,
   instead of wpc. So, we introduce here a notation to insert the mj explicitly to porting these proofs easier *)
Local Notation "'WPC' e @ k ; E1 {{ Φ } } {{ Φc } }" := (wpc0 NotStuck k%nat mj E1 e%E Φ Φc)
  (at level 20, e, Φ, Φc at level 200, only parsing) : bi_scope.
Local Notation "'WPC' e @ s ; k ; E1 {{ Φ } } {{ Φc } }" := (wpc0 s k%nat mj E1 e%E Φ Φc)
  (at level 20, e, Φ, Φc at level 200, only parsing) : bi_scope.
Local Notation "'WPC' e @ s ; k ; E1 {{ Φ } } {{ Φc } }" := (wpc0 s k%nat mj E1 e%E Φ Φc)
  (at level 20, e, Φ, Φc at level 200, only parsing) : stdpp_scope.

Implicit Types s : stuckness.
Implicit Types k : nat.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types Φinv : crashG Σ → pbundleG T Σ → iProp Σ.
Implicit Types Φc : crashG Σ → pbundleG T Σ → val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.

Definition wptp (ct : crashG Σ * pbundleG T Σ) s k tpool :=
  let Hc := fst ct in
  let t := snd ct in
  ([∗ list] ef ∈ tpool, WPC ef @ s; k; ⊤ {{ fork_post }} {{ True }})%I.

Definition wpnode (ct : crashG Σ * pbundleG T Σ) k (dn: dist_node) :=
  (⌜ equal_global_inG ct ⌝ ∗
  match tpool dn with
  | [] => False%I
  | e :: tp =>
    ∃ Φ Φinv Φr,
    wpr0 NotStuck k mj (fst ct) (snd ct) ⊤ e (boot dn) Φ Φinv Φr ∗
    wptp ct NotStuck k tp
  end)%I.

Definition stwpnode (ct : crashG Σ * pbundleG T Σ) k (dn: dist_node) : iProp Σ :=
  (let Hc := fst ct in
   let t := snd ct in
   state_interp (local_state dn) (pred (length (tpool dn))) ∗
   NC 1) ∗
  wpnode ct k dn.

Definition stwpnodes k (dns: list dist_node) : iProp Σ :=
  [∗ list] dn ∈ dns, ∃ ct, stwpnode ct k dn.

Existing Instance grove_invG | 0.

Lemma stwpnode_step ct k eb t1 σ1 g1 t2 σ2 g2 κ κs ns:
  step (t1, (σ1,g1)) κ (t2, (σ2,g2)) →
  grove_global_state_interp g1 ns (κ ++ κs) -∗
  stwpnode ct k {| boot := eb; tpool := t1; local_state := σ1 |} -∗
  |={⊤,∅}=> |={∅}▷=>^(S $ grove_num_laters_per_step ns) |={∅, ⊤}=>
  grove_global_state_interp g2 (S ns) κs ∗
  stwpnode ct k {| boot := eb; tpool := t2; local_state := σ2 |}.
Proof.
  iIntros (Hstep) "Hg Hnode".
  destruct ct as (Hc&t).
  iDestruct "Hnode" as "((Hσ&HNC)&(%Hequal&Hwptp))".
  destruct Hequal as (Hglobal&Hnum&Hinv).
  destruct t1; first done. simpl.
  rewrite -Hglobal -Hnum -Hinv.
  iDestruct "Hwptp" as (Φ Φinv Φr) "(Hwpr&Hwptp)".
  iPoseProof (crash_adequacy.wptp_step with "[$Hσ] [$Hg] [Hwpr] [Hwptp] [HNC]") as "H"; eauto.
  { rewrite wpr0_unfold/wpr0_pre. eauto. }
  { rewrite perennial_crashG. iFrame. }
  iMod "H" as (e2 t2' ->) "H".
  iMod "H". iModIntro. simpl. iMod "H". iModIntro. iNext.
  iApply (step_fupdN_wand with "H"). iIntros "H".
  iMod "H" as "(Hσ&Hg&Hwpr&Hwptp&HNC)".
  iFrame. iModIntro.
  iSplitL "HNC".
  { rewrite perennial_crashG. iFrame. }
  iSplit; first done.
  simpl. iExists Φ, Φinv, Φr.
  rewrite wpr0_unfold/wpr0_pre. eauto.
Qed.

Lemma stwpnode_crash ct k eb t1 σ1 g σ2 κ κs ns:
  crash_prim_step CS σ1 σ2 →
  grove_global_state_interp g ns (κ ++ κs) -∗
  stwpnode ct k {| boot := eb; tpool := t1; local_state := σ1 |} -∗
  |={⊤}=> ▷ |={⊤}=>
  grove_global_state_interp g (S ns) κs ∗
  stwpnode ct k {| boot := eb; tpool := [eb]; local_state := σ2 |}.
Proof.
  iIntros (Hstep) "Hg Hnode".
  destruct ct as (Hc&t).
  iDestruct "Hnode" as "((Hσ&HNC)&(%Hequal&Hwptp))".
  destruct Hequal as (Hglobal&Hnum&Hinv).
  destruct t1; first done. simpl.
  rewrite -Hglobal -Hinv.
  iDestruct "Hwptp" as (Φ Φinv Φr) "(Hwpr&Hwptp)".
  iMod (NC_upd_C with "HNC") as "#HC".
  rewrite wpr0_unfold/wpr0_pre.
  iMod (wpc0_crash with "Hwpr") as "H".
  iMod (own_disc_fupd_elim with "H") as "H".
  iSpecialize ("H" with "[HC]").
  { rewrite perennial_crashG. iFrame "#". }
  iMod (fupd_split_level_fupd with "H") as "H".
  iMod ("H" with "[//] [$] [$]") as "H".
  iModIntro. iNext. iClear "HC".
  iMod NC_alloc as (Hc') "HNC".
  rewrite Hinv.
  iSpecialize ("H" with "HNC").
  (* Need to change def of perennialG and wpr0 to ensure that
     (1) iris_invG cannot depend on the Hc instance
     (2) iris_invG instance is the same after the crash.
     Might be easiest to make a perennial_invG field of perennialG that
    iris_invG must be equal to. However, that didn't work so well for global_state_interp *)
Abort.

Lemma stwpnodes_step k dns1 g1 ns dns2 g2 κ κs :
  dist_step (CS := CS) (dns1, g1) κ (dns2, g2) →
  grove_global_state_interp g1 ns (κ ++ κs) -∗
  stwpnodes k dns1 -∗
  |={⊤,∅}=> |={∅}▷=>^(S $ grove_num_laters_per_step ns) |={∅, ⊤}=>
  grove_global_state_interp g2 (S ns) κs ∗
  stwpnodes k dns2.
Proof.
  iIntros (Hstep) "Hg Hnodes".
  inversion Hstep as [ρ1 κs' ρ2 m eb t1 σ1 t2 σ2 Hlookup1 Hlookup2 Hprim |].
  - subst. rewrite /stwpnodes.
    iDestruct (big_sepL_insert_acc with "Hnodes") as "(Hdn&Hnodes)"; first eassumption.
    iDestruct "Hdn" as (ct) "Hdn".
    iDestruct (stwpnode_step with "[$] [$]") as "H"; first eassumption.
    iApply (step_fupdN_inner_wand with "H"); auto.
    iIntros "($&Hnode)".
    simpl in Hlookup2. rewrite Hlookup2.
    iApply "Hnodes". iExists _. eauto.
  -
Abort.

End distributed_adequacy.
