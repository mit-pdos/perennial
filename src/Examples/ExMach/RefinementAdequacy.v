From iris.algebra Require Import auth gmap frac agree.
Require Export CSL.WeakestPre CSL.Lifting CSL.Adequacy.
Require Import Helpers.RelationTheorems.
From iris.algebra Require Export functions.
From iris.base_logic.lib Require Export invariants gen_heap.
From iris.proofmode Require Export tactics.
Require Export ExMach.ExMachAPI ExMach.WeakestPre.
Require Export ExMach.SeqHeap.
Set Default Proof Using "Type".

Class exmachPreG Σ := ExMachPreG {
  exm_preG_iris :> invPreG Σ;
  exm_preG_mem :> seq_heapPreG nat nat Σ;
  exm_preG_disk :> gen_heapPreG nat nat Σ
}.

Definition exmachΣ : gFunctors := #[invΣ; gen_heapΣ nat nat; seq_heapΣ nat nat].
Instance subG_exmachPreG {Σ} : subG exmachΣ Σ → exmachPreG Σ.
Proof. solve_inG. Qed.

Import ExMach.

(* We don't need to actually use this directly, because we're interested in showing refinements,
   but worth proving first because it's a bit simpler and helps check that everything makes sense. *)
Definition exmach_recovery_adequacy {T R} Σ `{exmachPreG Σ} s
           (e: proc ExMach.Op T) (rec: proc _ R) σ φ φrec (φinv : forall {_ : exmachG Σ}, iProp Σ) :
  state_wf σ →
  (∀ `{exmachGenG Σ},
      let H := exmachGen_set 0 in
      (([∗ map] i ↦ v ∈ mem_state σ, i ↦ v @N)
               ={⊤}=∗
               WP e @ s; ⊤ {{ v, ⌜φ v⌝ }}
               ∗ (|={⊤, ∅}=> φinv)
               ∗ □ (∀ Hinv H0 H1 k,
                      let H := @ExMachG Σ Hinv H0 H1 (S k) in
                      (∃ Hinv, @φinv (@ExMachG Σ Hinv _ _ k))
                      ={⊤}=∗ WP rec @ s; ⊤ {{ _, ⌜ φrec ⌝ }}
                         ∗ (|={⊤, ∅}=>
                         let _ := ExMachG Σ _ _ _ (exm_current) in φinv))
      )%I) →
  s = NotStuck →
  @recv_adequate _ _ _ ExMach.l s e rec σ (λ v _, φ v) (λ _, φrec).
Proof.
  intros Hwf Hwp Hnot_stuck.
  eapply (wp_recovery_adequacy _ _) with
   (φinv0 := (fun s => ∃ _ : exmachG Σ, state_interp s ∗ φinv _)%I); auto.
  iIntros (?) "".
  iMod (seq_heap_strong_init
          (fun i => if nat_eq_dec i 0 then mem_state σ else init_zero)) as (? Hpf_eq) "(Hmc&Hm)".
  iMod (gen_heap_init (disk_state σ)) as (?) "Hd".
  iExists (ex_mach_interp O).
  iSplitL "Hmc Hd".
  { simpl. iExists _, _. iFrame. iPureIntro.
    destruct nat_eq_dec; last by congruence.
    destruct Hwf as (Hwf1&Hwf2).
    split_and!; eauto.
    intros k ?.
    destruct nat_eq_dec.
    * lia.
    * intuition.
    * intros i. destruct (Hwf1 i). intuition.
    * intros i. destruct (Hwf2 i). intuition.
  }
  iPoseProof (Hwp (ExMachGenG Σ _ _ _)) as "H".
  iMod ("H" with "[Hm]") as "(Hwp&Hinv&#Hrec)"; iClear "H".
  {
    rewrite -Hpf_eq. iApply mem_init_to_bigOp0; auto.
    destruct Hwf; auto.
  }
  iModIntro.
  iSplitL "Hwp".
  { iApply wp_wand_l; iFrame. iIntros.
    iApply fupd_mask_weaken; first by set_solver+. auto. }
  iSplitL "Hinv".
  { iIntros.  iMod "Hinv". iModIntro. iExists _. iFrame; auto. }
  iAlways. iIntros (invG ?? Hcrash) "Hinv".
  iDestruct "Hinv" as (HexmachG) "(Hstate&Hinv)".
  simpl in *.
  iSpecialize ("Hrec" $! invG (@exm_mem_inG _ HexmachG) (@exm_disk_inG _ HexmachG)
                      ((@exm_current Σ HexmachG)) with "[Hinv]").
  { iExists (exm_invG). destruct HexmachG; auto. }
  iMod "Hrec" as "(Hrec&Hinv)".
  iModIntro.
  iExists ((@ex_mach_interp Σ (@exm_disk_inG Σ HexmachG) (@exm_mem_inG Σ HexmachG)
                            (S (@exm_current Σ HexmachG)))).
  iSplitL "Hstate".
  { (* shows ex_mach_interp is holds after crash for next gen *)
    rewrite /ex_mach_interp.
    iDestruct "Hstate" as (mems disks) "(?&?&%&Hp)".
    iDestruct "Hp" as %(Hdisks&Hcrash'&Hwf1&Hwf2).
    inversion Hcrash; subst.
    iExists mems, _. iFrame.
    iPureIntro. split_and!.
    * eauto.
    * rewrite /crash_fun//=.
    * intros. eapply Hcrash'; eauto. lia.
    * rewrite /crash_fun/=. intros i Hsome.
      apply not_le; intros Hge.
      rewrite init_zero_lookup_ge_None in Hsome; last by lia.
      apply is_Some_None in Hsome; auto.
    * rewrite /crash_fun; auto.
  }
  iSplitL "Hrec".
  {
    (* For some reason @wp_wand_l fails here, not sure why *)
    iPoseProof (@wp_mono with "[Hrec]") as "H"; [| eauto |]; last eauto.
    iIntros. iApply fupd_mask_weaken; auto.
  }
  iIntros.
  iMod "Hinv". iModIntro.
  iExists {| exm_invG := invG;
             exm_mem_inG := HexmachG.(@exm_mem_inG Σ);
             exm_disk_inG := HexmachG.(@exm_disk_inG Σ);
             exm_current := S HexmachG.(@exm_current Σ) |}.
  iFrame.
Qed.