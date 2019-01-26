From iris.algebra Require Import auth gmap frac agree.
Require Export CSL.WeakestPre CSL.Lifting.
Require Import Helpers.RelationTheorems.
From iris.algebra Require Export functions.
From iris.base_logic.lib Require Export invariants gen_heap.
From iris.proofmode Require Export tactics.
Require Export ExMach.ExMachAPI.
Require Export ExMach.SeqHeap.
Set Default Proof Using "Type".


Class exmachG Σ := ExMachG {
                     exm_invG : invG Σ;
                     exm_mem_inG :> seq_heapG nat nat Σ;
                     exm_disk_inG :> seq_heapG nat nat Σ;
                     exm_current : nat;
                   }.

Import ExMach.

Instance exmachG_irisG `{exmachG Σ} : irisG ExMach.Op ExMach.l Σ :=
  {
    iris_invG := exm_invG;
    state_interp :=
      (λ s, ∃ mems disks, @seq_heap_ctx _ _ _ _ _ (exm_mem_inG) mems ∗
                          @seq_heap_ctx _ _ _ _ _ (exm_disk_inG) disks ∗
                            ⌜ mems (exm_current) = mem_state s ∧
                              disks (exm_current) = disk_state s ∧
                              (∀ k, k > exm_current → mems k = mem_state (crash_fun s)) ∧
                              (∀ k, k > exm_current → disks k = disk_state (crash_fun s)) ∧
                              (∀ i, is_Some (mem_state s !! i) → i < size) ∧
                              (∀ i, is_Some (disk_state s !! i) → i < size) ⌝
      )%I
  }.

Section lifting.
Context `{exmachG Σ}.

Definition mem_mapsto_vs k v k' :=
  match Nat.compare k' k with
  | Lt => None
  | Eq => Some v
  | Gt => Some 0
  end.
  
Check mapsto_fun.
Local Notation "l ↦{ q } v @N" :=
  (@mapsto_fun _ _ _ _ _ (exm_mem_inG) l q (mem_mapsto_vs (exm_current) v))
  (at level 20, q at level 50, format "l  ↦{ q } v @N") : bi_scope.
Local Notation "l ↦ v @N " :=
  (@mapsto_fun _ _ _ _ _ (exm_mem_inG) l 1 (mem_mapsto_vs (exm_current) v))
  (at level 20) : bi_scope.

Local Notation "l ↦{ q } v @C" :=
  (@mapsto_fun _ _ _ _ _ (exm_mem_inG) l q (mem_mapsto_vs (S exm_current) v))
  (at level 20, q at level 50, format "l  ↦{ q } v @C") : bi_scope.
Local Notation "l ↦ v @C" :=
  (@mapsto_fun _ _ _ _ _ (exm_mem_inG) l 1 (mem_mapsto_vs (S exm_current) v))
  (at level 20) : bi_scope.

Lemma nat_compare_lt_Lt: ∀ n m : nat, n < m → (n ?= m) = Lt.
Proof. intros. by apply nat_compare_lt. Qed.
Lemma nat_compare_gt_Gt: ∀ n m : nat, n > m → (n ?= m) = Gt.
Proof. intros. by apply nat_compare_gt. Qed.

Lemma wp_write_mem s E i v' v :
  {{{ ▷ i ↦ v' @N }}} write_mem i v @ s; E {{{ RET tt; i ↦ v @N }}}.
Proof.
  iIntros (Φ) ">Hi HΦ". iApply wp_lift_call_step.
  iIntros (σ) "Hown".
  iModIntro. iSplit; first by destruct s.
  iIntros (e2 σ2 Hstep) "!>".
  inversion Hstep; subst.
  iDestruct "Hown" as (mems disks) "(Hown1&Hown2&Hp)".
  iDestruct "Hp" as %(Heq_mem&?&Hcrash_mem&Hcrash_disks&Hsize&?).
  iDestruct (seq_heap_valid with "Hown1 Hi") as %Hin_bound.
  iMod (@seq_heap_update _ _ _ _ _ exm_mem_inG mems i
                         (mem_mapsto_vs (exm_current) v')
                         (mem_mapsto_vs (exm_current) v)
          with "Hown1 Hi") as "(Hown1&Hi)".
  { intros k. rewrite /mem_mapsto_vs.  destruct Nat.compare => //=. clear; firstorder. }
  iModIntro.
  iSplitR "Hi HΦ".
  - iExists _, _. iFrame.
    iPureIntro. split_and!.
    * rewrite /mem_mapsto_vs Nat.compare_refl.
      rewrite /set_mem/set_default//=. rewrite -Heq_mem.
      specialize (Hin_bound exm_current v').
      rewrite Hin_bound //.
      rewrite /mem_mapsto_vs Nat.compare_refl //=.
    * done.
    * intros k Hgt.
      rewrite /mem_mapsto_vs. rewrite nat_compare_gt_Gt /=; last auto.
      rewrite /crash_fun/set_mem. rewrite /= Hcrash_mem; last auto.
      rewrite /crash_fun/set_mem/=.
      apply init_zero_insert_zero. apply Hsize.
      exists v'. rewrite -Heq_mem. apply Hin_bound.
      rewrite /mem_mapsto_vs Nat.compare_refl //=.
    * done.
    * rewrite /set_mem/set_default//= => i'.
      specialize (Hsize i').
      destruct ((mem_state σ) !! i) eqn:Heq; rewrite Heq.
      ** case (decide (i = i')).
         *** intros -> ?. apply Hsize; eauto.
         *** intros ?. rewrite lookup_insert_ne //=.
      ** apply Hsize.
    * eauto.
  - iApply "HΦ". eauto.
Qed.

Lemma wp_read_mem s E i v :
  {{{ ▷ i ↦ v @N }}} read_mem i @ s; E {{{ RET v; i ↦ v @N }}}.
Proof.
  iIntros (Φ) ">Hi HΦ". iApply wp_lift_call_step.
  iIntros (σ) "Hown". 
  iModIntro. iSplit; first by destruct s.
  iIntros (e2 σ2 Hstep) "!>".
  inversion Hstep; subst.
  iDestruct "Hown" as (mems disks) "(Hown1&Hown2&Hp)".
  iDestruct "Hp" as %(Heq_mem&?&Hcrash_mem&Hcrash_disks&Hsize&?).
  iDestruct (seq_heap_valid with "Hown1 Hi") as %Hin_bound.
  iModIntro. iSplitR "Hi HΦ".
  - iExists _, _. iFrame; iPureIntro; split_and!; eauto.
  - rewrite /get_mem/get_default.
    rewrite -Heq_mem.
    rewrite (Hin_bound _ v).
    * by iApply "HΦ".
    * rewrite /mem_mapsto_vs Nat.compare_refl //=.
Qed.

Lemma mem_crash i v : i ↦ v @N -∗ i ↦ 0 @C.
Proof.
  rewrite /
  iIntros.

Lemma cas_non_stuck i v1 v2 σ:
  ¬ Var.l.(step) (CAS i v1 v2) σ Err.
Proof.
  intros Hstuck. destruct Hstuck as [Hread|(v'&?&Hread&Hrest)].
  - inversion Hread.
  - destruct nat_eq_dec; subst; [apply bind_pure_no_err in Hrest|]; inversion Hrest.
Qed.

Lemma wp_cas_fail s E i v1 v2 v3 :
  v1 ≠ v2 →
  {{{ ▷ i ↦ v1 }}} cas i v2 v3 @ s; E {{{ RET v1; i ↦ v1 }}}.
Proof.
  iIntros (Hneq Φ) ">Hi HΦ". iApply wp_lift_call_step.
  iIntros (σ) "Hown". destruct_state σ "Hown".
  iModIntro. iSplit.
  { destruct s; auto using cas_non_stuck. }
  iIntros (e2 σ2 Hstep) "!>".
  inversion Hstep as (v'&σ2'&Hread&Hrest); subst.
  inversion Hread; subst.
  destruct i; iDestruct (reg_agree with "Hi [$]") as "%"; subst;
    iFrame; simpl;
  (destruct (nat_eq_dec); [ by (subst; exfalso; eauto)|];
  inversion Hrest; subst;
  iFrame; by iApply "HΦ").
Qed.

Lemma wp_cas_suc s E i v1 v2 :
  {{{ ▷ i ↦ v1 }}} cas i v1 v2 @ s; E {{{ RET v1; i ↦ v2 }}}.
Proof.
  iIntros (Φ) ">Hi HΦ". iApply wp_lift_call_step.
  iIntros (σ) "Hown". destruct_state σ "Hown".
  iModIntro. iSplit.
  { destruct s; auto using cas_non_stuck. }
  iIntros (e2 σ2 Hstep) "!>".
  inversion Hstep as (v'&σ2'&Hread&Hrest); subst.
  inversion Hread; subst.
  destruct i; iDestruct (reg_agree with "Hi [$]") as "%"; subst;
  (destruct (nat_eq_dec); [| simpl in *; congruence]);
  inversion Hrest as ([]&?&Hputs&Hpure); inversion Hputs; inversion Hpure; subst;
     iMod (reg_update _ v2 with "Hi [$]") as "(Hi&$)"; subst;
    iFrame; simpl;
  inversion Hrest; subst;
  iFrame; by iApply "HΦ".
Qed.

End lifting.

(* Essentially the same as the verification of the spinlock in Iris heap_lang
   except we don't allocate locks or pass the pointer to them; there is a dedicated
   lock register. *)

Class lockG Σ := LockG { lock_tokG :> inG Σ (exclR unitC) }.
Definition lockΣ : gFunctors := #[GFunctor (exclR unitC)].
Instance subG_lockΣ {Σ} : subG lockΣ Σ → lockG Σ.
Proof. solve_inG. Qed.

Section lock.
  Context `{!varG Σ, !lockG Σ}.

  Definition lock_inv (γ : gname) (P : iProp Σ) : iProp Σ :=
    ((Lock ↦ 0 ∗ P ∗ own γ (Excl ())) ∨ (Lock ↦ 1))%I.

  Definition is_lock (N: namespace) (γ: gname) (P: iProp Σ) : iProp Σ :=
    (inv N (lock_inv γ P))%I.

  Definition locked (γ: gname) : iProp Σ :=
    own γ (Excl ()).

  Global Instance is_lock_persistent N γ R : Persistent (is_lock N γ R).
  Proof. apply _. Qed.

  Global Instance locked_timless γ : Timeless (locked γ).
  Proof. apply _. Qed.

  Lemma lock_init N (R: iProp Σ) E : Lock ↦ 0 -∗ R ={E}=∗ ∃ γ, is_lock N γ R.
  Proof.
    iIntros "Hl HR".
    iMod (own_alloc (Excl ())) as (γ) "Hexcl"; first done.
    iMod (inv_alloc N _ (lock_inv γ R) with "[-]").
    { iNext. iLeft; iFrame. }
    iModIntro; iExists _; done.
  Qed.

  Lemma wp_lock N γ (R: iProp Σ):
    {{{ is_lock N γ R }}} lock {{{ RET tt; locked γ ∗ R }}}.
  Proof.
    iIntros (Φ) "#Hlock HΦ". iLöb as "IH".
    wp_loop; wp_bind.
    iInv N as "[HL|>HUL]".
    - iDestruct "HL" as "(>H&?&>?)".
      iApply (wp_cas_suc with "[$]"). iIntros "!> Hl !>"; iFrame.
      rewrite //=. wp_ret. wp_ret.
      iApply "HΦ"; iFrame.
    - iApply (wp_cas_fail with "[$]"); first done. iIntros "!> Hl !>"; iFrame.
      rewrite //=. wp_ret. iApply "IH"; eauto.
  Qed.

  Lemma wp_unlock N γ (R: iProp Σ):
    {{{ is_lock N γ R ∗ locked γ ∗ R }}} unlock {{{ RET tt; True }}}.
  Proof.
    iIntros (Φ) "(#Hlock&Hlocked&HR) HΦ".
    iInv N as "[HL|>HUL]".
    - iDestruct "HL" as "(>H&?&>Htok)".
      iDestruct (own_valid_2 with "Htok Hlocked") as %H => //=.
    - iApply (wp_write with "[$]"); iIntros "!> H !>".
      iSplitR "HΦ"; last by iApply "HΦ".
      iLeft. iFrame.
  Qed.
End lock.