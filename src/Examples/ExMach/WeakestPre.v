From iris.algebra Require Import auth gmap frac agree.
Require Export CSL.WeakestPre CSL.Lifting.
Require Import Helpers.RelationTheorems.
From iris.algebra Require Export functions.
From iris.base_logic.lib Require Export invariants gen_heap.
From iris.proofmode Require Export tactics.
Require Export ExMach.ExMachAPI.
Require Export ExMach.SeqHeap.
Set Default Proof Using "Type".

Class exmachGenG Σ := ExMachGenG {
                     exm_gen_invG : invG Σ;
                     exm_gen_mem_inG :> seq_heapG nat nat Σ;
                     exm_gen_disk_inG :> gen_heapG nat nat Σ;
                   }.

Class exmachG Σ := ExMachG {
                     exm_invG : invG Σ;
                     exm_mem_inG :> seq_heapG nat nat Σ;
                     exm_disk_inG :> gen_heapG nat nat Σ;
                     exm_current : nat;
                   }.

Definition exmachGen_set `{H: exmachGenG Σ} (k: nat) :=
  ExMachG Σ (exm_gen_invG) (exm_gen_mem_inG) (exm_gen_disk_inG)
          k.

Import ExMach.

Definition ex_mach_interp {Σ} {hG: gen_heapG addr nat Σ} {hS: seq_heapG addr nat Σ} curr :=
      (λ s, ∃ mems disks, seq_heap_ctx mems ∗
                          gen_heap_ctx disks ∗
                            ⌜ mems curr = mem_state s ∧
                              disks = disk_state s ∧
                              (∀ k, k > curr → mems k = mem_state (crash_fun s)) ∧
                              (∀ i, is_Some (mem_state s !! i) → i < size) ∧
                              (∀ i, is_Some (disk_state s !! i) → i < size) ⌝
      )%I.

Instance exmachG_irisG `{exmachG Σ} : irisG ExMach.Op ExMach.l Σ :=
  {
    iris_invG := exm_invG;
    state_interp := ex_mach_interp exm_current;
  }.


Definition mem_mapsto_vs k v k' :=
  match Nat.compare k' k with
  | Lt => None
  | Eq => Some v
  | Gt => Some 0
  end.

Global Notation "l ↦{ q } v @N" :=
  (@mapsto_fun _ _ _ _ _ (exm_mem_inG) l q (mem_mapsto_vs (exm_current) v))
  (at level 20, q at level 50, format "l  ↦{ q } v @N") : bi_scope.
Global Notation "l ↦ v @N " :=
  (@mapsto_fun _ _ _ _ _ (exm_mem_inG) l 1 (mem_mapsto_vs (exm_current) v))
  (at level 20) : bi_scope.

Global Notation "l ↦{ q } v @C" :=
  (@mapsto_fun _ _ _ _ _ (exm_mem_inG) l q (mem_mapsto_vs (S exm_current) v))
  (at level 20, q at level 50, format "l  ↦{ q } v @C") : bi_scope.
Global Notation "l ↦ v @C" :=
  (@mapsto_fun _ _ _ _ _ (exm_mem_inG) l 1 (mem_mapsto_vs (S exm_current) v))
  (at level 20) : bi_scope.


Section lifting.
Context `{exmachG Σ}.

Lemma nat_compare_lt_Lt: ∀ n m : nat, n < m → (n ?= m) = Lt.
Proof. intros. by apply nat_compare_lt. Qed.
Lemma nat_compare_gt_Gt: ∀ n m : nat, n > m → (n ?= m) = Gt.
Proof. intros. by apply nat_compare_gt. Qed.

Lemma mem_init_to_bigOp mem:
  own (seq_heap_name (exm_mem_inG))
      (◯ to_seq_heap (λ i : nat, match Nat.compare i exm_current with
                                    | Lt => ε
                                    | Eq => mem
                                    | Gt => (fun _ => 0) <$> mem
                                    end))
      -∗
  [∗ map] i↦v ∈ mem, i ↦ v @N.
Proof.
  induction mem using map_ind.
  - iIntros. rewrite //=.
  - iIntros "Hown".
    rewrite big_opM_insert //.

    iAssert (own (seq_heap_name (exm_mem_inG))
                 (◯ to_seq_heap (λ i : nat, match Nat.compare i exm_current with
                                            | Lt => ε
                                            | Eq => m
                                            | Gt => (fun _ => 0) <$> m
                                            end))
                 ∗
                 (i ↦ x @N))%I
                    with "[Hown]" as "[Hrest $]".
    { rewrite /mem_mapsto_vs mapsto_fun_eq /mapsto_fun_def.
      rewrite -own_op.
      iApply (own_mono with "Hown").
      rewrite -auth_frag_op. apply auth_frag_mono.
      exists ε. rewrite right_id.
      intros k. rewrite ofe_fun_lookup_op. rewrite /to_seq_heap.
      destruct (Nat.compare_spec k (exm_current)).
      * subst. rewrite to_gen_heap_insert.
        rewrite insert_singleton_op; first by rewrite comm.
        by apply lookup_to_gen_heap_None.
      * by rewrite right_id.
      * rewrite fmap_insert to_gen_heap_insert.
        rewrite insert_singleton_op; first by rewrite comm.
        rewrite ?lookup_fmap H0 //=.
    }
    by iApply IHmem.
Qed.

Lemma mem_init_to_bigOp0 mem:
  exm_current = 0 →
  (∀ i, is_Some (mem !! i) ↔ i < size) →
  own (seq_heap_name (exm_mem_inG))
      (◯ to_seq_heap (λ i : nat, if nat_eq_dec i exm_current then mem else init_zero))
      -∗
  [∗ map] i↦v ∈ mem, i ↦ v @N.
Proof.
  intros H0 Hsize.
  iIntros.
  iApply mem_init_to_bigOp.
  iApply own_mono; last eauto.
  apply auth_frag_mono.
  exists ε. rewrite right_id.
  intros k. rewrite H0. rewrite /to_seq_heap.
  destruct (Nat.compare_spec k 0).
  * subst. destruct nat_eq_dec; last by exfalso. done.
  * lia.
  * destruct nat_eq_dec; first by lia.
    rewrite /to_gen_heap => l.
    rewrite well_sized_mem_0_init //.
Qed.

Lemma wp_write_mem s E i v' v :
  {{{ ▷ i ↦ v' @N }}} write_mem i v @ s; E {{{ RET tt; i ↦ v @N }}}.
Proof.
  iIntros (Φ) ">Hi HΦ". iApply wp_lift_call_step.
  iIntros (σ) "Hown".
  iModIntro. iSplit; first by destruct s.
  iIntros (e2 σ2 Hstep) "!>".
  inversion Hstep; subst.
  iDestruct "Hown" as (mems disks) "(Hown1&Hown2&Hp)".
  iDestruct "Hp" as %(Heq_mem&?&Hcrash_mem&Hsize&?).
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
  iDestruct "Hp" as %(Heq_mem&?&Hcrash_mem&Hsize&?).
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
  eapply mapsto_fun_weaken with (k := exm_current).
  intros k. rewrite /mem_mapsto_vs. destruct nat_eq_dec; subst.
  - rewrite nat_compare_lt_Lt; auto.
  - destruct (Nat.compare_spec k (exm_current)).
    * rewrite nat_compare_lt_Lt; try congruence.
    * rewrite nat_compare_lt_Lt; try congruence; lia.
    * destruct (Nat.compare_spec k (S exm_current)); auto.
      lia.
Qed.

Lemma cas_non_stuck i v1 v2 σ:
  ¬ ExMach.l.(step) (CAS i v1 v2) σ Err.
Proof.
  intros Hstuck. destruct Hstuck as [Hread|(v'&?&Hread&Hrest)].
  - inversion Hread.
  - destruct nat_eq_dec; subst; [apply bind_pure_no_err in Hrest|]; inversion Hrest.
Qed.

Lemma wp_cas_fail s E i v1 v2 v3 :
  v1 ≠ v2 →
  {{{ ▷ i ↦ v1 @N }}} cas i v2 v3 @ s; E {{{ RET v1; i ↦ v1 @N }}}.
Proof.
  iIntros (Hneq Φ) ">Hi HΦ". iApply wp_lift_call_step.
  iIntros (σ) "Hown".
  iModIntro. iSplit.
  { destruct s; auto using cas_non_stuck. }
  iIntros (e2 σ2 Hstep) "!>".
  iDestruct "Hown" as (mems disks) "(Hown1&Hown2&Hp)".
  iDestruct "Hp" as %(Heq_mem&?&Hcrash_mem&Hsize&?).
  iDestruct (seq_heap_valid with "Hown1 Hi") as %Hin_bound.
  assert (Hlookup: σ.(mem_state) !! i = Some v1).
  { rewrite -Heq_mem. apply Hin_bound.
    rewrite /mem_mapsto_vs Nat.compare_refl //=. }
  inversion Hstep as (v'&σ2'&Hread&Hrest); subst.
  rewrite /get_mem/get_default/reads Hlookup in Hread.
  inversion Hread; subst.
  destruct nat_eq_dec; first by exfalso.
  inversion Hrest; subst.
  iModIntro. iSplitR "Hi HΦ".
  - iExists _, _. iFrame; iPureIntro; split_and!; eauto.
  - by iApply "HΦ".
Qed.

Lemma wp_cas_suc s E i v1 v2 :
  {{{ ▷ i ↦ v1 @N }}} cas i v1 v2 @ s; E {{{ RET v1; i ↦ v2 @N }}}.
Proof.
  iIntros (Φ) ">Hi HΦ". iApply wp_lift_call_step.
  iIntros (σ) "Hown".
  iModIntro. iSplit.
  { destruct s; auto using cas_non_stuck. }
  iIntros (v2' σ2 Hstep) "!>".
  iDestruct "Hown" as (mems disks) "(Hown1&Hown2&Hp)".
  iDestruct "Hp" as %(Heq_mem&?&Hcrash_mem&Hsize&?).
  iDestruct (seq_heap_valid with "Hown1 Hi") as %Hin_bound.
  assert (Hlookup: σ.(mem_state) !! i = Some v1).
  { rewrite -Heq_mem. apply Hin_bound.
    rewrite /mem_mapsto_vs Nat.compare_refl //=. }
  inversion Hstep as (v'&σ2'&Hread&Hrest); subst.
  inversion Hread; subst.
  rewrite /get_mem/get_default/reads Hlookup in Hread Hrest.
  destruct nat_eq_dec; last by eauto.
  destruct Hrest as ([]&?&Hputs&Hpure).
  inversion Hpure; subst.
  inversion Hputs; inversion Hpure; subst.
  iMod (@seq_heap_update _ _ _ _ _ exm_mem_inG mems i
                         (mem_mapsto_vs (exm_current) _)
                         (mem_mapsto_vs (exm_current) v2)
          with "Hown1 Hi") as "(Hown1&Hi)".
  { intros k. rewrite /mem_mapsto_vs.  destruct Nat.compare => //=. clear; firstorder. }
  iModIntro.
  iSplitR "Hi HΦ".
  - iExists _, _. iFrame.
    iPureIntro. split_and!.
    * rewrite /mem_mapsto_vs Nat.compare_refl.
      rewrite /set_mem/set_default//=. rewrite -Heq_mem.
      specialize (Hin_bound exm_current v2').
      rewrite Hin_bound //.
      rewrite /mem_mapsto_vs Nat.compare_refl //=.
    * done.
    * intros k Hgt.
      rewrite /mem_mapsto_vs. rewrite nat_compare_gt_Gt /=; last auto.
      rewrite /crash_fun/set_mem. rewrite /= Hcrash_mem; last auto.
      rewrite /crash_fun/set_mem/=.
      apply init_zero_insert_zero. apply Hsize.
      exists v2'. rewrite -Heq_mem. apply Hin_bound.
      rewrite /mem_mapsto_vs Nat.compare_refl //=.
    * rewrite /set_mem/set_default//= => i'.
      specialize (Hsize i').
      destruct ((mem_state σ2') !! i) eqn:Heq; rewrite Heq.
      ** case (decide (i = i')).
         *** intros -> ?. apply Hsize; eauto.
         *** intros ?. rewrite lookup_insert_ne //=.
      ** apply Hsize.
    * eauto.
  - iApply "HΦ". eauto.
Qed.

Lemma wp_assert s E b:
  b = true →
  {{{ True }}} assert b @ s; E {{{ RET (); True }}}.
Proof.
  iIntros (Hb Φ) "_ HΦ". rewrite Hb -wp_bind_proc_val.
  iNext. wp_ret. by iApply "HΦ".
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
  Context `{!exmachG Σ, !lockG Σ}.

  Definition lock_inv (γ : gname) (i: addr) (P : iProp Σ) : iProp Σ :=
    ((i ↦ 0 @N ∗ P ∗ own γ (Excl ())) ∨ (i ↦ 1 @N))%I.

  Definition is_lock (N: namespace) (γ: gname) (i: addr) (P: iProp Σ) : iProp Σ :=
    (inv N (lock_inv γ i P))%I.

  Definition locked (γ: gname) : iProp Σ :=
    own γ (Excl ()).

  Global Instance is_lock_persistent N γ i R : Persistent (is_lock N γ i R).
  Proof. apply _. Qed.

  Global Instance locked_timless γ : Timeless (locked γ).
  Proof. apply _. Qed.

  Lemma lock_init N i (R: iProp Σ) E : i ↦ 0 @N -∗ R ={E}=∗ ∃ γ, is_lock N γ i R.
  Proof.
    iIntros "Hl HR".
    iMod (own_alloc (Excl ())) as (γ) "Hexcl"; first done.
    iMod (inv_alloc N _ (lock_inv γ i R) with "[-]").
    { iNext. iLeft; iFrame. }
    iModIntro; iExists _; done.
  Qed.

  Lemma wp_lock N γ i (R: iProp Σ):
    {{{ is_lock N γ i R }}} lock i {{{ RET tt; locked γ ∗ R }}}.
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

  Lemma wp_unlock N γ i (R: iProp Σ):
    {{{ is_lock N γ i R ∗ locked γ ∗ R }}} unlock i {{{ RET tt; True }}}.
  Proof.
    iIntros (Φ) "(#Hlock&Hlocked&HR) HΦ".
    iInv N as "[HL|>HUL]".
    - iDestruct "HL" as "(>H&?&>Htok)".
      iDestruct (own_valid_2 with "Htok Hlocked") as %H => //=.
    - iApply (wp_write_mem with "[$]"); iIntros "!> H !>".
      iSplitR "HΦ"; last by iApply "HΦ".
      iLeft. iFrame.
  Qed.
End lock.