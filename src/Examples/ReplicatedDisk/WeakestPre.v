From iris.algebra Require Import auth gmap frac agree csum excl.
Require Export CSL.WeakestPre CSL.Lifting CSL.Counting CSL.ThreadReg CSL.Leased_Heap.
From iris.algebra Require Export functions csum.
From iris.base_logic.lib Require Export invariants gen_heap.
From iris.proofmode Require Export tactics.
Require Export TwoDiskAPI.
Set Default Proof Using "Type".

Import TwoDisk.

Canonical Structure diskIdC := leibnizO diskId.
Class disk_statusG (Σ: gFunctors) : Set :=
  Disk_statusG { disk_status_inG :> inG Σ (csumR (exclR unitO) (agreeR (diskIdC)));
                 disk_status_name: gname}.
Arguments disk_status_name {_}.

Section disk_status.
  Context `{tr: disk_statusG Σ}.

  Definition is_OnlyDisk (id: diskId) :=
    own (disk_status_name tr) (Cinr (to_agree id)).

  Definition to_status (ds: DisksState) :=
    match ds with
    | OnlyDisk id _ => (Cinr (to_agree id))
    | BothDisks _ _ => (Cinl ((Excl tt)))
    end.

  Definition disk_status_ctx ds :=
    own (disk_status_name tr) (to_status ds).

  Lemma disk_status_agree id ds :
    disk_status_ctx ds -∗ is_OnlyDisk id -∗ ∃ d, ⌜ ds = OnlyDisk id d ⌝.
  Proof.
    iIntros "H1 H2". iDestruct (own_valid_2 with "H1 H2") as %H.
    destruct ds; eauto. rewrite -Cinr_op in H. apply agree_op_inv' in H. inversion H; subst.
    eauto.
  Qed.

  Lemma disk_status_update_both disk0 disk1 ds:
    disk_status_ctx (BothDisks disk0 disk1) ==∗ disk_status_ctx ds.
  Proof.
    iIntros "Hown". iMod (own_update with "Hown") as "$"; eauto.
    { simpl. apply: cmra_update_exclusive. destruct ds; econstructor. }
  Qed.

  Lemma disk_status_update_only id d d':
    disk_status_ctx (OnlyDisk id d) ==∗ disk_status_ctx (OnlyDisk id d').
  Proof.
    iIntros "Hown". trivial.
  Qed.

End disk_status.

Class exmachG Σ := ExMachG {
                     exm_invG : invG Σ;
                     exm_mem_inG :> gen_heapG nat nat Σ;
                     exm_disk0_inG :> leased_heapG nat nat Σ;
                     exm_disk1_inG :> leased_heapG nat nat Σ;
                     exm_status_inG :> disk_statusG Σ;
                     exm_treg_inG :> tregG Σ;
                   }.

Lemma gen_heap_strong_init `{H: gen_heapPreG L V Σ} σs :
  (|==> ∃ (H0 : gen_heapG L V Σ)
          (Hpf: @gen_heap_inG _ _ _ _ _ H0 = gen_heap_preG_inG), gen_heap_ctx σs ∗
    own (gen_heap_name H0) (◯ (to_gen_heap σs)))%I.
Proof.
  iMod (own_alloc (● to_gen_heap σs ⋅ ◯ to_gen_heap σs)) as (γ) "(?&?)".
  { apply auth_both_valid; split; auto. exact: to_gen_heap_valid. }
  iMod (own_alloc (● to_gen_meta ∅)) as (γm) "Hm".
  { rewrite auth_auth_valid. exact: to_gen_meta_valid. }
  iModIntro. iExists (GenHeapG L V Σ _ _ _ _ _ γ γm), eq_refl.
  iFrame. iExists _. iFrame. eauto.
Qed.

Definition disk_state_interp {Σ}
           (hM: gen_heapG addr nat Σ) (hD0 hD1: leased_heapG addr nat Σ) (hStatus: disk_statusG Σ)  :=
  (λ s, ∃ mem disk0 disk1, (gen_heap_ctx mem (hG := hM)) ∗
                     (gen_heap_ctx disk0 (hG := (leased_heap_heapG hD0))) ∗
                     (gen_heap_ctx disk1 (hG := (leased_heap_heapG hD1))) ∗
                      disk_status_ctx (disks_state s) ∗
                        ⌜ mem = mem_state s ∧
                           match disks_state s with
                           | BothDisks disk0' disk1' => disk0 = disk0' ∧ disk1 = disk1'
                           | OnlyDisk d0 disk0' => disk0 = disk0'
                           | OnlyDisk d1 disk1' => disk1 = disk1'
                           end ∧ state_wf s⌝)%I.

Definition ex_mach_interp {Σ} {hM: gen_heapG addr nat Σ} {hD0 hD1: leased_heapG addr nat Σ} hS
           {tr: tregG Σ}  :=
  (λ s, thread_count_interp (fst s) ∗ disk_state_interp hM hD0 hD1 hS (snd s))%I.

Definition ex_mach_interp' `{exmachG Σ} :=
    @ex_mach_interp _ exm_mem_inG exm_disk0_inG exm_disk1_inG  exm_status_inG exm_treg_inG.

Instance exmachG_irisG `{exmachG Σ} : irisG TwoDisk.Op TwoDisk.l Σ :=
  {
    iris_invG := exm_invG;
    state_interp := ex_mach_interp'
  }.

Definition mem_mapsto_vs k v k' :=
  match Nat.compare k' k with
  | Lt => None
  | Eq => Some v
  | Gt => Some 0
  end.

(*
Definition master0 `{exmachG Σ} := (master (hG := exm_disk0_inG)).
Definition master1 `{exmachG Σ} := (master (hG := exm_disk1_inG)).
*)

Global Notation "l m↦{ q } v " := (mapsto (hG := exm_mem_inG) l q v)
  (at level 20, q at level 50, format "l  m↦{ q } v") : bi_scope.
Global Notation "l m↦ v " :=
  (mapsto (hG := exm_mem_inG) l 1 v)
  (at level 20) : bi_scope.

Global Notation "l d0◯↦ v " :=
  (mapsto (hG := leased_heap_heapG exm_disk0_inG) l 1 v)
  (at level 20) : bi_scope.

Global Notation "l d0↦ v " :=
  (mapsto (hG := leased_heap_heapG exm_disk0_inG) l 1 v ∗
   master (hG := exm_disk0_inG) l v)%I
  (at level 20) : bi_scope.

Global Notation "l d1◯↦ v " :=
  (mapsto (hG := leased_heap_heapG exm_disk1_inG) l 1 v)
  (at level 20) : bi_scope.

Global Notation "l d1↦ v " :=
  (mapsto (hG := leased_heap_heapG exm_disk1_inG) l 1 v ∗
   master (hG := exm_disk1_inG) l v)%I
  (at level 20) : bi_scope.

Definition lease0 `{exmachG Σ} := (lease (hG := exm_disk0_inG)).
Definition lease1 `{exmachG Σ} := (lease (hG := exm_disk1_inG)).

(*
Global Notation "l d0↦{ q } v " := (mapsto (hG := exm_disk0_inG) l q v)
  (at level 20, q at level 50, format "l  d0↦{ q } v") : bi_scope.
Global Notation "l d0↦ v " :=
  (mapsto (hG := exm_disk0_inG) l 1 v)
  (at level 20) : bi_scope.
Global Notation "l d1↦{ q } v " := (mapsto (hG := exm_disk1_inG) l q v)
  (at level 20, q at level 50, format "l  d1↦{ q } v") : bi_scope.
Global Notation "l d1↦ v " :=
  (mapsto (hG := exm_disk1_inG) l 1 v)
  (at level 20) : bi_scope.
*)

Section lifting.
Context `{exmachG Σ}.

Lemma nat_compare_lt_Lt: ∀ n m : nat, n < m → (n ?= m) = Lt.
Proof. intros. by apply nat_compare_lt. Qed.
Lemma nat_compare_gt_Gt: ∀ n m : nat, n > m → (n ?= m) = Gt.
Proof. intros. by apply nat_compare_gt. Qed.

Lemma mem_init_to_bigOp Hpf Hn mem:
  Hpf = (@gen_heap_inG _ _ _ _ _ exm_mem_inG) →
  Hn = (gen_heap_name (exm_mem_inG)) →
  own (i := Hpf)
      Hn
      (◯ to_gen_heap mem)
      -∗
  [∗ map] i↦v ∈ mem, i m↦ v .
Proof.
  intros Heq_pf Heq_name.
  induction mem using map_ind.
  - iIntros. rewrite //=.
  - iIntros "Hown".
    rewrite big_opM_insert //.
    iAssert (own (i := Hpf) (gen_heap_name (exm_mem_inG))
                 (◯ to_gen_heap m) ∗
                 (i m↦ x))%I
                    with "[Hown]" as "[Hrest $]".
    {
      rewrite mapsto_eq /mapsto_def // Heq_pf Heq_name.
      rewrite to_gen_heap_insert insert_singleton_op; last by apply lookup_to_gen_heap_None.
      rewrite auth_frag_op. iDestruct "Hown" as "(?&?)". iFrame.
    }
    rewrite -Heq_name.
    by iApply IHmem.
Qed.


(*
Lemma disk0_init_to_bigOp disk:
  own (i := @gen_heap_inG _ _ _ _ _ exm_disk0_inG)
      (gen_heap_name (exm_disk0_inG))
      (◯ to_gen_heap disk)
      -∗
  [∗ map] i↦v ∈ disk, i d0↦ v .
Proof.
  induction disk using map_ind.
  - iIntros. rewrite //=.
  - iIntros "Hown".
    rewrite big_opM_insert //.

    iAssert (own (i := @gen_heap_inG _ _ _ _ _ exm_disk0_inG) (gen_heap_name (exm_disk0_inG))
                 (◯ to_gen_heap m) ∗
                 (i d0↦ x))%I
                    with "[Hown]" as "[Hrest $]".
    {
      rewrite mapsto_eq /mapsto_def //.
      rewrite to_gen_heap_insert insert_singleton_op; last by apply lookup_to_gen_heap_None.
      rewrite auth_frag_op. iDestruct "Hown" as "(?&?)". iFrame.
    }
    by iApply IHdisk.
Qed.

Lemma disk1_init_to_bigOp disk:
  own (i := @gen_heap_inG _ _ _ _ _ exm_disk1_inG)
      (gen_heap_name (exm_disk1_inG))
      (◯ to_gen_heap disk)
      -∗
  [∗ map] i↦v ∈ disk, i d1↦ v .
Proof.
  induction disk using map_ind.
  - iIntros. rewrite //=.
  - iIntros "Hown".
    rewrite big_opM_insert //.

    iAssert (own (i := @gen_heap_inG _ _ _ _ _ exm_disk1_inG) (gen_heap_name (exm_disk1_inG))
                 (◯ to_gen_heap m) ∗
                 (i d1↦ x))%I
                    with "[Hown]" as "[Hrest $]".
    {
      rewrite mapsto_eq /mapsto_def //.
      rewrite to_gen_heap_insert insert_singleton_op; last by apply lookup_to_gen_heap_None.
      rewrite auth_frag_op. iDestruct "Hown" as "(?&?)". iFrame.
    }
    by iApply IHdisk.
Qed.
*)

Import Reg_wp.
Lemma thread_reg1:
  ∀ n σ, state_interp (n, σ)
         -∗ thread_count_interp n
            ∗ disk_state_interp (exm_mem_inG) (exm_disk0_inG) (exm_disk1_inG) (exm_status_inG) σ.
Proof. eauto. Qed.
Lemma thread_reg2:
  ∀ n σ, thread_count_interp n
         ∗ disk_state_interp (exm_mem_inG) (exm_disk0_inG) (exm_disk1_inG) (exm_status_inG) σ
         -∗ state_interp (n, σ).
Proof. auto. Qed.

Lemma wp_spawn {T} s E (e: proc _ T) Φ :
  ▷ Registered
    -∗ ▷ (Registered -∗ WP (let! _ <- e; Unregister)%proc @ s; ⊤ {{ _, True }})
    -∗ ▷ ( Registered -∗ Φ tt)
    -∗ WP Spawn e @ s; E {{ Φ }}.
Proof. eapply wp_spawn; eauto using thread_reg1, thread_reg2. Qed.

Lemma wp_unregister s E :
  {{{ ▷ Registered }}} Unregister @ s; E {{{ RET tt; True }}}.
Proof. eapply wp_unregister; eauto using thread_reg1, thread_reg2. Qed.

Lemma wp_wait s E :
  {{{ ▷ Registered }}} Wait @ s; E {{{ RET tt; AllDone }}}.
Proof. eapply wp_wait; eauto using thread_reg1, thread_reg2. Qed.

Lemma wp_write_mem s E i v' v :
  {{{ ▷ i m↦ v' }}} write_mem i v @ s; E {{{ RET tt; i m↦ v }}}.
Proof.
  iIntros (Φ) ">Hi HΦ". iApply wp_lift_call_step.
  iIntros ((n, σ)) "Hown".
  iModIntro. iSplit; first by destruct s.
  iIntros (e2 (n', σ2) Hstep) "!>".
  inversion Hstep; subst.
  inversion H0. subst.
  inversion Hstep; subst.
  iDestruct "Hown" as "(?&Hown)".
  rewrite /disk_state_interp.
  iDestruct "Hown" as (mems disk0 disk1) "(Hown1&Hownd0&Hownd1&?&Hp)".
  iDestruct "Hp" as %(Heq_mem&?&Hsize&?).
  iDestruct (gen_heap_valid with "Hown1 Hi") as %Hin_bound.
  iMod (@gen_heap_update with "Hown1 Hi") as "[Hown1 Hi]".
  iModIntro. iSplitR "Hi HΦ".
  - iFrame. iExists _, disk0, disk1. iFrame.
    iPureIntro. split_and!.
    * rewrite /upd_mem/upd_default -Heq_mem Hin_bound //.
    * simpl in *. destruct (σ.(disks_state)); eauto.
    * split; intuition; eauto.
      rewrite /upd_mem/upd_default//= => i'.
      specialize (Hsize i').
      destruct ((mem_state σ) !! i) eqn:Heq; rewrite Heq.
      ** case (decide (i = i')).
         *** intros ->. simpl in *. rewrite -Hsize lookup_insert. split; eauto.
         *** intros ?. rewrite lookup_insert_ne //=.
      ** apply Hsize.
  - iApply "HΦ". eauto.
Qed.

Lemma wp_read_mem s E i v :
  {{{ ▷ i m↦ v }}} read_mem i @ s; E {{{ RET v; i m↦ v }}}.
Proof.
  iIntros (Φ) ">Hi HΦ". iApply wp_lift_call_step.
  iIntros ((n, σ)) "Hown".
  iModIntro. iSplit; first by destruct s.
  iIntros (e2 (n', σ2) Hstep) "!>".
  inversion Hstep; subst.
  inversion H0. subst.
  inversion Hstep; subst.
  inversion Hstep; subst.
  iDestruct "Hown" as "(?&Hown)".
  iDestruct "Hown" as (mems disk0 disk1) "(Hown1&Hown2&?&?&Hp)".
  iDestruct "Hp" as %(Heq_mem&?&Hsize&?).
  iDestruct (gen_heap_valid with "Hown1 Hi") as %Hin_bound.
  iModIntro. iSplitR "Hi HΦ".
  - iFrame. iExists _, disk0, disk1. iFrame; iPureIntro; split_and!; eauto.
    rewrite /state_wf. split_and; intuition; eauto.
  - rewrite /lookup_mem/lookup_default -Heq_mem Hin_bound.
    by iApply "HΦ".
Qed.

Lemma cas_non_stuck i v1 v2 σ:
  ¬ TwoDisk.l.(step) (CAS i v1 v2) σ Err.
Proof.
  intros Hstuck. destruct Hstuck as [Hread|(v'&?&Hread&Hrest)].
  - inversion Hread.
  - destruct nat_eq_dec; subst; [apply bind_pure_no_err in Hrest|]; inversion Hrest.
Qed.

Lemma wp_cas_fail s E i v1 v2 v3 :
  v1 ≠ v2 →
  {{{ ▷ i m↦ v1 }}} cas i v2 v3 @ s; E {{{ RET v1; i m↦ v1 }}}.
Proof.
  iIntros (Hneq Φ) ">Hi HΦ". iApply wp_lift_call_step.
  iIntros ((n, σ)) "Hown".
  iModIntro. iSplit.
  { destruct s; auto. iPureIntro. eapply snd_lift_non_err, cas_non_stuck. }
  iIntros (e2 (n2, σ2) Hstep) "!>".
  iDestruct "Hown" as "(?&Hown)".
  iDestruct "Hown" as (mems disk0 disk1) "(Hown1&Hown2&?&?&Hp)".
  iDestruct "Hp" as %(Heq_mem&?&Hsize&?).
  iDestruct (gen_heap_valid with "Hown1 Hi") as %Hin_bound.
  assert (Hlookup: σ.(mem_state) !! i = Some v1).
  { rewrite -Heq_mem. apply Hin_bound. }
  inversion Hstep; subst.
  inversion H2 as (v'&σ2'&Hread&Hrest); subst.
  rewrite /lookup_mem/lookup_default/reads Hlookup in Hread.
  inversion Hread; subst.
  destruct nat_eq_dec; first by exfalso.
  inversion Hrest; subst.
  iModIntro. iSplitR "Hi HΦ".
  - iFrame. iExists _, disk0, disk1. iFrame; iPureIntro; split_and!; eauto.
    split_and!; intuition eauto.
  - by iApply "HΦ".
Qed.

Lemma wp_cas_suc s E i v1 v2 :
  {{{ ▷ i m↦ v1 }}} cas i v1 v2 @ s; E {{{ RET v1; i m↦ v2 }}}.
Proof.
  iIntros (Φ) ">Hi HΦ". iApply wp_lift_call_step.
  iIntros ((n, σ)) "Hown".
  iModIntro. iSplit.
  { destruct s; auto using snd_lift_non_err, cas_non_stuck. }
  iIntros (v2' (n2, σ2) Hstep) "!>".
  iDestruct "Hown" as "(?&Hown)".
  iDestruct "Hown" as (mems disk0 disk1) "(Hown1&Hown2&?&?&Hp)".
  iDestruct "Hp" as %(Heq_mem&?&Hsize&?).
  iDestruct (gen_heap_valid with "Hown1 Hi") as %Hin_bound.
  assert (Hlookup: σ.(mem_state) !! i = Some v1).
  { rewrite -Heq_mem. apply Hin_bound. }
  inversion Hstep; subst.
  inversion H2 as (v'&σ2'&Hread&Hrest); subst.
  inversion Hread; subst.
  rewrite /lookup_mem/lookup_default/reads Hlookup in Hread Hrest.
  destruct nat_eq_dec; last by eauto.
  destruct Hrest as ([]&?&Hputs&Hpure).
  inversion Hpure; subst.
  inversion Hputs; inversion Hpure; subst.
  iMod (@gen_heap_update with "Hown1 Hi") as "(Hown1&Hi)".
  iModIntro.
  iSplitR "Hi HΦ".
  - iFrame. iExists _, disk0, disk1. iFrame.
    iPureIntro. split_and!.
    * rewrite /upd_mem/upd_default//= Hin_bound //.
    * done.
    * split; intuition; eauto.
      rewrite /upd_mem/upd_default//= => i'.
      specialize (Hsize i').
      destruct ((mem_state σ2') !! i) eqn:Heq; rewrite Heq.
      ** case (decide (i = i')).
         *** intros ->. simpl in *. rewrite -Hsize lookup_insert. split; eauto.
         *** intros ?. rewrite lookup_insert_ne //=.
      ** apply Hsize.
  - iApply "HΦ". eauto.
Qed.

Lemma wf_range_pres_update (m: gmap addr nat) i v:
  wf_range m → wf_range (upd_default i v m).
Proof.
  intros Hwf i'. rewrite -Hwf.
  rewrite /upd_default.
  destruct (decide (i = i')).
  - subst. destruct (m !! i') as [?|] eqn:Heq; rewrite Heq.
    * rewrite lookup_insert //=. split; eauto.
    * rewrite -Heq. eauto.
  - destruct (m !! i) as [?|] eqn:Heq; rewrite ?Heq.
    * rewrite lookup_insert_ne //=.
    * eauto.
Qed.

Hint Resolve wf_range_pres_update : twodb.

Lemma wf_disk0_update id0 i v x:
  wf_disk (disk0 x) →
  wf_disk (disk0 (upd_disk id0 i v x)).
Proof.
  destruct x as (?&ds).
  destruct ds; try destruct id0; try destruct id; auto => //=; eauto with twodb.
Qed.

Lemma wf_disk1_update id0 i v x:
  wf_disk (disk1 x) →
  wf_disk (disk1 (upd_disk id0 i v x)).
Proof.
  destruct x as (?&ds).
  destruct ds; try destruct id0; try destruct id; auto => //=; eauto with twodb.
Qed.

Lemma wf_disk0_fail id0 x:
  wf_disk (disk0 x) →
  wf_disk (disk0 (maybe_fail_disk id0 x)).
Proof.
  destruct x as (?&ds).
  destruct ds; try destruct id0; try destruct id; auto => //=; eauto with twodb.
Qed.

Lemma wf_disk1_fail id0 x:
  wf_disk (disk1 x) →
  wf_disk (disk1 (maybe_fail_disk id0 x)).
Proof.
  destruct x as (?&ds).
  destruct ds; try destruct id0; try destruct id; auto => //=; eauto with twodb.
Qed.

Lemma disk_fail_only_one σ σ' id d u:
  disks_state σ = OnlyDisk id d →
  disk_fail σ (Val σ' u) →
  σ = σ'.
Proof.
  intros Hds.
  inversion 1; inversion H1; subst; eauto.
  - inversion H2. subst.
  destruct σ. destruct disks_state0. subst.
  simpl in *. congruence.
  simpl in *. inversion Hds. subst. simpl.
  destruct id; simpl; rewrite //=.
  - inversion H2. subst.
  destruct σ. destruct disks_state0. subst.
  simpl in *. congruence.
  simpl in *. inversion Hds. subst. simpl.
  destruct id; simpl; rewrite //=.
Qed.

Lemma disk_fail_non_err σ:
  ¬ disk_fail σ Err.
Proof.
  inversion 1 as [Hp|Hor]. inversion Hp.
  inversion Hor as [Hp|Hp]; inversion Hp.
Qed.

Hint Resolve wf_disk0_fail wf_disk1_fail wf_disk0_update wf_disk1_update disk_fail_non_err : twodb.

Ltac inv_step :=
  repeat (match goal with
         | [ H : unit |- _ ] => destruct H
         | [ H : and_then _ _ _ Err  |- _ ] =>
           let Hhd_err := fresh "Hhd_err" in
           let Hhd := fresh "Hhd" in
           let Htl_err := fresh "Htl_err" in
           inversion H as [Hhd_err|(?&?&Hhd&Htl_err)]; clear H
         | [ H : such_that _ _ _ |- _ ] => inversion H; subst; clear H
         | [ H : pure _ _ _ |- _ ] => inversion H; subst; clear H
         | [ H: puts _ _ _ |- _ ] => inversion H; subst; clear H
         | [ H: reads _ _ _ |- _ ] => inversion H; subst; clear H
         | [ H : Some _ = Some _ |- _] => apply Some_inj in H; subst
         | [ H : Cinl _ = Cinl _ |- _] => inversion H; clear H; subst
         | [ H : (?a, ?b) = (?c, ?d) |- _] => apply pair_inj in H as (?&?); subst
         | [ H : disk_fail _ Err |- _] => exfalso; eapply disk_fail_non_err; eauto
         | [ H: l.(Layer.sem).(Proc.step) ?op _ (Val _ _) |- _] =>
           let Hhd := fresh "Hhd" in
           let Htl := fresh "Htl" in
           destruct H as (?&?&Hhd&Htl)
         | [ H: l.(Layer.sem).(Proc.step) ?op _ (Val _ _) |- _] =>
           inversion H; subst
         end; auto with twodb).

    Ltac inv_case :=
      match goal with
      | [ H : rel_or _ _ _ _ |- _ ] =>
        let Hcase := fresh "Hcase" in
        inversion H as [Hcase|Hcase]
      end.

Lemma disk_status_ctx_upd id0 i v x:
  disk_status_ctx (disks_state (upd_disk id0 i v x)) =
  disk_status_ctx (disks_state x).
Proof.
  rewrite /disk_status_ctx/to_status.
  destruct x as (?&[]); destruct id0; try destruct id; rewrite //=.
Qed.

Definition status_token (ds: DisksState) : iProp Σ :=
  match ds with
    | BothDisks _ _ => True%I
    | OnlyDisk id _ => is_OnlyDisk id
  end.

Lemma disk_status_update σ σ' u:
  disk_fail σ (Val σ' u) →
  disk_status_ctx σ.(disks_state) ==∗
  (disk_status_ctx σ'.(disks_state) ∗ status_token σ'.(disks_state)).
Proof.
  intros Hfail.
  destruct σ as (?&[]).
  * inversion Hfail; inv_step; try inv_case; inv_step; eauto => //=;
    iIntros "H"; eauto; iMod (disk_status_update_both with "[$]") as "H"; eauto.
  * eapply disk_fail_only_one in Hfail; subst; eauto.
Qed.


Lemma wp_write_disk0' s E i v' v :
  {{{ ▷ i d0◯↦ v' }}} write_disk d0 i v @ s; E {{{ RET tt; i d0◯↦ v }}}.
Proof.
  iIntros (Φ) ">Hi HΦ". iApply wp_lift_call_step.
  iIntros ((n, σ)) "Hown".
  iModIntro.
  iSplit.
  { destruct s; auto. iPureIntro. apply snd_lift_non_err.
    inversion 1; inv_step. repeat deex. inv_step.
  }
  iIntros (e2 (n2, σ2) Hstep) "!>".
  inversion Hstep; subst.
  inv_step.
  iDestruct "Hown" as "(?&Hown)".
  iDestruct "Hown" as (mems disk0 disk1) "(Hmem&Hown0&Hown1&Hstatus&Hp)".
  iDestruct "Hp" as %(Heq_mem&Heq_disk&?&Hsize).
  iDestruct (gen_heap_valid with "Hown0 Hi") as %Hin_bound.
  iMod (@gen_heap_update with "Hown0 Hi") as "[Hown0 Hi]".
  iSplitR "Hi HΦ".
  {
  simpl in Heq_disk. destruct (σ.(disks_state)) as [?|?] eqn:Heq_state.
  - simpl. rewrite Heq_state. iMod (disk_status_update_both with "Hstatus") as "$".
    iFrame. iExists _, (<[i := v]>disk0), disk1. iFrame.
    iFrame. simpl. intuition; eauto. subst.
    inversion Hhd.
    { iPureIntro.
      split_and!; eauto; inv_step .
      rewrite Heq_state => //=.
      destruct x0 => //=.
      simpl in *. subst. simpl; intuition; eauto.
      rewrite /upd_default.
      * rewrite /upd_disk/upd_default Hin_bound //.
      * split_and!; intuition eauto with twodb.
    }
    inv_case; inv_step.
    { iPureIntro.
      split_and!; eauto.
      subst; rewrite /maybe_fail_disk Heq_state => //=.
      split_and!; intuition eauto with twodb.
    }
    { iPureIntro.
      split_and!; eauto.
      subst; rewrite /maybe_fail_disk Heq_state => //=.
      * rewrite /upd_disk/upd_default Hin_bound //.
      * split_and!; intuition eauto with twodb.
    }
  - destruct id.
    * subst.
      rewrite Heq_state. simpl. iFrame. simpl. rewrite /disk_state_interp.
      iFrame. iExists _, (<[i := v]>d), disk1. iFrame.
      iFrame. eapply disk_fail_only_one in Hhd; eauto. subst.
      inv_step.
      rewrite disk_status_ctx_upd Heq_state. iFrame.
      iPureIntro.
      split_and!; eauto.
      ** rewrite /upd_disk/upd_default Heq_state => //=.
         destruct x0 => //=.
         simpl in *. subst. simpl; intuition; eauto.
         rewrite Hin_bound //.
      ** split_and!; intuition eauto with twodb.
    * subst.
      rewrite Heq_state. simpl. iFrame. simpl. rewrite /disk_state_interp.
      iFrame. iExists _, (<[i := v]>disk0), d. iFrame.
      iFrame. eapply disk_fail_only_one in Hhd; eauto. subst.
      inv_step.
      rewrite disk_status_ctx_upd Heq_state. iFrame.
      iPureIntro.
      split_and!; eauto.
      ** rewrite /upd_disk/upd_default Heq_state => //=.
         destruct x0 => //=.
         simpl in *. subst. simpl; intuition; eauto.
      ** split_and!; intuition eauto with twodb.
  }
  by iApply "HΦ".
Qed.

Lemma wp_write_disk0 s E i v' v v0 :
  {{{ ▷ i d0↦ v' ∗ ▷ lease0 i v0 }}} write_disk d0 i v @ s; E {{{ RET tt; i d0↦ v ∗ lease0 i v }}}.
Proof.
  iIntros (Φ) "(>(Hi&Hmaster)&>Hlease) HΦ".
  rewrite /lease0.
  iMod (master_lease_update (hG := exm_disk0_inG) i v' v0 v with "[$] [$]") as "(?&?)".
  iApply (wp_write_disk0' with "[$]").
  iNext. iIntros. iApply "HΦ"; iFrame.
Qed.

Lemma wp_read_disk0' s E i v :
  {{{ ▷ i d0◯↦ v }}}
    read_disk d0 i @ s; E
  {{{ mv, RET mv;
      i d0◯↦ v ∗ match mv with
                | None => is_OnlyDisk d1
                | Some v' => ⌜ v = v' ⌝
                end }}}.
Proof.
  iIntros (Φ) ">Hi HΦ". iApply wp_lift_call_step.
  iIntros ((n, σ)) "Hown".
  iModIntro. iSplit.
  { destruct s; auto. iPureIntro. apply snd_lift_non_err.
    inversion 1; inv_step. repeat deex. inv_step.
  }
  iIntros (e2 (n2, σ2) Hstep) "!>".
  inversion Hstep; subst.
  inv_step.
  iDestruct "Hown" as "(?&Hown)".
  iDestruct "Hown" as (mems disk0 disk1) "(Hown_mem&Hown0&Hown1&Hstatus&Hp)".
  iDestruct "Hp" as %(Heq_mem&Heq_disk&Hsize&?).
  iDestruct (gen_heap_valid with "Hown0 Hi") as %Hin_bound.
  simpl in Heq_disk.
  iMod (disk_status_update with "Hstatus") as "($&Htok)"; first eauto.
  destruct (σ.(disks_state)) as [?|?] eqn:Heq_state.
  - simpl. iFrame. iSplitR "Hi HΦ Htok".
    * iExists _, disk0, disk1. iFrame.
      iFrame. simpl. intuition; eauto. subst.
      inversion Hhd.
      { iPureIntro.
        split_and!; eauto; inv_step .
        rewrite Heq_state => //=.
        split_and!; intuition eauto with twodb.
      }
      inv_case; inv_step.
      { iPureIntro.
        split_and!; eauto.
        subst; rewrite /maybe_fail_disk Heq_state => //=.
        split_and!; intuition eauto with twodb.
      }
      { iPureIntro.
        split_and!; eauto.
        subst; rewrite /maybe_fail_disk Heq_state => //=.
        split_and!; intuition eauto with twodb.
      }
    * inversion Hhd.
      {
        rewrite /lookup_disk/get_disk/TwoDisk.disk0. inv_step. rewrite Heq_state.
        rewrite /lookup_default. intuition. subst. rewrite Hin_bound.
        iApply "HΦ"; eauto.
      }
      inv_case; inv_step.
      {
        rewrite /lookup_disk/get_disk/maybe_fail_disk Heq_state //=.
        iApply "HΦ"; eauto.
      }
      {
        rewrite /lookup_disk/get_disk/maybe_fail_disk Heq_state //=.
        rewrite /lookup_default. intuition. subst. rewrite Hin_bound.
        iApply "HΦ"; eauto.
      }
  - eapply disk_fail_only_one in Hhd; eauto. subst.
    simpl. iFrame. iSplitR "Hi HΦ Htok".
    * iExists _, disk0, disk1. iFrame.
      iFrame. simpl. intuition; eauto. subst.
      iPureIntro.
      split_and!; eauto.
      subst; rewrite /maybe_fail_disk Heq_state => //=.
      split_and!; intuition eauto with twodb.
    * rewrite /lookup_disk/get_disk/TwoDisk.disk0/TwoDisk.disk1 ?Heq_state //=.
      destruct id; rewrite /lookup_default; intuition; subst; rewrite ?Hin_bound;
      iApply "HΦ"; eauto.
Qed.

Lemma wp_read_disk0_only0' s E i v :
  {{{ ▷ i d0◯↦ v ∗ ▷ is_OnlyDisk d0 }}}
    read_disk d0 i @ s; E
  {{{ RET (Some v); i d0◯↦ v }}}.
Proof.
  iIntros (Φ) "(>Hi&>His_only) HΦ". iApply wp_lift_call_step.
  iIntros ((n, σ)) "Hown".
  iModIntro. iSplit.
  { destruct s; auto. iPureIntro. apply snd_lift_non_err.
    inversion 1; inv_step. repeat deex. inv_step.
  }
  iIntros (e2 (n2, σ2) Hstep) "!>".
  inversion Hstep; subst.
  inv_step.
  iDestruct "Hown" as "(?&Hown)".
  iDestruct "Hown" as (mems disk0 disk1) "(Hown_mem&Hown0&Hown1&Hstatus&Hp)".
  iDestruct "Hp" as %(Heq_mem&Heq_disk&Hsize&?).
  iDestruct (gen_heap_valid with "Hown0 Hi") as %Hin_bound.
  iDestruct (disk_status_agree with "[$] [$]") as %Hstatus.
  destruct Hstatus as (disk0'&Heq). simpl in *.
  rewrite Heq in Heq_disk. subst.
  eapply disk_fail_only_one in Hhd; eauto. subst.
  iFrame. iSplitR "Hi HΦ".
    * iExists _, disk0', disk1. iFrame.
      iPureIntro.
      split_and!; eauto; inv_step.
      rewrite Heq => //=.
      split_and!; intuition eauto with twodb.
    * rewrite /lookup_disk/get_disk/TwoDisk.disk0. inv_step. rewrite Heq.
      rewrite /lookup_default. intuition. subst. rewrite Hin_bound.
      iApply "HΦ"; eauto.
Qed.

Lemma wp_read_disk0 s E i v :
  {{{ ▷ i d0↦ v }}}
    read_disk d0 i @ s; E
  {{{ mv, RET mv;
      i d0↦ v ∗ match mv with
                | None => is_OnlyDisk d1
                | Some v' => ⌜ v = v' ⌝
                end }}}.
Proof.
  iIntros (Φ) ">(Hi&?) HΦ".
  iApply (wp_read_disk0' with "[$]").
  iNext. iIntros (?) "(?&?)". iApply "HΦ"; iFrame.
Qed.

Lemma wp_read_disk0_only0 s E i v :
  {{{ ▷ i d0↦ v ∗ ▷ is_OnlyDisk d0 }}}
    read_disk d0 i @ s; E
  {{{ RET (Some v); i d0↦ v }}}.
Proof.
  iIntros (Φ) "(>(Hi&?)&?) HΦ".
  iApply (wp_read_disk0_only0' with "[$]").
  iNext. iIntros "?". iApply "HΦ"; iFrame.
Qed.

Lemma wp_write_disk1' s E i v' v :
  {{{ ▷ i d1◯↦ v' }}} write_disk d1 i v @ s; E {{{ RET tt; i d1◯↦ v }}}.
Proof.
  iIntros (Φ) ">Hi HΦ". iApply wp_lift_call_step.
  iIntros ((n, σ)) "Hown".
  iModIntro.
  iSplit.
  { destruct s; auto. iPureIntro. apply snd_lift_non_err.
    inversion 1; inv_step. repeat deex. inv_step.
  }
  iIntros (e2 (n2, σ2) Hstep) "!>".
  inversion Hstep; subst.
  inv_step.
  iDestruct "Hown" as "(?&Hown)".
  iDestruct "Hown" as (mems disk0 disk1) "(Hmem&Hown0&Hown1&Hstatus&Hp)".
  iDestruct "Hp" as %(Heq_mem&Heq_disk&?&Hsize).
  iDestruct (gen_heap_valid with "Hown1 Hi") as %Hin_bound.
  iMod (@gen_heap_update with "Hown1 Hi") as "[Hown1 Hi]".
  iSplitR "Hi HΦ".
  {
  simpl in Heq_disk. destruct (σ.(disks_state)) as [?|?] eqn:Heq_state.
  - simpl. rewrite Heq_state. iMod (disk_status_update_both with "Hstatus") as "$".
    iFrame. iExists _, disk0, (<[i := v]>disk1). iFrame.
    iFrame. simpl. intuition; eauto. subst.
    inversion Hhd.
    { iPureIntro.
      split_and!; eauto; inv_step .
      rewrite Heq_state => //=.
      destruct x0 => //=.
      simpl in *. subst. simpl; intuition; eauto.
      rewrite /upd_default.
      * rewrite /upd_disk/upd_default Hin_bound //.
      * split_and!; intuition eauto with twodb.
    }
    inv_case; inv_step.
    { iPureIntro.
      split_and!; eauto.
      subst; rewrite /maybe_fail_disk Heq_state => //=.
      * rewrite /upd_disk/upd_default Hin_bound //.
      * split_and!; intuition eauto with twodb.
    }
    { iPureIntro.
      split_and!; eauto.
      subst; rewrite /maybe_fail_disk Heq_state => //=.
      split_and!; intuition eauto with twodb.
    }
  - destruct id.
    * subst.
      rewrite Heq_state. simpl. iFrame. simpl. rewrite /disk_state_interp.
      iFrame. iExists _, d, (<[i := v]>disk1). iFrame.
      iFrame. eapply disk_fail_only_one in Hhd; eauto. subst.
      inv_step.
      rewrite disk_status_ctx_upd Heq_state. iFrame.
      iPureIntro.
      split_and!; eauto.
      ** rewrite /upd_disk/upd_default Heq_state => //=.
         destruct x0 => //=.
         simpl in *. subst. simpl; intuition; eauto.
      ** split_and!; intuition eauto with twodb.
    * subst.
      rewrite Heq_state. simpl. iFrame. simpl. rewrite /disk_state_interp.
      iFrame. iExists _, disk0, (<[i := v]>d). iFrame.
      iFrame. eapply disk_fail_only_one in Hhd; eauto. subst.
      inv_step.
      rewrite disk_status_ctx_upd Heq_state. iFrame.
      iPureIntro.
      split_and!; eauto.
      ** rewrite /upd_disk/upd_default Heq_state => //=.
         destruct x0 => //=.
         simpl in *. subst. simpl; intuition; eauto.
         rewrite Hin_bound //.
      ** split_and!; intuition eauto with twodb.
  }
  by iApply "HΦ".
Qed.

Lemma wp_write_disk1 s E i v' v v0 :
  {{{ ▷ i d1↦ v' ∗ ▷ lease1 i v0 }}} write_disk d1 i v @ s; E {{{ RET tt; i d1↦ v ∗ lease1 i v }}}.
Proof.
  iIntros (Φ) "(>(Hi&Hmaster)&>Hlease) HΦ".
  iMod (master_lease_update i v' v0 v with "[$] [$]") as "(?&?)".
  iApply (wp_write_disk1' with "[$]").
  iNext. iIntros. iApply "HΦ"; iFrame.
Qed.

Lemma wp_read_disk1' s E i v :
  {{{ ▷ i d1◯↦ v }}}
    read_disk d1 i @ s; E
  {{{ mv, RET mv;
      i d1◯↦ v ∗ match mv with
                | None => is_OnlyDisk d0
                | Some v' => ⌜ v = v' ⌝
                end }}}.
Proof.
  iIntros (Φ) ">Hi HΦ". iApply wp_lift_call_step.
  iIntros ((n, σ)) "Hown".
  iModIntro. iSplit.
  { destruct s; auto. iPureIntro. apply snd_lift_non_err.
    inversion 1; inv_step. repeat deex. inv_step.
  }
  iIntros (e2 (n2, σ2) Hstep) "!>".
  inversion Hstep; subst.
  inv_step.
  iDestruct "Hown" as "(?&Hown)".
  iDestruct "Hown" as (mems disk0 disk1) "(Hown_mem&Hown0&Hown1&Hstatus&Hp)".
  iDestruct "Hp" as %(Heq_mem&Heq_disk&Hsize&?).
  iDestruct (gen_heap_valid with "Hown1 Hi") as %Hin_bound.
  simpl in Heq_disk.
  iMod (disk_status_update with "Hstatus") as "($&Htok)"; first eauto.
  destruct (σ.(disks_state)) as [?|?] eqn:Heq_state.
  - simpl. iFrame. iSplitR "Hi HΦ Htok".
    * iExists _, disk0, disk1. iFrame.
      iFrame. simpl. intuition; eauto. subst.
      inversion Hhd.
      { iPureIntro.
        split_and!; eauto; inv_step .
        rewrite Heq_state => //=.
        split_and!; intuition eauto with twodb.
      }
      inv_case; inv_step.
      { iPureIntro.
        split_and!; eauto.
        subst; rewrite /maybe_fail_disk Heq_state => //=.
        split_and!; intuition eauto with twodb.
      }
      { iPureIntro.
        split_and!; eauto.
        subst; rewrite /maybe_fail_disk Heq_state => //=.
        split_and!; intuition eauto with twodb.
      }
    * inversion Hhd.
      {
        rewrite /lookup_disk/get_disk/TwoDisk.disk1. inv_step. rewrite Heq_state.
        rewrite /lookup_default. intuition. subst. rewrite Hin_bound.
        iApply "HΦ"; eauto.
      }
      inv_case; inv_step.
      {
        rewrite /lookup_disk/get_disk/maybe_fail_disk Heq_state //=.
        rewrite /lookup_default. intuition. subst. rewrite Hin_bound.
        iApply "HΦ"; eauto.
      }
      {
        rewrite /lookup_disk/get_disk/maybe_fail_disk Heq_state //=.
        iApply "HΦ"; eauto.
      }
  - eapply disk_fail_only_one in Hhd; eauto. subst.
    simpl. iFrame. iSplitR "Hi HΦ Htok".
    * iExists _, disk0, disk1. iFrame.
      iFrame. simpl. intuition; eauto. subst.
      iPureIntro.
      split_and!; eauto.
      subst; rewrite /maybe_fail_disk Heq_state => //=.
      split_and!; intuition eauto with twodb.
    * rewrite /lookup_disk/get_disk/TwoDisk.disk0/TwoDisk.disk1 ?Heq_state //=.
      destruct id; rewrite /lookup_default; intuition; subst; rewrite ?Hin_bound;
      iApply "HΦ"; eauto.
Qed.

Lemma wp_read_disk1 s E i v :
  {{{ ▷ i d1↦ v }}}
    read_disk d1 i @ s; E
  {{{ mv, RET mv;
      i d1↦ v ∗ match mv with
                | None => is_OnlyDisk d0
                | Some v' => ⌜ v = v' ⌝
                end }}}.
Proof.
  iIntros (Φ) ">(Hi&?) HΦ".
  iApply (wp_read_disk1' with "[$]").
  iNext. iIntros (?) "(?&?)". iApply "HΦ"; iFrame.
Qed.

(* Once disk0 has failed, we can do a "ghost write" to it at any point *)
Lemma wp_write_disk0_only1' {T} s E1 E2 i v v' (p: proc Op T) Φ:
  to_val p = None →
  (|={E1, E2}=> (i d0◯↦ v ∗ is_OnlyDisk d1) ∗ (i d0◯↦ v' -∗ |={E2, E1}=> WP p @ s ; E1 {{ Φ }}))
    -∗ WP p @ s ; E1 {{ Φ }}.
Proof.
  iIntros (?) "Hfupd".
  iApply wp_lift_pre_step; first auto.
  iIntros ((n, σ)) "Hown".
  iMod "Hfupd".
  iDestruct "Hfupd" as "((Hi&Honly)&Hwand)".
  iDestruct "Hown" as "(?&Hown)".
  iDestruct "Hown" as (mems disk0 disk1) "(Hown_mem&Hown0&Hown1&Hstatus&Hp)".
  iDestruct "Hp" as %(Heq_mem&Heq_disk&Hsize&?).
  iDestruct (gen_heap_valid with "Hown0 Hi") as %Hin_bound.
  iDestruct (disk_status_agree with "[$] [$]") as %Hstatus.
  destruct Hstatus as (disk1'&Heq). simpl in *.
  rewrite Heq in Heq_disk. subst.
  iMod (@gen_heap_update with "Hown0 Hi") as "[Hown0 Hi]".
  iMod ("Hwand" with "Hi").
  iFrame. iExists _, _, _; iFrame.
  simpl. rewrite Heq. eauto.
Qed.

(* Once disk0 has failed, we can do a "ghost write" to it at any point *)
Lemma wp_write_disk0_only1 {T} s E1 E2 i v v' v0 (p: proc Op T) Φ:
  to_val p = None →
  (|={E1, E2}=> (i d0↦ v ∗ lease0 i v0 ∗ is_OnlyDisk d1)
                  ∗ ((i d0↦ v' ∗ lease0 i v') -∗ |={E2, E1}=> WP p @ s ; E1 {{ Φ }}))
    -∗ WP p @ s ; E1 {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_write_disk0_only1'; auto.
  iMod "H" as "(((?&?)&?&?)&Hwand)".
  iMod (master_lease_update (hG := exm_disk0_inG) i v v0 v' with "[$] [$]") as "(?&?)".
  iModIntro. iFrame. iIntros. iApply "Hwand". iFrame.
Qed.

Lemma wp_read_disk1_only1' s E i v :
  {{{ ▷ i d1◯↦ v ∗ ▷ is_OnlyDisk d1 }}}
    read_disk d1 i @ s; E
  {{{ RET (Some v); i d1◯↦ v }}}.
Proof.
  iIntros (Φ) "(>Hi&>His_only) HΦ". iApply wp_lift_call_step.
  iIntros ((n, σ)) "Hown".
  iModIntro. iSplit.
  { destruct s; auto. iPureIntro. apply snd_lift_non_err.
    inversion 1; inv_step. repeat deex. inv_step.
  }
  iIntros (e2 (n2, σ2) Hstep) "!>".
  inversion Hstep; subst.
  inv_step.
  iDestruct "Hown" as "(?&Hown)".
  iDestruct "Hown" as (mems disk0 disk1) "(Hown_mem&Hown0&Hown1&Hstatus&Hp)".
  iDestruct "Hp" as %(Heq_mem&Heq_disk&Hsize&?).
  iDestruct (gen_heap_valid with "Hown1 Hi") as %Hin_bound.
  iDestruct (disk_status_agree with "[$] [$]") as %Hstatus.
  destruct Hstatus as (disk1'&Heq). simpl in *.
  rewrite Heq in Heq_disk. subst.
  eapply disk_fail_only_one in Hhd; eauto. subst.
  iFrame. iSplitR "Hi HΦ".
    * iExists _, disk0, disk1'. iFrame.
      iPureIntro.
      split_and!; eauto; inv_step.
      rewrite Heq => //=.
      split_and!; intuition eauto with twodb.
    * rewrite /lookup_disk/get_disk/TwoDisk.disk1. inv_step. rewrite Heq.
      rewrite /lookup_default. intuition. subst. rewrite Hin_bound.
      iApply "HΦ"; eauto.
Qed.

Lemma wp_read_disk1_only1 s E i v :
  {{{ ▷ i d1↦ v ∗ ▷ is_OnlyDisk d1 }}}
    read_disk d1 i @ s; E
  {{{ RET (Some v); i d1↦ v }}}.
Proof.
  iIntros (Φ) "(>(Hi&?)&?) HΦ".
  iApply (wp_read_disk1_only1' with "[$]").
  iNext. iIntros "?". iApply "HΦ"; iFrame.
Qed.

Lemma disk0_lease_agree i v1 v2:
  i d0↦ v1 -∗ lease0 i v2 -∗ ⌜v1 = v2⌝.
Proof.
  iIntros "(_&?) ?". iApply (master_lease_agree with "[$] [$]").
Qed.

Lemma disk0_next i v:
  i d0↦ v ==∗
    (i d0◯↦ v ∗ next_master (hG := exm_disk0_inG) i v) ∗ next_lease (hG := exm_disk0_inG) i v.
Proof.
  iIntros "(?&?)". by iMod (master_next with "[$]") as "($&$)".
Qed.

Lemma disk1_lease_agree i v1 v2:
  i d1↦ v1 -∗ lease1 i v2 -∗ ⌜v1 = v2⌝.
Proof.
  iIntros "(_&?) ?". iApply (master_lease_agree with "[$] [$]").
Qed.

Lemma disk1_next i v:
  i d1↦ v ==∗
    (i d1◯↦ v ∗ next_master (hG := exm_disk1_inG) i v) ∗ next_lease (hG := exm_disk1_inG) i v.
Proof.
  iIntros "(?&?)". by iMod (master_next with "[$]") as "($&$)".
Qed.

End lifting.

(* Essentially the same as the verification of the spinlock in Iris heap_lang
   except we don't allocate locks or pass the pointer to them; there is a dedicated
   lock register. *)

Class lockG Σ := LockG { lock_tokG :> inG Σ (exclR unitO) }.
Definition lockΣ : gFunctors := #[GFunctor (exclR unitO)].
Instance subG_lockΣ {Σ} : subG lockΣ Σ → lockG Σ.
Proof. solve_inG. Qed.

Section lock.
  Context `{!exmachG Σ, !lockG Σ}.

  Definition lock_inv (γ : gname) (i: addr) (P : iProp Σ) : iProp Σ :=
    ((i m↦ 0 ∗ P ∗ own γ (Excl ())) ∨ (∃ v, i m↦ v ∗ ⌜ v ≠ 0 ⌝))%I.

  Definition is_lock (N: namespace) (γ: gname) (i: addr) (P: iProp Σ) : iProp Σ :=
    (inv N (lock_inv γ i P))%I.

  Definition locked (γ: gname) : iProp Σ :=
    own γ (Excl ()).

  Global Instance is_lock_persistent N γ i R : Persistent (is_lock N γ i R).
  Proof. apply _. Qed.

  Global Instance locked_timless γ : Timeless (locked γ).
  Proof. apply _. Qed.

  Lemma lock_init N i v (R: iProp Σ) E : i m↦ v -∗ (⌜ v = 0 ⌝ -∗ R) ={E}=∗ ∃ γ, is_lock N γ i R.
  Proof.
    iIntros "Hl HR".
    iMod (own_alloc (Excl ())) as (γ) "Hexcl"; first done.
    iMod (inv_alloc N _ (lock_inv γ i R) with "[-]").
    { iNext.
      destruct (nat_eq_dec v 0).
      * subst. iLeft; iFrame. iApply "HR"; auto.
      * iRight. iExists _. iFrame. eauto.
    }
    iModIntro; iExists _; done.
  Qed.

  Lemma lock_init_unlocked N i (R: iProp Σ) E : i m↦ 0 -∗ R ={E}=∗ ∃ γ, is_lock N γ i R.
  Proof.
    iIntros "Hl HR".
    iApply (lock_init with "Hl").
    iIntros "_"; iFrame.
  Qed.

  Lemma lock_crack N i (R: iProp Σ) γ E :
    ↑N ⊆ E →
    is_lock N γ i R ={E, E ∖ ↑N}=∗ ▷ ∃ v, i m↦ v ∗ (⌜ v = 0 ⌝ -∗ R).
  Proof.
    intros. rewrite /is_lock. iIntros "Hinv".
    iInv "Hinv" as "[(?&?&?)|HR]" "_".
    - iModIntro. iExists 0. iNext. iFrame; iIntros; auto.
    - iModIntro. iNext. iDestruct "HR" as (v) "(?&%)".
      iExists v. iFrame. iIntros; congruence.
  Qed.

  Lemma wp_lock N γ i (R: iProp Σ):
    {{{ is_lock N γ i R }}} lock i {{{ RET tt; locked γ ∗ R }}}.
  Proof.
    iIntros (Φ) "#Hlock HΦ". iLöb as "IH".
    wp_loop; wp_bind.
    iInv N as "[HL|>HUL]".
    - iDestruct "HL" as "(>H&?&>?)".
      iApply (wp_cas_suc with "[$]"). iIntros "!> Hl !>"; iFrame.
      iSplitL "Hl".
      { iRight. iNext. iExists _. iFrame. eauto. }
      rewrite //=. wp_ret. wp_ret.
      iApply "HΦ"; iFrame.
    - iDestruct "HUL" as (v) "(?&%)".
      iApply (wp_cas_fail with "[$]"); first done. iIntros "!> Hl !>"; iFrame.
      iSplitL "Hl".
      { iRight. iNext. iExists _. iFrame. eauto. }
      rewrite //=. destruct nat_eq_dec; first by congruence. wp_ret. iApply "IH"; eauto.
  Qed.

  Lemma wp_unlock N γ i (R: iProp Σ):
    {{{ is_lock N γ i R ∗ locked γ ∗ R }}} unlock i {{{ RET tt; True }}}.
  Proof.
    iIntros (Φ) "(#Hlock&Hlocked&HR) HΦ".
    iInv N as "[HL|>HUL]".
    - iDestruct "HL" as "(>H&?&>Htok)".
      iDestruct (own_valid_2 with "Htok Hlocked") as %H => //=.
    - iDestruct "HUL" as (v) "(?&%)".
      iApply (wp_write_mem with "[$]"); iIntros "!> H !>".
      iSplitR "HΦ"; last by iApply "HΦ".
      iLeft. iFrame.
  Qed.

  Lemma wp_unlock' N γ i (R: iProp Σ):
    is_lock N γ i R -∗ {{{ locked γ ∗ R }}} unlock i {{{ RET tt; True }}}.
  Proof.
    iIntros "#Hlock". iAlways.
    iIntros (Φ) "(Hlocked&HR) HΦ".
    iApply (wp_unlock with "[-HΦ]").
    { iFrame "Hlock". iFrame. }
    eauto.
  Qed.
End lock.
