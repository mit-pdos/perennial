From iris.algebra Require Import auth gmap list.
From Perennial Require Export CSL.Refinement.
From Perennial Require Import AtomicPairAPI AtomicPair.ImplShadow ExMach.WeakestPre ExMach.RefinementAdequacy.
From Perennial Require Import AtomicPair.Helpers.
Unset Implicit Arguments.

Existing Instance from_exist_left_sep_later.

Local Ltac destruct_einner H :=
  iDestruct H as (? (?&?) (?&?)) ">(Hsource&Hmap)";
  iDestruct "Hmap" as "(Hptr&Hcase)";
  repeat unify_lease;
  repeat unify_ghost.

Set Default Proof Using "Type".
Section refinement_triples.
  Context `{!exmachG Σ, lockG Σ, !@cfgG (AtomicPair.Op) (AtomicPair.l) Σ,
            !inG Σ (authR (optionUR (exclR (prodO natO natO)))),
            !inG Σ (authR (optionUR (exclR natO)))}.
  Import ExMach.

  (* TODO: this should work, but the invariant is too global: ideally,
     most threads should not care about the value in the non-pointed to
     copy, and a writer who holds the lock should be able to modify it freely
     without opening this invariant up prior to updating the pointer *)
  Definition ptr_map (ptr_val : nat) (pcurr: nat * nat) (pother: nat * nat) :=
    (ptr_addr d↦ ptr_val
     ∗ (read_addrs ptr_val).1 d↦ pcurr.1
     ∗ (read_addrs ptr_val).2 d↦ pcurr.2
     ∗ (write_addrs ptr_val).1 d↦ pother.1
     ∗ (write_addrs ptr_val).2 d↦ pother.2)%I.

  Definition ExecInner :=
    (∃ (ptr_val : nat) (pcurr: nat * nat) (pother: nat * nat),
        source_state pcurr ∗ ptr_map ptr_val pcurr pother)%I.

  (* Holding the lock guarantees the value of the atomic pair/pointer will not
     change out from underneath you -- this is enforced by granting leases *)

  Definition lease_map (ptr_val : nat) (pcurr: nat * nat) (pother: nat * nat) :=
     (lease ptr_addr ptr_val
      ∗ lease (read_addrs ptr_val).1 pcurr.1
      ∗ lease (read_addrs ptr_val).2 pcurr.2
      ∗ lease (write_addrs ptr_val).1 pother.1
      ∗ lease (write_addrs ptr_val).2 pother.2)%I.

  Definition ExecLockInv :=
    (∃ (ptr_val : nat) (pcurr: nat * nat) pother,
        lease_map ptr_val pcurr pother)%I.

  (* Post-crash, pre recovery we know the ptr mapping is in a good state w.r.t the
     abstract state, and the lock must have been reset 0 *)

  Definition CrashInner :=
    (∃ (ptr_val : nat) (pcurr: nat * nat) pother,
        source_state pcurr ∗ ptr_map ptr_val pcurr pother ∗ lease_map ptr_val pcurr pother
                     ∗ lock_addr m↦ 0)%I.

  Definition lN : namespace := (nroot.@"lock").
  Definition iN : namespace := (nroot.@"inner").

  Definition ExecInv :=
    (source_ctx ∗ ∃ γlock, is_lock lN γlock lock_addr ExecLockInv ∗ inv iN ExecInner)%I.
  Definition CrashInv := (source_ctx ∗ inv iN CrashInner)%I.

  Lemma read_of_swap ptr_val :
    (read_addrs (swap_ptr ptr_val)) = write_addrs ptr_val.
  Proof. destruct ptr_val => //=. Qed.

  Lemma write_of_swap ptr_val :
    (write_addrs (swap_ptr ptr_val)) = read_addrs ptr_val.
  Proof. destruct ptr_val => //=. Qed.

  Lemma write_refinement {T} j K `{LanguageCtx AtomicPair.Op unit T AtomicPair.l K} p:
    {{{ j ⤇ K (Call (AtomicPair.Write p)) ∗ Registered ∗ ExecInv }}}
      write p
    {{{ v, RET v; j ⤇ K (Ret v) ∗ Registered }}}.
  Proof.
    iIntros (Φ) "(Hj&Hreg&#Hsource_inv&Hinv) HΦ".
    iDestruct "Hinv" as (γlock) "(#Hlockinv&#Hinv)".
    wp_lock "(Hlocked&HEL)".
    iDestruct "HEL" as (ptr_val pcurr pother)
                         "(Hptr_ghost&Hpair1_ghost&Hpair2_ghost&Hother1_ghost&Hother2_ghost)".
    wp_bind.
    iInv "Hinv" as "H".
    destruct_einner "H".
    wp_step.
    iModIntro; iExists _, _, _; iFrame.
    destruct p as (new_fst&new_snd).

    wp_bind.
    iFastInv "Hinv" "H".
    destruct_einner "H".
    iDestruct "Hcase" as "(?&?&Hfst&Hsnd)".
    wp_step.
    iExists ptr_val. simpl. iExists _, (new_fst, _); iFrame.
    simpl. iFrame.

    iModIntro.
    wp_bind.
    iInv "Hinv" as "H".
    destruct_einner "H".
    iDestruct "Hcase" as "(Ho1&Ho2&Hfst&Hsnd)".
    wp_step.
    iModIntro; iExists _, _; iFrame.
    simpl.
    iExists (_, _). iFrame.

    wp_bind.
    iFastInv "Hinv" "H".
    destruct_einner "H".
    iDestruct "Hcase" as "(Ho1&Ho2&Hfst'&Hsnd')".
    repeat unify_lease.
    iMod (ghost_step_lifting with "Hj Hsource_inv Hsource") as "(Hj&Hsource&_)".
    { intros. eexists. do 2 eexists; split; last by eauto. econstructor; eauto.
      econstructor.
    }
    { solve_ndisj. }
    wp_step.
    iExists (swap_ptr ptr_val). iExists _, _; iFrame.
    rewrite ?read_of_swap ?write_of_swap; iFrame.

    iModIntro.
    wp_unlock "[-HΦ Hreg Hj]"; iFrame.
    {
      iExists _, (_, _), (_, _).
      iFrame. rewrite ?read_of_swap ?write_of_swap; iFrame.
    }
    iApply "HΦ"; iFrame.
  Qed.

  Lemma read_refinement {T} j K `{LanguageCtx AtomicPair.Op (nat*nat) T AtomicPair.l K}:
    {{{ j ⤇ K (Call (AtomicPair.Read)) ∗ Registered ∗ ExecInv }}}
      read
    {{{ v, RET v; j ⤇ K (Ret v) ∗ Registered }}}.
  Proof.
    iIntros (Φ) "(Hj&Hreg&#Hsource_inv&Hinv) HΦ".
    iDestruct "Hinv" as (γlock) "(#Hlockinv&#Hinv)".
    wp_lock "(Hlocked&HEL)".
    iDestruct "HEL" as (ptr_val pcurr pother)
                         "(Hptr_ghost&Hpair1_ghost&Hpair2_ghost&Hother1_ghost&Hother2_ghost)".

    wp_bind.
    iInv "Hinv" as "H".
    destruct_einner "H".
    wp_step.
    iModIntro; iExists _, _, _; iFrame.

    wp_bind.
    iInv "Hinv" as "H".
    destruct_einner "H".
    iDestruct "Hcase" as "(Hfst&Hsnd&?&?)".
    simpl. repeat unify_lease.
    wp_step.
    iModIntro; iExists _, (_, _), (_, _); iFrame.

    wp_bind.
    iInv "Hinv" as "H".
    destruct_einner "H".
    iDestruct "Hcase" as "(Hfst&Hsnd&?&?)".
    simpl. repeat unify_lease.
    repeat unify_lease.
    wp_step.
    iMod (ghost_step_lifting with "Hj Hsource_inv Hsource") as "(Hj&Hsource&_)".
    { intros. eexists. do 2 eexists; split; last by eauto. econstructor; eauto.
      econstructor.
    }
    { solve_ndisj. }

    iModIntro; iExists _, (_, _), (_, _); iFrame.
    wp_bind.
    wp_unlock "[-HΦ Hreg Hj]".
    { iExists _, _, _. iFrame. }
    wp_ret. iApply "HΦ"; iFrame.
  Qed.

  Lemma init_mem_split:
    (([∗ map] i↦v ∈ init_zero, i m↦ v) -∗ lock_addr m↦ 0)%I.
  Proof.
    iIntros "Hmem".
    rewrite (big_opM_delete _ _ 0 0); last first.
    { rewrite /ExMach.mem_state. apply init_zero_lookup_lt_zero. rewrite /size. lia. }
    iDestruct "Hmem" as "(?&_)".
    iFrame.
  Qed.

  Lemma init_disk_split:
    (([∗ map] i↦v ∈ init_zero, i d↦ v ∗ lease i v)
       -∗ (ptr_addr d↦ 0
          ∗ copy0_fst d↦ 0 ∗ copy0_snd d↦ 0
          ∗ copy1_fst d↦ 0 ∗ copy1_snd d↦ 0)
          ∗ lease ptr_addr 0
          ∗ lease copy0_fst 0 ∗ lease copy0_snd 0
          ∗ lease copy1_fst 0 ∗ lease copy1_snd 0)%I.
  Proof.
    iIntros "Hdisk".
    iPoseProof (disk_ptr_iter_split_aux O 4 with "Hdisk") as "H".
    { rewrite /size. lia. }
    iDestruct "H" as "(H&_)".
    repeat iDestruct "H" as "((?&?)&H)". iFrame.
  Qed.

End refinement_triples.

Module sRT <: exmach_refinement_type.

Definition helperΣ : gFunctors := #[GFunctor (authR (optionUR (exclR (natO))));
                                     GFunctor (authR (optionUR (exclR (prodO natO natO))))].
Instance subG_helperΣ : subG helperΣ Σ → inG Σ (authR (optionUR (exclR (natO)))).
Proof. solve_inG. Qed.
Instance subG_helperΣ' : subG helperΣ Σ → inG Σ (authR (optionUR (exclR (prodO natO natO)))).
Proof. solve_inG. Qed.

Definition Σ : gFunctors := #[Adequacy.exmachΣ; @cfgΣ AtomicPair.Op AtomicPair.l; lockΣ; helperΣ].

Definition init_absr σ1a σ1c :=
  ExMach.l.(initP) σ1c ∧ AtomicPair.l.(initP) σ1a.

  Definition OpT := AtomicPair.Op.
  Definition Λa := AtomicPair.l.

  Definition impl := ImplShadow.impl.
  Existing Instance subG_cfgPreG.

  Instance CFG : @cfgPreG AtomicPair.Op AtomicPair.l Σ. apply _. Qed.
  Instance HEX : ExMach.Adequacy.exmachPreG Σ. apply _. Qed.
  Instance INV : Adequacy.invPreG Σ. apply _. Qed.
  Instance REG : inG Σ (csumR countingR (authR (optionUR (exclR unitO)))). apply _. Qed.

  Global Instance inG_inst1: inG Σ (authR (optionUR (exclR (prodO natO natO)))).
  Proof. apply _. Qed.

  Global Instance inG_inst2: inG Σ (authR (optionUR (exclR natO))).
  Proof. apply _. Qed.

  Global Instance inG_inst3: lockG Σ.
  Proof. apply _. Qed.

  Definition exec_inv := fun H1 H2 => (@ExecInv Σ H2 _ H1)%I.
  Definition exec_inner :=
    fun H1 H2 => (∃ v, lock_addr m↦ v ∗
          ((⌜ v = 0  ⌝ -∗ @ExecLockInv Σ H2) ∗ @ExecInner Σ H2 H1))%I.

  Definition crash_param := fun (_ : @cfgG OpT Λa Σ) (_ : exmachG Σ) => unit.
  Definition crash_inv := fun H1 H2 (_ : crash_param _ _) => @CrashInv Σ H2 H1.
  Definition crash_starter :=
    fun H1 H2 (_ : crash_param H1 H2) => (True%I : iProp Σ).
  Definition crash_inner := fun H1 H2 => (@CrashInner Σ H2 H1)%I.
  Definition E := nclose sourceN.

  Definition recv: proc ExMach.Op unit := Ret tt.

End sRT.

Module sRD := exmach_refinement_definitions sRT.

Module sRO : exmach_refinement_obligations sRT.

  Module eRD := exmach_refinement_definitions sRT.
  Import sRT.
  Import sRD.

  Lemma einv_persist: forall {H1 : @cfgG OpT Λa Σ} {H2 : _},
      Persistent (exec_inv H1 H2).
  Proof. apply _. Qed.

  Lemma cinv_persist: forall {H1 : @cfgG OpT Λa Σ} {H2 : _} P,
      Persistent (crash_inv H1 H2 P).
  Proof. apply _. Qed.

  Lemma nameIncl: nclose sourceN ⊆ E.
  Proof. solve_ndisj. Qed.

  Lemma recsingle: recover impl = rec_singleton recv.
  Proof. trivial. Qed.

  Lemma refinement_op_triples: refinement_op_triples_type.
  Proof.
    red. intros. iIntros "(?&?&HDB)". destruct op.
    - iApply (write_refinement with "[$]"). iNext. iIntros (?) "H". iFrame.
    - iApply (read_refinement with "[$]"). iNext. iIntros (?) "H". iFrame.
  Qed.

  Lemma exec_inv_source_ctx: ∀ {H1 H2}, exec_inv H1 H2 ⊢ source_ctx.
  Proof. iIntros (??) "(?&?)"; eauto. Qed.

  Lemma ptr_map_next {H: exmachG Σ} Hinv Hmem Hreg ptr_val curr other:
    ptr_map ptr_val curr other ==∗
            let Hex := ExMachG Σ Hinv Hmem (next_leased_heapG (hG := (exm_disk_inG))) Hreg in
            ptr_map ptr_val curr other ∗ lease_map ptr_val curr other.
  Proof.
    iIntros "(Hptr&Ho1&Ho2&Hc1&Hc2)".
    by repeat iMod (disk_next with "[$]") as "($&$)".
  Qed.

  Lemma recv_triple: recv_triple_type.
  Proof.
    red. intros. iIntros "((#Hctx&#Hinv)&_)".
    wp_ret. iInv "Hinv" as (ptr_val pcurr pother) ">(?&Hcase&Hlease&?)" "_".
    iApply (fupd_mask_weaken _ _).
    { solve_ndisj. }
    iExists pcurr, pcurr. iFrame.
    iSplitL "".
    { iPureIntro; econstructor. }
    iClear "Hctx Hinv".
    iIntros (???) "(#Hctx&Hstate)".
    iMod (ptr_map_next with "Hcase") as "(Hp&Hl)".
    iExists 0. iFrame.
    iSplitL "Hl"; iModIntro; iIntros; iExists _, _, _; iFrame.
  Qed.

  Lemma init_wf: ∀ σ1a σ1c, init_absr σ1a σ1c → ExMach.state_wf σ1c.
  Proof.
    intros ?? (H&?). inversion H. subst. eapply ExMach.init_state_wf.
  Qed.

  Lemma init_exec_inner : init_exec_inner_type.
  Proof.
    red. intros ?? (H&Hinit) ??. inversion H. inversion Hinit. subst.
    iIntros "(Hmem&Hdisk&#?&Hstate)".
    iPoseProof (init_mem_split with "Hmem") as "?".
    iPoseProof (init_disk_split with "Hdisk") as "(Hd&Hl)".
    iModIntro. iExists _. iFrame.
    iSplitL "Hl".
    - iDestruct "Hl" as "(?&?&?&?&?)". iIntros "_". iExists 0, (_, _), (_, _). iFrame.
    - iDestruct "Hd" as "(?&?&?&?&?)". iExists 0, (_, _), (_, _). iFrame.
  Qed.

  Lemma exec_inv_preserve_crash: exec_inv_preserve_crash_type.
  Proof.
    red. intros. iIntros "(#Hctx&#Hinv)".
    iDestruct "Hinv" as (γlock) "(#Hlock&#Hinv)".
    iInv "Hinv" as "Hopen" "_".
    destruct_einner "Hopen".
    iApply fupd_mask_weaken; first by solve_ndisj.
    iIntros (??) "Hmem".
    iPoseProof (@init_mem_split with "Hmem") as "?".
    iMod (ptr_map_next with "[Hptr Hcase]") as "(?&?)"; first by iFrame.
    iModIntro. iExists _, (_ , _), (_, _). iFrame.
  Qed.

  Lemma crash_inv_preserve_crash: crash_inv_preserve_crash_type.
  Proof.
    red. intros. iIntros "(#Hctx&#Hinv)".
    iInv "Hinv" as ">Hopen" "_".
    iDestruct "Hopen" as (? (?&?) (?&?)) "(?&Hcase&_)".
    iApply fupd_mask_weaken; first by solve_ndisj.
    iIntros (??) "Hmem".
    iMod (ptr_map_next with "Hcase") as "(?&?)".
    iModIntro. iExists _, (_ , _), (_, _). iFrame.
    iPoseProof (@init_mem_split with "Hmem") as "?".
    iFrame.
  Qed.

  Lemma crash_inner_inv : crash_inner_inv_type.
  Proof.
    red. intros. iIntros "(Hinv&#Hsrc)".
    iDestruct "Hinv" as (invG) "Hinv".
    iDestruct "Hinv" as (???) "(?&?&?)".
    iMod (@inv_alloc Σ (exm_invG) iN _ CrashInner with "[-]").
    { iNext. iExists _, _, _; iFrame. }
    iModIntro. iFrame. iExists tt. iFrame "Hsrc".
  Qed.

  Lemma exec_inner_inv : exec_inner_inv_type.
  Proof.
    red. intros. iIntros "(Hinv&#Hsrc)".
    iDestruct "Hinv" as (invG v) "Hinv".
    iDestruct "Hinv" as "(?&Hinv)".
    iDestruct "Hinv" as "(Hlock&Hinner)".
    iMod (@lock_init Σ (ExMachG _ (exm_invG) (exm_mem_inG) (exm_disk_inG) _) _ lN
                     lock_addr _ (ExecLockInv) with "[$] [-Hinner]") as (γlock) "H".
    { iFrame. }
    iMod (@inv_alloc Σ (exm_invG) iN _ (ExecInner) with "[Hinner]").
    { iFrame. }
    iModIntro. iFrame "Hsrc". iExists _. iFrame.
  Qed.

  Lemma exec_inv_preserve_finish : exec_inv_preserve_finish_type.
  Proof.
    iIntros (??) "? (?&H)".
    iDestruct "H" as (?) "(Hlock&Hinv)".
    iInv "Hinv" as "H" "_".
    iDestruct "H" as (ptr (n1&n2) (n1'&n2')) ">(Hsource&Hmap)".
    iMod (lock_crack with "Hlock") as ">H"; first by solve_ndisj.
    iDestruct "H" as (v) "(?&?)".
    iApply fupd_mask_weaken; first by solve_ndisj.
    iExists _, _; iFrame.
    iSplitL "".
    { iPureIntro. econstructor. }
    iIntros (????) "(?&?&Hmem)".
    iMod (ptr_map_next with "Hmap") as "(Hp&Hl)".
    iPoseProof (@init_mem_split with "Hmem") as "?".
    iExists _. iFrame. rewrite /ExecLockInv.
    iSplitL "Hl"; iModIntro; iIntros; iExists _, (_, _), (_, _); iFrame.
  Qed.

End sRO.

Module sR := exmach_refinement sRT sRO.
Import sR.

Lemma exmach_crash_refinement_seq {T} σ1c σ1a (es: proc_seq AtomicPair.Op T) :
  sRT.init_absr σ1a σ1c →
  wf_client_seq es →
  ¬ proc_exec_seq AtomicPair.l es (rec_singleton (Ret ())) (1, σ1a) Err →
  ∀ σ2c res, proc_exec_seq ExMach.l (compile_proc_seq ImplShadow.impl es)
                                      (rec_singleton recv) (1, σ1c) (Val σ2c res) →
  ∃ σ2a, proc_exec_seq AtomicPair.l es (rec_singleton (Ret tt)) (1, σ1a) (Val σ2a res).
Proof. apply sR.R.crash_refinement_seq. Qed.
