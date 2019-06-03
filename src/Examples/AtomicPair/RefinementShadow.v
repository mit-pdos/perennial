From iris.algebra Require Import auth gmap list.
Require Export CSL.Refinement.
Require Import AtomicPairAPI AtomicPair.ImplShadow ExMach.WeakestPre ExMach.RefinementAdequacy.
Require Import AtomicPair.Helpers.
Unset Implicit Arguments.

Existing Instance from_exist_left_sep_later.

Local Ltac destruct_einner H :=
  iDestruct H as (? (?&?) (?&?)) ">(Hown1&Hown2&Hown3&Hsource&Hmap)";
  iDestruct "Hmap" as "(Hptr&Hcase)";
  repeat unify_ghost.

Set Default Proof Using "Type".
Section refinement_triples.
  Context `{!exmachG Σ, lockG Σ, !@cfgG (AtomicPair.Op) (AtomicPair.l) Σ,
            !inG Σ (authR (optionUR (exclR (prodC natC natC)))),
            !inG Σ (authR (optionUR (exclR natC)))}.
  Import ExMach.

  (* TODO: this should work, but the invariant is too global: ideally,
     most threads should not care about the value in the non-pointed to
     copy, and a writer who holds the lock should be able to modify it freely
     without opening this invariant up prior to updating the pointer *)
  Definition ptr_map (ptr_val : nat) (pcurr: nat * nat) (pother: nat * nat) :=
    (ptr_addr d↦ ptr_val ∗
     (read_addrs ptr_val).1 d↦ pcurr.1 ∗
     (read_addrs ptr_val).2 d↦ pcurr.2 ∗
     (write_addrs ptr_val).1 d↦ pother.1 ∗
     (write_addrs ptr_val).2 d↦ pother.2)%I.

  Definition ExecInner γ1 γ2 γ3 :=
    (∃ (ptr_val : nat) (pcurr: nat * nat) (pother: nat * nat),
        own γ1 (● (Excl' ptr_val))
            ∗ own γ2 (● (Excl' pcurr))
            ∗ own γ3 (● (Excl' pother))
            ∗ source_state pcurr ∗
            ptr_map ptr_val pcurr pother)%I.


  (* Holding the lock guarantees the value of the atomic pair/pointer will not
     change out from underneath you -- this is enforced by granting ownership of
     appropriate ghost variables *)
  Definition ExecLockInv γ1 γ2 γ3 :=
    (∃ ptr_val (pcurr : nat * nat) (pother: nat * nat),
        own γ1 (◯ (Excl' ptr_val))
            ∗ own γ2 (◯ (Excl' pcurr))
            ∗ own γ3 (◯ (Excl' pother))
    )%I.

  (* Post-crash, pre recovery we know the ptr mapping is in a good state w.r.t the
     abstract state, and the lock must have been reset 0 *)

  Definition CrashInner :=
    (∃ (ptr_val : nat) (pcurr: nat * nat) pother,
        source_state pcurr ∗ ptr_map ptr_val pcurr pother ∗ lock_addr m↦ 0)%I.

  Definition lN : namespace := (nroot.@"lock").
  Definition iN : namespace := (nroot.@"inner").

  Definition ExecInv :=
    (source_ctx ∗ ∃ γlock γ1 γ2 γ3, is_lock lN γlock lock_addr (ExecLockInv γ1 γ2 γ3)
                                           ∗ inv iN (ExecInner γ1 γ2 γ3))%I.
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
    iDestruct "Hinv" as (γlock γ1 γ2 γ3) "(#Hlockinv&#Hinv)".
    wp_lock "(Hlocked&HEL)".
    iDestruct "HEL" as (ptr_val pcurr pother) "(Hptr_ghost&Hpair_ghost&Hother_ghost)".
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
    iMod (ghost_var_update γ3 (new_fst, n2) with "Hown3 [$]") as "(Hown3&Hother_ghost)".
    iExists ptr_val. simpl. iExists _, _; iFrame.
    simpl. iFrame.

    iModIntro.
    wp_bind.
    iInv "Hinv" as "H".
    destruct_einner "H".
    iDestruct "Hcase" as "(Ho1&Ho2&Hfst&Hsnd)".
    wp_step.
    iMod (ghost_var_update γ3 (new_fst, new_snd) with "Hown3 [$]") as "(Hown3&Hother_ghost)".
    iModIntro; iExists _, _; iFrame.
    simpl.
    iExists (_, _). iFrame.

    wp_bind.
    iFastInv "Hinv" "H".
    destruct_einner "H".
    iMod (ghost_var_update γ1 (swap_ptr ptr_val) with "Hown1 [$]") as "(Hown1&Hptr_ghost)".
    iMod (ghost_var_update γ2 (new_fst, new_snd) with "Hown2 [$]") as "(Hown2&Hpair_ghost)".
    iMod (ghost_var_update γ3 (n, n0) with "Hown3 [$]") as "(Hown3&Hother_ghost)".
    iMod (ghost_step_lifting with "Hj Hsource_inv Hsource") as "(Hj&Hsource&_)".
    { intros. eexists. do 2 eexists; split; last by eauto. econstructor; eauto.
      econstructor.
    }
    { solve_ndisj. }
    wp_step.
    iExists (swap_ptr ptr_val). iExists _, _; iFrame.
    iDestruct "Hcase" as "(Ho1&Ho2&Hfst'&Hsnd')".
    rewrite ?read_of_swap ?write_of_swap; iFrame.

    iModIntro.
    wp_unlock "[-HΦ Hreg Hj]"; iFrame.
    { iExists _, _, _. iFrame. }
    iApply "HΦ"; iFrame.
  Qed.

  Lemma read_refinement {T} j K `{LanguageCtx AtomicPair.Op (nat*nat) T AtomicPair.l K}:
    {{{ j ⤇ K (Call (AtomicPair.Read)) ∗ Registered ∗ ExecInv }}}
      read
    {{{ v, RET v; j ⤇ K (Ret v) ∗ Registered }}}.
  Proof.
    iIntros (Φ) "(Hj&Hreg&#Hsource_inv&Hinv) HΦ".
    iDestruct "Hinv" as (γlock γ1 γ2 γ3) "(#Hlockinv&#Hinv)".
    wp_lock "(Hlocked&HEL)".
    iDestruct "HEL" as (ptr_val pcurr pother) "(Hptr_ghost&Hpair_ghost&Hother_ghost)".

    wp_bind.
    iInv "Hinv" as "H".
    destruct_einner "H".
    wp_step.
    iModIntro; iExists _, _, _; iFrame.

    wp_bind.
    iInv "Hinv" as "H".
    destruct_einner "H".
    iDestruct "Hcase" as "(Hfst&Hsnd&?&?)".
    wp_step.
    iModIntro; iExists _, _, _; iFrame.

    wp_bind.
    iInv "Hinv" as "H".
    destruct_einner "H".
    iDestruct "Hcase" as "(Hfst&Hsnd&?&?)".
    wp_step.
    iMod (ghost_step_lifting with "Hj Hsource_inv Hsource") as "(Hj&Hsource&_)".
    { intros. eexists. do 2 eexists; split; last by eauto. econstructor; eauto.
      econstructor.
    }
    { solve_ndisj. }

    iModIntro; iExists _, _, _; iFrame.
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
    (([∗ map] i↦v ∈ init_zero, i d↦ v)
       -∗ ptr_addr d↦ 0 ∗ copy0_fst d↦ 0 ∗ copy0_snd d↦ 0
          ∗ copy1_fst d↦ 0 ∗ copy1_snd d↦ 0)%I.
  Proof.
    iIntros "Hdisk".
    iPoseProof (disk_ptr_iter_split_aux O 4 with "Hdisk") as "H".
    { rewrite /size. lia. }
    iDestruct "H" as "($&_)".
  Qed.

End refinement_triples.

Module sRT <: exmach_refinement_type.

Definition helperΣ : gFunctors := #[GFunctor (authR (optionUR (exclR (natC))));
                                     GFunctor (authR (optionUR (exclR (prodC natC natC))))].
Instance subG_helperΣ : subG helperΣ Σ → inG Σ (authR (optionUR (exclR (natC)))).
Proof. solve_inG. Qed.
Instance subG_helperΣ' : subG helperΣ Σ → inG Σ (authR (optionUR (exclR (prodC natC natC)))).
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
  Instance REG : inG Σ (csumR countingR (authR (optionUR (exclR unitC)))). apply _. Qed.

  Definition exec_inv := fun H1 H2 => (@ExecInv Σ H2 _ H1 _ _)%I.
  Definition exec_inner :=
    fun H1 H2 => (∃ v, lock_addr m↦ v ∗
          (∃ γ1 γ2 γ3, (⌜ v = 0  ⌝ -∗ @ExecLockInv Σ _ _ γ1 γ2 γ3)
                        ∗ @ExecInner Σ H2 H1 _ _ γ1 γ2 γ3))%I.

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

  Lemma recv_triple: recv_triple_type.
  Proof.
    red. intros. iIntros "((#Hctx&#Hinv)&_)".
    wp_ret. iInv "Hinv" as (ptr_val pcurr pother) ">(?&Hcase&?)" "_".
    iMod (own_alloc (● (Excl' ptr_val) ⋅ ◯ (Excl' ptr_val))) as (γ1) "[Hauth_ptr Hfrag_ptr]".
    { apply auth_both_valid; split; eauto. econstructor. }
    iMod (own_alloc (● (Excl' pcurr) ⋅ ◯ (Excl' pcurr))) as (γ2) "[Hauth_curr Hfrag_curr]".
    { apply auth_both_valid; split; eauto. econstructor. }
    iMod (own_alloc (● (Excl' pother) ⋅ ◯ (Excl' pother))) as (γ3) "[Hauth_other Hfrag_other]".
    { apply auth_both_valid; split; eauto. econstructor. }
    iApply (fupd_mask_weaken _ _).
    { solve_ndisj. }
    iExists pcurr, pcurr. iFrame.
    iSplitL "".
    { iPureIntro; econstructor. }
    iClear "Hctx Hinv".
    iIntros (???) "(#Hctx&Hstate)".
    iModIntro. iExists _. iFrame. iExists γ1, γ2, γ3.
    iSplitL "Hfrag_ptr Hfrag_curr Hfrag_other"; iIntros; iExists _, _, _; iFrame.
  Qed.

  Lemma init_wf: ∀ σ1a σ1c, init_absr σ1a σ1c → ExMach.state_wf σ1c.
  Proof.
    intros ?? (H&?). inversion H. subst. eapply ExMach.init_state_wf.
  Qed.

  Lemma init_exec_inner : init_exec_inner_type.
  Proof.
    red. intros ?? (H&Hinit) ??. inversion H. inversion Hinit. subst.
    iIntros "(Hmem&Hdisk&#?&Hstate)".
    iMod (own_alloc (● (Excl' 0) ⋅ ◯ (Excl' 0))) as (γ1) "[Hauth_ptr Hfrag_ptr]".
    { apply auth_both_valid; split; eauto. econstructor. }
    iMod (own_alloc (● (Excl' (0, 0)) ⋅ ◯ (Excl' (0, 0)))) as (γ2) "[Hauth_curr Hfrag_curr]".
    { apply auth_both_valid; split; eauto. econstructor. }
    iMod (own_alloc (● (Excl' (0, 0)) ⋅ ◯ (Excl' (0, 0)))) as (γ3) "[Hauth_other Hfrag_other]".
    { apply auth_both_valid; split; eauto. econstructor. }
    iPoseProof (init_mem_split with "Hmem") as "?".
    iPoseProof (init_disk_split with "Hdisk") as "(?&?&?&?&?)".
    iModIntro. iExists _. iFrame. iExists γ1, γ2, γ3.
    iSplitL "Hfrag_ptr Hfrag_curr Hfrag_other"; iIntros; iExists _, _, _; iFrame.
    simpl. iFrame.
  Qed.

  Lemma exec_inv_preserve_crash: exec_inv_preserve_crash_type.
  Proof.
    red. intros. iIntros "(#Hctx&#Hinv)".
    iDestruct "Hinv" as (γlock γ1 γ2 γ3) "(#Hlock&#Hinv)".
    iInv "Hinv" as "Hopen" "_".
    destruct_einner "Hopen".
    iApply fupd_mask_weaken; first by solve_ndisj.
    iIntros (??) "Hmem".
    iModIntro. iExists _, _, _. iFrame.
    iPoseProof (@init_mem_split with "Hmem") as "?".
    iFrame.
  Qed.

  Lemma crash_inv_preserve_crash: crash_inv_preserve_crash_type.
  Proof.
    red. intros. iIntros "(#Hctx&#Hinv)".
    iInv "Hinv" as ">Hopen" "_".
    iDestruct "Hopen" as (???) "(?&?&_)".
    iApply fupd_mask_weaken; first by solve_ndisj.
    iIntros (??) "Hmem".
    iModIntro. iExists _, _, _. iFrame.
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
    iDestruct "Hinv" as (γ1 γ2 γ3) "(Hlock&Hinner)".
    iMod (@lock_init Σ (ExMachG _ (exm_invG) (exm_mem_inG) (exm_disk_inG) _) _ lN
                     lock_addr _ (ExecLockInv γ1 γ2 γ3) with "[$] [-Hinner]") as (γlock) "H".
    { iFrame. }
    iMod (@inv_alloc Σ (exm_invG) iN _ (ExecInner γ1 γ2 γ3) with "[Hinner]").
    { iFrame. }
    iModIntro. iFrame "Hsrc". iExists _, _, _, _. iFrame.
  Qed.

  Lemma exec_inv_preserve_finish : exec_inv_preserve_finish_type.
  Proof.
    iIntros (??) "? (?&H)".
    iDestruct "H" as (????) "(Hlock&Hinv)".
    iInv "Hinv" as "H" "_".
    iDestruct "H" as (ptr (n1&n2) (n1'&n2')) ">(Hown1&Hown2&Hown3&Hsource&Hmap)";
      iDestruct "Hmap" as "(Hptr&Hcase)";
      repeat unify_ghost.
    iMod (lock_crack with "Hlock") as ">H"; first by solve_ndisj.
    iDestruct "H" as (v) "(?&?)".
    iApply fupd_mask_weaken; first by solve_ndisj.
    iExists _, _; iFrame.
    iSplitL "".
    { iPureIntro. econstructor. }
    iFrame. iIntros (????) "(?&?&Hmem)".
    iPoseProof (@init_mem_split with "Hmem") as "?".
    iExists _. iFrame. rewrite /ExecLockInv.
    iMod (own_alloc (● (Excl' ptr) ⋅ ◯ (Excl' ptr))) as (γ1') "[Hauth_ptr Hfrag_ptr]".
    { apply auth_both_valid; split; eauto. econstructor. }
    iMod (own_alloc (● (Excl' (n1, n2)) ⋅ ◯ (Excl' (n1, n2))))
      as (γ2') "[Hauth_curr Hfrag_curr]".
    { apply auth_both_valid; split; eauto. econstructor. }
    iMod (own_alloc (● (Excl' (n1', n2')) ⋅ ◯ (Excl' (n1', n2'))))
      as (γ3') "[Hauth_other Hfrag_other]".
    { apply auth_both_valid; split; eauto. econstructor. }
    iExists γ1', γ2', γ3'. iFrame.
    iModIntro. rewrite /ExecInner. iSplitL "Hfrag_ptr Hfrag_curr Hfrag_other".
    { iIntros. iExists _, _, _. iFrame. }
    { iIntros. iExists _, _, _. iFrame. }
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