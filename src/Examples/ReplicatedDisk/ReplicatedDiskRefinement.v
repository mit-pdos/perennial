From iris.algebra Require Import auth gmap list.
Require Export CSL.Refinement CSL.NamedDestruct.
Require Import OneDiskAPI ReplicatedDiskImpl ReplicatedDisk.WeakestPre ReplicatedDisk.RefinementAdequacy.
Set Default Proof Using "All".
Unset Implicit Arguments.

From Tactical Require Import UnfoldLemma.

Definition gen_heap_ctx' {L V} `{Countable L} `{hG: gen_heapG L V Σ}
  := (∃ σ, gen_heap_ctx σ)%I.
Lemma gen_heap_update' {L V} `{Countable L} `{hG: gen_heapG L V Σ} l v1 v2:
    gen_heap_ctx' -∗ mapsto l 1 v1 ==∗ gen_heap_ctx' ∗ mapsto l 1 v2.
Proof.
  iIntros "Hctx Hmapsto". iDestruct "Hctx" as (σ) "H".
  iMod (gen_heap_update with "[$] [$]") as "(?&$)".
  iExists _; eauto.
Qed.

Inductive addr_status :=
| Sync
| Unsync (j: nat) {T2} K `{LanguageCtx _ unit T2 OneDisk.l K}.

Canonical Structure addr_statusC :=
  leibnizC addr_status.
Canonical Structure addr_statusF :=
  discreteC addr_status.

Section refinement_triples.
  Context `{!exmachG Σ, lockG Σ, !@cfgG (OneDisk.Op) (OneDisk.l) Σ}.
  Context {hD0Lease:  gen_heapG addr nat Σ}.
  Context {hD1Lease:  gen_heapG addr nat Σ}.
  Context {hSync: gen_heapG addr addr_status Σ}.

  Notation "l l0↦{ q } v " := (mapsto (hG := hD0Lease) l q v)
    (at level 20, q at level 50, format "l  l0↦{ q }  v") : bi_scope.
  Notation "l l0↦ v " :=
    (mapsto (hG := hD0Lease) l 1 v)
    (at level 20) : bi_scope.
  Notation "l l1↦{ q } v " := (mapsto (hG := hD1Lease) l q v)
    (at level 20, q at level 50, format "l  l1↦{ q }  v ") : bi_scope.
  Notation "l l1↦ v " :=
    (mapsto (hG := hD1Lease) l 1 v)
    (at level 20) : bi_scope.

  Notation "l s↦{ q } v " := (mapsto (hG := hSync) l q v)
    (at level 20, q at level 50, format "l  s↦{ q }  v") : bi_scope.

  Definition LockInv (a: addr) :=
    (∃ v, a l0↦{1/2} v ∗ a l1↦{1/2} v ∗ a s↦{1/2} Sync)%I.

  Definition UnlockedInv (a: addr) :=
    (∃ v0 v1 vstat, a l0↦{1/2} v0 ∗ a l1↦{1/2} v1 ∗ a s↦{1/2} vstat)%I.

  Definition status_interp (a: addr) v0 v1 (s: addr_status) :=
    (match s with
     | Sync => ⌜ v0 = v1 ⌝
     | Unsync j K => j ⤇ K (Call (OneDisk.Write_Disk a v0)) ∗ Registered
     end)%I.

  Global Instance status_interp_timeless a v0 v1 s:
    Timeless (status_interp a v0 v1 s).
  Proof. destruct s; apply _. Qed.

  Definition DurInv (a: addr) v1 :=
    (∃ v0 stat, a d0↦ v0 ∗ a d1↦ v1 ∗ a l0↦{1/2} v0 ∗ a l1↦{1/2} v1 ∗ a s↦{1/2} stat
                  ∗ status_interp a v0 v1 stat)%I.

  Definition DurInvSync (a: addr) v1 :=
    (a d0↦ v1 ∗ a d1↦ v1 ∗ a l0↦{1/2} v1 ∗ a l1↦{1/2} v1 ∗ a s↦{1/2} Sync)%I.

  Definition durN : namespace := (nroot.@"dur_inv").
  Definition lockN : namespace := (nroot.@"lock_inv").

  Definition addrset := dom (gset nat) init_zero.
  Opaque init_zero size.

  Definition DisksInv :=
    (∃ σ : OneDisk.State, ⌜ dom (gset _) (OneDisk.disk_state σ) = addrset ⌝ ∗ source_state σ
       ∗ gen_heap_ctx' (hG := hD0Lease)
       ∗ gen_heap_ctx' (hG := hD1Lease)
       ∗ gen_heap_ctx' (hG := hSync)
       ∗ [∗ map] a↦v1 ∈ OneDisk.disk_state σ, DurInv a v1)%I.

  Definition ExecInv :=
    (source_ctx ∗ ([∗ set] a ∈ addrset, ∃ γ, is_lock lockN γ a (LockInv a)) ∗ inv durN DisksInv)%I.

  Definition ExecInner :=
    (([∗ set] a ∈ addrset, a m↦0 ∗ LockInv a) ∗ DisksInv)%I.

  Definition CrashInv :=
    (source_ctx ∗ inv durN DisksInv)%I.

  Definition CrashStarter := ([∗ set] a ∈ addrset, a m↦0 ∗ UnlockedInv a)%I.

  Definition CrashInner :=
    (CrashInv ∗ CrashStarter)%I.

  Global Instance addr_status_inhabited :
    Inhabited (addr_status).
  Proof. econstructor. exact Sync. Qed.

  Global Instance odstate_inhaibted:
    Inhabited (OneDisk.State).
  Proof. econstructor. exact {| OneDisk.disk_state := init_zero |}. Qed.


  Lemma not_lt_size_not_in_addrset a:
    ¬ a < size → a ∉ addrset.
  Proof. intros. apply not_elem_of_dom, init_zero_lookup_ge_None; lia. Qed.

  Lemma lt_size_in_addrset a:
    a < size → a ∈ addrset.
  Proof. intros. apply elem_of_dom. eexists. apply init_zero_lookup_lt_zero; lia. Qed.

  Opaque addrset.

  Set Nested Proofs Allowed.
  Lemma upd_disk_dom a v σ:
    dom (gset nat) (OneDisk.upd_disk a v σ).(OneDisk.disk_state) =
    dom (gset nat) σ.(OneDisk.disk_state).
  Proof.
    rewrite /OneDisk.upd_disk//=/OneDisk.upd_default//=.
    destruct (_ !! a) as [?|] eqn:Hlookup.
    - rewrite dom_insert_L.
      assert (a ∈ dom (gset nat) σ.(OneDisk.disk_state)).
      { apply elem_of_dom; eauto. }
      set_solver.
    - auto.
  Qed.

  Lemma write_refinement {T} j K `{LanguageCtx OneDisk.Op unit T OneDisk.l K} a v:
    {{{ j ⤇ K (Call (OneDisk.Write_Disk a v)) ∗ Registered ∗ ExecInv }}}
      write a v
    {{{ v, RET v; j ⤇ K (Ret v) ∗ Registered }}}.
  Proof.
    iIntros (Φ) "(Hj&Hreg&(#Hsrc&#Hlocks&#Hinv)) HΦ".
    rewrite /write. destruct lt_dec as [Hlt|Hnlt]; last first.
    {
      iApply wp_bind_proc_subst.
      iInv "Hinv" as "H".
      iDestruct "H" as (σ) "(>Hdom1&>Hstate&?)".
      iDestruct "Hdom1" as %Hdom1.
      iMod (ghost_step_call with "Hj Hsrc [$]") as "(Hj&Hstate&_)".
      { intros. do 2 eexists; split; last econstructor.
        split; auto.
        econstructor.
      }
      { solve_ndisj. }
      wp_ret.
      assert ((OneDisk.upd_disk a v σ) = σ) as ->.
      {  destruct σ as [d].
         rewrite /OneDisk.upd_disk. f_equal.
         rewrite /OneDisk.upd_default.
         pose proof (not_lt_size_not_in_addrset a Hnlt) as Hdom.
         rewrite -Hdom1 not_elem_of_dom in Hdom * => ->.
         eauto.
      }
      iExists _. iFrame. iSplitL "".
      { iModIntro. iNext. iPureIntro. auto. }
      iModIntro. iNext. wp_ret. clear. iApply "HΦ". iFrame.
    }
    wp_bind. apply lt_size_in_addrset in Hlt.
    iDestruct (big_sepS_elem_of with "Hlocks") as "Hlock"; first eauto.
    iDestruct "Hlock" as (γ) "Hlock".
    iApply (wp_lock with "[$]").
    iIntros "!> (Hlocked&Hlockinv)".
    wp_bind. iDestruct "Hlockinv" as (v') "(Hl0&Hl1&Hstatus)".
    iInv "Hinv" as "H".
    iDestruct "H" as (σ) "(>Hdom1&>Hstate&Hctx0&Hctx1&Hctx_stat&>Hdur)".
    iDestruct "Hdom1" as %Hdom1.
    generalize Hlt => Hdom2.
    rewrite -Hdom1 in Hdom2.
    rewrite elem_of_dom in Hdom2 *. intros [v1 Hlookup].
    iDestruct (big_sepM_lookup_acc with "Hdur") as "(Hcurr&Hdur)"; first eauto.
    iDestruct "Hcurr" as (v0 stat) "(Hd0&Hd1&Hl0_auth&Hl1_auth&Hstatus_auth&Hstat)".
    iDestruct (mapsto_agree with "Hl0 Hl0_auth") as %Heq; subst.
    iDestruct (mapsto_agree with "Hl1 Hl1_auth") as %Heq; subst.
    iDestruct (mapsto_agree with "Hstatus Hstatus_auth") as %Heq; subst.
    iDestruct "Hstat" as %Heq; subst.
    iApply (wp_write_disk0 with "[$]").
    iIntros "!> Hd0".
    iMod (gen_heap_update' _ _ v with "Hctx0 [Hl0 Hl0_auth]") as "(?&Hl0)".
    { iCombine "Hl0 Hl0_auth" as "$". }
    iDestruct "Hl0" as "(Hl0&Hl0_auth)".
    iMod (gen_heap_update' _ _ (Unsync j K) with "[$] [Hstatus Hstatus_auth]") as "(?&Hstatus)".
    { iCombine "Hstatus Hstatus_auth" as "$". }
    iDestruct "Hstatus" as "(Hstatus&Hstatus_auth)".
    iExists _. iFrame.
    iSplitL "Hdur Hd0 Hd1 Hl0_auth Hl1_auth Hstatus_auth Hj Hreg".
    { iSplitL ""; first by iPureIntro.
      iApply "Hdur". iExists _, _. iFrame.
      iFrame. clear. iClear "Hlocks". auto. }
    iModIntro. wp_bind.

    iInv "Hinv" as "H".
    clear σ Hdom1 Hlookup Heq.
    iDestruct "H" as (σ) "(>Hdom1&>Hstate&Hctx0&Hctx1&Hctx_stat&>Hdur)".
    iDestruct "Hdom1" as %Hdom1.
    generalize Hlt => Hdom2.
    rewrite -Hdom1 in Hdom2.
    rewrite elem_of_dom in Hdom2 *. intros [v1' Hlookup].
    iDestruct (big_sepM_insert_acc with "Hdur") as "(Hcurr&Hdur)"; first eauto.
    iDestruct "Hcurr" as (? ?) "(Hd0&Hd1&Hl0_auth&Hl1_auth&Hstatus_auth&Hstat)".
    iDestruct (mapsto_agree with "Hl0 Hl0_auth") as %<-; subst.
    iDestruct (mapsto_agree with "Hl1 Hl1_auth") as %Heq; subst.
    iDestruct (mapsto_agree with "Hstatus Hstatus_auth") as %Heq; subst.
    iApply (wp_write_disk1 with "[$]").
    iIntros "!> Hd1".
    iMod (gen_heap_update' _ _ v with "[$] [Hl1 Hl1_auth]") as "(?&Hl1)".
    { iCombine "Hl1 Hl1_auth" as "$". }
    iDestruct "Hl1" as "(Hl1&Hl1_auth)".
    iMod (gen_heap_update' _ _ Sync with "[$] [Hstatus Hstatus_auth]") as "(?&Hstatus)".
    { iCombine "Hstatus Hstatus_auth" as "$". }
    iDestruct "Hstatus" as "(Hstatus&Hstatus_auth)".
    iDestruct "Hstat" as "(Hj&Hreg)".
    iMod (ghost_step_call with "Hj Hsrc [$]") as "(Hj&Hstate&_)".
    { intros. do 2 eexists; split; last econstructor.
      split; auto.
      econstructor.
    }
    { solve_ndisj. }
    iExists _. iFrame.

    rewrite upd_disk_dom.
    iSplitL "Hdur Hd0 Hd1 Hl0_auth Hl1_auth Hstatus_auth".
    { iSplitL ""; first by iPureIntro.
      iModIntro. iNext.
      rewrite /OneDisk.upd_disk/OneDisk.upd_default /= Hlookup.
      iApply "Hdur". iExists _, _. iFrame.
      iFrame. clear. iClear "Hlocks". auto. }

    iApply (wp_unlock with "[Hl0 Hl1 Hstatus Hlocked]").
    { iFrame "Hlock". iFrame. iExists _; iFrame. }
    iIntros "!> _". iApply "HΦ". iFrame.
  Qed.

  Lemma read_refinement {T} j K `{LanguageCtx OneDisk.Op nat T OneDisk.l K} a:
    {{{ j ⤇ K (Call (OneDisk.Read_Disk a)) ∗ Registered ∗ ExecInv }}}
      read a
    {{{ v, RET v; j ⤇ K (Ret v) ∗ Registered }}}.
  Proof.
    iIntros (Φ) "(Hj&Hreg&(#Hsrc&#Hlocks&#Hinv)) HΦ".
    rewrite /read. destruct lt_dec as [Hlt|Hnlt]; last first.
    {
      iApply wp_bind_proc_subst.
      iInv "Hinv" as "H".
      iDestruct "H" as (σ) "(>Hdom1&>Hstate&?)".
      iDestruct "Hdom1" as %Hdom1.
      iMod (ghost_step_call with "Hj Hsrc [$]") as "(Hj&Hstate&_)".
      { intros. do 2 eexists; split; last econstructor.
        split; auto.
        econstructor.
      }
      { solve_ndisj. }
      wp_ret.
      assert ((OneDisk.lookup_disk a σ) = 0) as ->.
      {  destruct σ as [d].
         rewrite /OneDisk.lookup_disk/OneDisk.lookup_default.
         pose proof (not_lt_size_not_in_addrset a Hnlt) as Hdom.
         rewrite -Hdom1 not_elem_of_dom in Hdom * => ->.
         eauto.
      }
      iExists _. iFrame. iSplitL "".
      { iModIntro. iNext. iPureIntro. auto. }
      iModIntro. iNext. wp_ret. clear. iApply "HΦ". iFrame.
    }
    wp_bind. apply lt_size_in_addrset in Hlt.
    iDestruct (big_sepS_elem_of with "Hlocks") as "Hlock"; first eauto.
    iDestruct "Hlock" as (γ) "Hlock".
    iApply (wp_lock with "[$]").
    iIntros "!> (Hlocked&Hlockinv)".
    wp_bind. iDestruct "Hlockinv" as (v') "(Hl0&Hl1&Hstatus)".
    wp_bind.
    iInv "Hinv" as "H".
    iDestruct "H" as (σ) "(>Hdom1&>Hstate&Hctx0&Hctx1&Hctx_stat&>Hdur)".
    iDestruct "Hdom1" as %Hdom1.
    generalize Hlt => Hdom2.
    rewrite -Hdom1 in Hdom2.
    rewrite elem_of_dom in Hdom2 *. intros [v1 Hlookup].
    iDestruct (big_sepM_lookup_acc with "Hdur") as "(Hcurr&Hdur)"; first eauto.
    iDestruct "Hcurr" as (v0 stat) "(Hd0&Hd1&Hl0_auth&Hl1_auth&Hstatus_auth&Hstat)".
    iDestruct (mapsto_agree with "Hl0 Hl0_auth") as %Heq; subst.
    iDestruct (mapsto_agree with "Hl1 Hl1_auth") as %Heq; subst.
    iDestruct (mapsto_agree with "Hstatus Hstatus_auth") as %Heq; subst.
    iDestruct "Hstat" as %Heq; subst.
    iApply (wp_read_disk0 with "[$]").
    iIntros (mv) "!> (Hd0&Hret)".
    destruct mv as [v|].
    - (* We read a value from disk 0, so this was the linearization point. *)
      iMod (ghost_step_call with "Hj Hsrc [$]") as "(Hj&Hstate&_)".
      { intros. do 2 eexists; split; last econstructor.
        split; auto.
        econstructor.
      }
      { solve_ndisj. }
      iDestruct "Hret" as %Heq'; subst.
      iExists _. iFrame.
      iSplitL "Hdur Hd0 Hd1 Hl0_auth Hl1_auth Hstatus_auth".
      { iSplitL ""; first by iPureIntro.
        iApply "Hdur". iExists _, _. iFrame.
        iFrame. clear. iClear "Hlocks". auto. }
      iModIntro.
      wp_ret.
      wp_bind.
      iApply (wp_unlock with "[Hl0 Hl1 Hstatus Hlocked]").
      { iFrame "Hlock". iFrame. iExists _; iFrame. }
      iIntros "!> _". wp_ret. iApply "HΦ". iFrame.
      assert ((OneDisk.lookup_disk a σ) = v) as ->.
      {  destruct σ as [d].
         rewrite /OneDisk.lookup_disk/OneDisk.lookup_default.
         by rewrite Hlookup.
      }
      iFrame.
    - (* Disk0 read failed, but that means we know the read from Disk1 must succeed *)
      iExists _. iFrame.
      iSplitL "Hdur Hd0 Hd1 Hl0_auth Hl1_auth Hstatus_auth".
      { iSplitL ""; first by iPureIntro.
        iApply "Hdur". iExists _, _. iFrame.
        iFrame. clear. iClear "Hlocks". auto. }
      iModIntro.
      wp_bind.
      iInv "Hinv" as "H".
      clear σ Hdom1 Hlookup Heq.
      iDestruct "H" as (σ) "(>Hdom1&>Hstate&Hctx0&Hctx1&Hctx_stat&>Hdur)".
      iDestruct "Hdom1" as %Hdom1.
      generalize Hlt => Hdom2.
      rewrite -Hdom1 in Hdom2.
      rewrite elem_of_dom in Hdom2 *. intros [v1' Hlookup].
      iDestruct (big_sepM_lookup_acc with "Hdur") as "(Hcurr&Hdur)"; first eauto.
      iDestruct "Hcurr" as (v0 stat) "(Hd0&Hd1&Hl0_auth&Hl1_auth&Hstatus_auth&Hstat)".
      iDestruct (mapsto_agree with "Hl0 Hl0_auth") as %Heq; subst.
      iDestruct (mapsto_agree with "Hl1 Hl1_auth") as %Heq; subst.
      iDestruct (mapsto_agree with "Hstatus Hstatus_auth") as %Heq; subst.
      iDestruct "Hstat" as %Heq; subst.
      iApply (wp_read_disk1_only1 with "[$]").
      iIntros "!> Hd1".
      iMod (ghost_step_call with "Hj Hsrc [$]") as "(Hj&Hstate&_)".
      { intros. do 2 eexists; split; last econstructor.
        split; auto.
        econstructor.
      }
      { solve_ndisj. }
      iExists _. iFrame.
      iSplitL "Hdur Hd0 Hd1 Hl0_auth Hl1_auth Hstatus_auth".
      { iSplitL ""; first by iPureIntro.
        iApply "Hdur". iExists _, _. iFrame.
        iFrame. clear. iClear "Hlocks". auto. }
      iModIntro.
      wp_ret.
      wp_bind.
      iApply (wp_unlock with "[Hl0 Hl1 Hstatus Hlocked]").
      { iFrame "Hlock". iFrame. iExists _; iFrame. }
      iIntros "!> _". wp_ret. iApply "HΦ". iFrame.
      assert ((OneDisk.lookup_disk a σ) = v1') as ->.
      {  destruct σ as [d].
         rewrite /OneDisk.lookup_disk/OneDisk.lookup_default.
           by rewrite Hlookup.
      }
      iFrame.
  Qed.

End refinement_triples.

Definition myΣ : gFunctors := #[exmachΣ; @cfgΣ OneDisk.Op OneDisk.l;
                                  lockΣ; gen_heapΣ addr addr_status].

Existing Instance subG_cfgPreG.

Definition init_absr σ1a σ1c :=
  TwoDisk.l.(initP) σ1c ∧ OneDisk.l.(initP) σ1a.

Opaque size.

Lemma exmach_crash_refinement_seq {T} σ1c σ1a (es: proc_seq OneDisk.Op T) :
  init_absr σ1a σ1c →
  wf_client_seq es →
  ¬ proc_exec_seq OneDisk.l es (rec_singleton (Ret ())) (1, σ1a) Err →
  ∀ σ2c res, proc_exec_seq TwoDisk.l (compile_proc_seq ReplicatedDiskImpl.impl es)
                                      (rec_singleton recv) (1, σ1c) (Val σ2c res) →
  ∃ σ2a, proc_exec_seq OneDisk.l es (rec_singleton (Ret tt)) (1, σ1a) (Val σ2a res).
Proof.
  eapply (exmach_crash_refinement_seq) with
      (Σ := myΣ)
      (exec_inv := fun H1 H2 => (∃ hL0 hL1 hS, @ExecInv myΣ H2 _ H1 hL0 hL1 hS)%I)
      (exec_inner := fun H1 H2 => (∃ hL0 hL1 hS, @ExecInner myΣ H2 H1 hL0 hL1 hS)%I)
      (crash_inner := fun H1 H2 => (∃ hL0 hL1 hS , @CrashInner myΣ H2 H1 hL0 hL1 hS)%I)
      (*
      (crash_param := fun H1 H2 => unit)
       *)
      (crash_inv := fun H1 H2 ghosts =>
                      let '(hL0, hL1, hS) := ghosts in
                      @CrashInv myΣ H2 H1 hL0 hL1 hS)
      (crash_starter := fun H1 H2 ghosts =>
                      let '(hL0, hL1, hS) := ghosts in
                     (@CrashStarter myΣ H2 hL0 hL1 hS))
      (E := nclose sourceN).
  { apply _. }
  { apply _. }
  { intros. apply _. }
  { intros ?? ((?&?)&?). apply _. }
  { set_solver+. }
  { intros. iIntros "(Hj&Hreg&H)". iDestruct "H" as (???) "H". destruct op.
    - iApply (@read_refinement with "[$]"). eauto.
    - iApply (@write_refinement with "[$]"). eauto.
  }
  { intros. iIntros "H". iDestruct "H" as (???) "(?&?)". eauto. }
  {
    (* recv triple *)
    intros ? ? ((hL0&hL1)&hS). iIntros "(H&Hreg&Hstarter)". iDestruct "H" as "(#Hctx&#Hinv)".
    rewrite /recv.
    iAssert (([∗ set] a ∈ addrset,
              if lt_dec a size then
                a m↦0 ∗ @UnlockedInv _ hL0 hL1 hS a
              else
                a m↦0 ∗ @LockInv _ hL0 hL1 hS a))%I with "[Hstarter]" as "Hprogress".
    { iApply (big_sepS_mono with "Hstarter").
      iIntros (a Hin) "Hunlcoked".
      destruct lt_dec; first iFrame.
      exfalso. eapply not_lt_size_not_in_addrset; eauto.
    }
    iInduction size as [| n] "IH".
    - wp_ret.
      iInv "Hinv" as ">H" "_".
      iDestruct "H" as (σ) "(Hdom1&Hstate&Hctx0&Hctx1&Hctx_stat&Hdur)".
      iDestruct "Hdom1" as %Hdom1.
      iApply fupd_mask_weaken.
      { solve_ndisj. }
      iAssert ([∗ map] a↦v1 ∈ σ.(OneDisk.disk_state), @DurInvSync _ _ hL0 hL1 hS a v1
                                                      ∗ (a m↦ 0 ∗ @LockInv _ hL0 hL1 hS a))%I
        with "[Hprogress Hdur]" as "Hprogress".
      {
        rewrite -Hdom1. iDestruct (big_sepM_dom with "Hprogress") as "H".
        iDestruct (big_sepM_sepM with "[H Hdur]") as "H".
        { iFrame. }
        iApply (big_sepM_mono with "H").
        iIntros (a v Hlookup) "(Hd&(?&Hl))".
        iDestruct "Hl" as (v') "(Hl0&Hl1&Hstatus)".
        iDestruct "Hd" as (v0 stat) "(Hd0&Hd1&Hl0_auth&Hl1_auth&Hstatus_auth&Hstat)".
        iDestruct (mapsto_agree with "Hl0 Hl0_auth") as %Heq; subst.
        iDestruct (mapsto_agree with "Hl1 Hl1_auth") as %Heq; subst.
        iDestruct (mapsto_agree with "Hstatus Hstatus_auth") as %Heq; subst.
        iFrame. iExists _. iFrame.
      }
      iExists _, _. iFrame.
      iSplitL "".
      { iPureIntro. econstructor. }
      iClear "Hctx".
      iIntros (???) "(Hctx&Hstate)".
      iDestruct (big_sepM_sepM with "Hprogress") as "(Hdur&Hprogress)".
      iDestruct (big_sepM_dom with "Hprogress") as "Hprogress".
      rewrite Hdom1.
      iModIntro. iExists hL0, hL1, hS. iFrame.
      iExists _; iFrame. eauto.
      iSplitL ""; auto.
      iApply (big_sepM_mono with "Hdur").
      iIntros (a' v' Hlookup) "(?&?&?&?&?)".
      iExists _, Sync. iFrame.
      auto.
    - wp_bind. wp_bind.
Abort.