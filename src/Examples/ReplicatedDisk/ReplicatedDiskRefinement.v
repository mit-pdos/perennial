From iris.algebra Require Import auth gmap list.
Require Export CSL.Refinement CSL.NamedDestruct CSL.BigDynOp.
Require Import OneDiskAPI ReplicatedDiskImpl ReplicatedDisk.WeakestPre ReplicatedDisk.RefinementAdequacy.
Set Default Proof Using "All".
Unset Implicit Arguments.

Import agree.
From Tactical Require Import UnfoldLemma.

Definition addrset := dom (gset nat) init_zero.
Opaque init_zero size.


(* TODO: move out and re-use this *)
Section gen_heap.
Context `{hG: gen_heapG L V Σ}.
Lemma gen_heap_init_to_bigOp σ:
  own (gen_heap_name hG) (◯ to_gen_heap σ)
      -∗ [∗ map] i↦v ∈ σ, mapsto i 1 v .
Proof.
  induction σ using map_ind.
  - iIntros. rewrite //=.
  - iIntros "Hown".
    rewrite big_opM_insert //.
    iAssert (own (gen_heap_name hG) (◯ to_gen_heap m) ∗ (mapsto i 1 x))%I
      with "[Hown]" as "[Hrest $]".
    {
      rewrite mapsto_eq /mapsto_def //.
      rewrite to_gen_heap_insert.
      rewrite (insert_singleton_op (to_gen_heap m) i (1%Qp, to_agree x));
        last by apply lookup_to_gen_heap_None.
      rewrite auth_frag_op. iDestruct "Hown" as "(?&?)". iFrame.
    }
    by iApply IHσ.
Qed.

Lemma gen_heap_bigOpM_dom (σ: gmap L V) (q: Qp):
  ([∗ map] i↦v ∈ σ, mapsto i q v)
    -∗ [∗ set] i ∈ dom (gset L) σ, ∃ v, ⌜ σ !! i = Some v ⌝ ∗ mapsto i q v .
Proof.
  iIntros "H". iApply big_sepM_dom.
  iApply (big_sepM_mono with "H").
  iIntros (k x Hlookup) "H".
  iExists _. iFrame. eauto.
Qed.

Lemma gen_heap_bigOp_split (σ: gmap L V) (q: Qp):
  ([∗ map] i↦v ∈ σ, mapsto i q v)
    -∗ ([∗ map] i↦v ∈ σ, mapsto i (q/2) v) ∗ ([∗ map] i↦v ∈ σ, mapsto i (q/2) v).
Proof.
  rewrite -big_sepM_sep. apply big_sepM_mono.
  iIntros (?? ?) "($&$)".
Qed.
End gen_heap.

Definition gen_heap_ctx' {Σ V} {hG: gen_heapG nat V Σ}
  := (∃ σ : gmap nat V, ⌜ dom (gset nat) σ = addrset ⌝ ∗ gen_heap_ctx σ)%I.
Lemma gen_heap_update' {Σ V} {hG: gen_heapG nat V Σ} (l: nat) v1 v2:
    gen_heap_ctx' -∗ mapsto l 1 v1 ==∗ gen_heap_ctx' ∗ mapsto l 1 v2.
Proof.
  iIntros "Hctx Hmapsto". iDestruct "Hctx" as (σ Hdom) "H".
  iDestruct (@gen_heap_valid with "[$] [$]") as %Hlookup.
  iMod (@gen_heap_update with "[$] [$]") as "(?&$)".
  iExists _; iFrame.
  iPureIntro. rewrite dom_insert_L -Hdom.
  cut (l ∈ dom (gset nat) σ).
  { set_solver+. }
  apply elem_of_dom. eauto.
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

  Definition status_interp (a: addr) v0 v1 (s: addr_status) P :=
    (match s with
     | Sync => ⌜ v0 = v1 ⌝
     | Unsync j K => j ⤇ K (Call (OneDisk.Write_Disk a v0)) ∗ P
     end)%I.

  Global Instance status_interp_timeless a v0 v1 s P:
    Timeless P →
    Timeless (status_interp a v0 v1 s P).
  Proof. destruct s; apply _. Qed.

  Definition DurInv (a: addr) v1 P :=
    (∃ v0 stat, a d0↦ v0 ∗ a d1↦ v1 ∗ a l0↦{1/2} v0 ∗ a l1↦{1/2} v1 ∗ a s↦{1/2} stat
                  ∗ status_interp a v0 v1 stat P)%I.

  Definition DurInvSync (a: addr) v1 :=
    (a d0↦ v1 ∗ a d1↦ v1 ∗ a l0↦{1/2} v1 ∗ a l1↦{1/2} v1 ∗ a s↦{1/2} Sync)%I.

  Definition durN : namespace := (nroot.@"dur_inv").
  Definition lockN : namespace := (nroot.@"lock_inv").

  Definition DisksInv P :=
    (∃ σ : OneDisk.State, ⌜ dom (gset _) (OneDisk.disk_state σ) = addrset ⌝ ∗ source_state σ
       ∗ gen_heap_ctx' (hG := hD0Lease)
       ∗ gen_heap_ctx' (hG := hD1Lease)
       ∗ gen_heap_ctx' (hG := hSync)
       ∗ [∗ map] a↦v1 ∈ OneDisk.disk_state σ, DurInv a v1 P)%I.

  Definition ExecInv :=
    (source_ctx ∗ ([∗ set] a ∈ addrset, ∃ γ, is_lock lockN γ a (LockInv a))
                ∗ inv durN (DisksInv Registered))%I.

  Definition ExecInner :=
    (([∗ set] a ∈ addrset, a m↦0 ∗ LockInv a) ∗ (DisksInv Registered))%I.

  Definition CrashInv :=
    (source_ctx ∗ inv durN (DisksInv True))%I.

  Definition CrashStarter := ([∗ set] a ∈ addrset, a m↦0 ∗ UnlockedInv a)%I.

  Definition CrashInner :=
    ((source_ctx ∗ (DisksInv True)) ∗ CrashStarter)%I.

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
    iMod (gen_heap_update' (hG := hD0Lease) _ _ v with "Hctx0 [Hl0 Hl0_auth]") as "(?&Hl0)".
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

Lemma init_zero_lookup_is_zero k x:
  init_zero !! k = Some x → x = 0.
Proof.
  destruct (lt_dec k size).
  - rewrite init_zero_lookup_lt_zero; congruence.
  - rewrite init_zero_lookup_ge_None; congruence.
Qed.

Module repRT <: twodisk_refinement_type.

Definition Σ : gFunctors := #[exmachΣ; @cfgΣ OneDisk.Op OneDisk.l;
                                  lockΣ; gen_heapΣ addr addr_status].

Existing Instance subG_cfgPreG.

Definition init_absr σ1a σ1c :=
  TwoDisk.l.(initP) σ1c ∧ OneDisk.l.(initP) σ1a.

Opaque size.

  Definition OpT := OneDisk.Op.
  Definition Λa := OneDisk.l.

  Definition impl := ReplicatedDiskImpl.impl.
  Import TwoDisk.

  Instance from_exist_left_sep' {Σ} {A} (Φ : A → iProp Σ) Q :
    FromExist ((∃ a, Φ a) ∗ Q) (λ a, Φ a ∗ Q)%I .
  Proof. rewrite /FromExist. iIntros "H". iDestruct "H" as (?) "(?&$)". iExists _; eauto. Qed.

  Instance CFG : @cfgPreG OneDisk.Op OneDisk.l Σ. apply _. Qed.
  Instance HEX : ReplicatedDisk.RefinementAdequacy.exmachPreG Σ. apply _. Qed.
  Instance INV : Adequacy.invPreG Σ. apply _. Qed.
  Instance REG : inG Σ (csumR countingR (authR (optionUR (exclR unitC)))). apply _. Qed.

  Global Instance inst_inG1: lockG Σ.
  Proof. apply _. Qed.

  Definition exec_inv := fun H1 H2 => (∃ hL0 hL1 hS, @ExecInv Σ H2 _ H1 hL0 hL1 hS)%I.
  Definition exec_inner := fun H1 H2 => (∃ hL0 hL1 hS, @ExecInner Σ H2 H1 hL0 hL1 hS)%I.
  Definition crash_inner := fun H1 H2 => (∃ hL0 hL1 hS , @CrashInner Σ H2 H1 hL0 hL1 hS)%I.
  Definition crash_inv := fun H1 H2 ghosts =>
                      let '(hL0, hL1, hS) := ghosts in
                      @CrashInv Σ H2 H1 hL0 hL1 hS.
  Definition crash_param := fun (_ : @cfgG OpT Λa Σ) (_ : exmachG Σ) =>
    (gen_heapG addr nat Σ * gen_heapG addr nat Σ * gen_heapG addr addr_status Σ)%type.
  Definition crash_starter :=
    fun (H1: @cfgG OpT Λa Σ) (H2: exmachG Σ) ghosts => let '(hL0, hL1, hS) := ghosts in
                                     (@CrashStarter Σ H2 hL0 hL1 hS).
  Definition E := nclose sourceN.
  Definition recv := recv.
End repRT.

Module repRD := twodisk_refinement_definitions repRT.

Module repRO : twodisk_refinement_obligations repRT.

  Module eRD := repRD.
  Import repRT repRD.

  Lemma einv_persist: forall {H1 : @cfgG OpT Λa Σ} {H2 : _},
      Persistent (exec_inv H1 H2).
  Proof. apply _. Qed.

  Lemma cinv_persist: forall {H1 : @cfgG OpT Λa Σ} {H2 : _} P,
      Persistent (crash_inv H1 H2 P).
  Proof. intros ?? ((?&?)&?). apply _. Qed.

  Lemma nameIncl: nclose sourceN ⊆ E.
  Proof. solve_ndisj. Qed.

  Lemma recsingle: recover impl = rec_singleton recv.
  Proof. trivial. Qed.

  Lemma refinement_op_triples: refinement_op_triples_type.
  Proof.
    red. intros. iIntros "(Hj&Hreg&H)". iDestruct "H" as (???) "H". destruct op.
    - iApply (@read_refinement with "[$]"). eauto.
    - iApply (@write_refinement with "[$]"). eauto.
  Qed.

  Lemma exec_inv_source_ctx: ∀ {H1 H2}, exec_inv H1 H2 ⊢ source_ctx.
  Proof.
    red. intros. iIntros "H". iDestruct "H" as (???) "(?&?)". eauto.
  Qed.

  Lemma recv_triple: recv_triple_type.
  Proof.
    (* recv triple *)
    intros ? ? ((hL0&hL1)&hS). iIntros "(H&Hreg&Hstarter)". iDestruct "H" as "(#Hctx&#Hinv)".
    rewrite /recv.
    iAssert (([∗ set] a ∈ addrset,
              if lt_dec a size then
                a m↦0 ∗ @UnlockedInv _ hL0 hL1 hS a
              else
                a m↦0 ∗ @LockInv _ hL0 hL1 hS a))%I with "[Hstarter]" as "Hprogress".
    { iApply (big_sepS_mono with "Hstarter").
      iIntros (a Hin) "Hunlocked".
      destruct lt_dec; first iFrame.
      exfalso. eapply not_lt_size_not_in_addrset; eauto.
    }
    rewrite /ReplicatedDiskImpl.recv.
    assert (Hbound: size <= size) by lia.
    remember size as n eqn:Heqn. rewrite {2}Heqn in Hbound.
    clear Heqn.
    iInduction n as [| n] "IH".
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
        iDestruct (big_sepM_sep with "[H Hdur]") as "H".
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
      iDestruct (big_sepM_sep with "Hprogress") as "(Hdur&Hprogress)".
      iDestruct (big_sepM_dom with "Hprogress") as "Hprogress".
      rewrite Hdom1.
      iModIntro. iExists hL0, hL1, hS. iFrame.
      iExists _; iFrame. eauto.
      iSplitL ""; auto.
      iApply (big_sepM_mono with "Hdur").
      iIntros (a' v' Hlookup) "(?&?&?&?&?)".
      iExists _, Sync. iFrame.
      auto.
    - wp_bind.
      rewrite /fixup.
      unshelve (iApply (wp_bind (λ x, Bind x _))).
      { apply _. }
      assert (Hlt: n < size) by lia.
      assert (Hin: n ∈ addrset).
      { by apply lt_size_in_addrset. }
      iDestruct (big_sepS_delete with "Hprogress") as "(Hcurr&Hrest)"; first eauto.
      destruct lt_dec; last by lia.
      iDestruct "Hcurr" as "(Hmem&Hcurr)".
      iDestruct "Hcurr" as (v0 v1 ?) "(Hl0&Hl1&Hstatus)".

    iInv "Hinv" as "H".
    iDestruct "H" as (σ) "(>Hdom1&>Hstate&Hctx0&Hctx1&Hctx_stat&>Hdur)".
    iDestruct "Hdom1" as %Hdom1.
    generalize Hin => Hdom2.
    rewrite -Hdom1 in Hdom2.
    rewrite elem_of_dom in Hdom2 *. intros [v1' Hlookup].
    iDestruct (big_sepM_lookup_acc with "Hdur") as "(Hcurr&Hdur)"; first eauto.
    iDestruct "Hcurr" as (v0' stat) "(Hd0&Hd1&Hl0_auth&Hl1_auth&Hstatus_auth&Hstat)".
    iDestruct (mapsto_agree with "Hl0 Hl0_auth") as %Heq; subst.
    iDestruct (mapsto_agree with "Hl1 Hl1_auth") as %Heq; subst.
    iDestruct (mapsto_agree with "Hstatus Hstatus_auth") as %Heq; subst.
    iApply (wp_read_disk0 with "[$]").
    iIntros (mv) "!> (Hd0&Hret)".
    destruct mv as [v|].
    * iSplitL "Hstate Hctx0 Hctx1 Hctx_stat Hdur Hd0 Hd1 Hl0_auth Hl1_auth Hstatus_auth Hstat".
      { iExists _. iFrame. iSplitL ""; first by iPureIntro.
        iApply "Hdur". iExists _, _. by iFrame. }
      iModIntro. wp_bind. wp_ret.
      iInv "Hinv" as "H".
      clear σ Hdom1 Hlookup.
      iDestruct "H" as (σ) "(>Hdom1&>Hstate&Hctx0&Hctx1&Hctx_stat&>Hdur)".
      iDestruct "Hdom1" as %Hdom1.
      generalize Hin => Hdom2.
      rewrite -Hdom1 in Hdom2.
      rewrite elem_of_dom in Hdom2 *. intros [v1'' Hlookup].
      iDestruct (big_sepM_insert_acc with "Hdur") as "(Hcurr&Hdur)"; first eauto.
      iDestruct "Hcurr" as (v0'' stat') "(Hd0&Hd1&Hl0_auth&Hl1_auth&Hstatus_auth&Hstat)".
      iDestruct (mapsto_agree with "Hl0 Hl0_auth") as %Heq; subst.
      iDestruct (mapsto_agree with "Hl1 Hl1_auth") as %Heq; subst.
      iDestruct (mapsto_agree with "Hstatus Hstatus_auth") as %Heq; subst.
      iApply (wp_write_disk1 with "[$]").
      iDestruct "Hret" as %Heq; subst.
      iIntros "!> Hd1".
      iMod (gen_heap_update' _ _ v with "Hctx1 [Hl1 Hl1_auth]") as "(Hctx1&Hl1)".
      { iCombine "Hl1 Hl1_auth" as "$". }
      iDestruct "Hl1" as "(Hl1&Hl1_auth)".
      iMod (gen_heap_update' _ _ Sync with "Hctx_stat [Hstatus Hstatus_auth]") as "(Hctx_stat&Hstatus)".
      { iCombine "Hstatus Hstatus_auth" as "$". }
      iDestruct "Hstatus" as "(Hstatus&Hstatus_auth)".
      iSplitL "Hstate Hctx0 Hctx1 Hctx_stat Hdur Hd0 Hd1 Hl0_auth Hl1_auth Hstatus_auth Hstat".
      { destruct stat'.
        * iExists _. iFrame. iSplitL ""; first by iPureIntro.
          iSpecialize ("Hdur" $! v1'').
          rewrite insert_id; last auto.
          iApply "Hdur".
          iDestruct "Hstat" as %Heq; subst.
          iExists _, _. by iFrame.
        * iDestruct "Hstat" as "(Hj&Hreg')".
          iMod (ghost_step_call with "Hj [$] [$]") as "(Hj&Hstate&_)".
          { intros. do 2 eexists; split; last econstructor.
            split; auto.
            econstructor.
          }
          { solve_ndisj. }
          iExists _. iFrame. rewrite upd_disk_dom. iSplitL ""; first by iPureIntro.
          rewrite /OneDisk.upd_disk/OneDisk.upd_default Hlookup.
          iApply "Hdur".
          iExists _, _. by iFrame.
      }
      iModIntro. iApply ("IH" with "[] Hreg [Hrest Hl0 Hl1 Hstatus Hmem]").
      { iPureIntro. lia. }
      iApply big_sepS_delete; first eauto.
      iSplitR "Hrest".
      { destruct lt_dec; try lia; [].
        iFrame. iExists _. iFrame. }
      { iApply (big_sepS_mono with "Hrest").
        iIntros (x Hin') "H".
        assert (x ≠ n).
        { apply elem_of_difference in Hin' as (?&Hsingle). intros Heq; subst.
          apply Hsingle, elem_of_singleton; auto. }
        do 2 destruct (lt_dec); auto.
        { lia. }
        { iDestruct "H" as "($&H)". iDestruct "H" as (?) "(?&?&?)".
          iExists _, _, _. iFrame. }
      }
    * iSplitL "Hstate Hctx0 Hctx1 Hctx_stat Hdur Hd0 Hd1 Hl0_auth Hl1_auth Hstatus_auth Hstat".
      { iExists _. iFrame. iSplitL ""; first by iPureIntro.
        iApply "Hdur". iExists _, _. by iFrame. }
      iModIntro.
      iApply (wp_write_disk0_only1 _ _ (⊤ ∖ ↑durN)  n v0' v1').
      { trivial. }
      iInv "Hinv" as "H" "Hclo".
      clear σ Hdom1 Hlookup.
      iDestruct "H" as (σ) "(>Hdom1&>Hstate&>Hctx0&Hctx1&>Hctx_stat&>Hdur)".
      iDestruct "Hdom1" as %Hdom1.
      generalize Hin => Hdom2.
      rewrite -Hdom1 in Hdom2.
      rewrite elem_of_dom in Hdom2 *. intros [v1'' Hlookup].
      iDestruct (big_sepM_insert_acc with "Hdur") as "(Hcurr&Hdur)"; first eauto.
      iDestruct "Hcurr" as (v0'' stat') "(Hd0&Hd1&Hl0_auth&Hl1_auth&Hstatus_auth&Hstat)".
      iDestruct (mapsto_agree with "Hl0 Hl0_auth") as %Heq; subst.
      iDestruct (mapsto_agree with "Hl1 Hl1_auth") as %Heq; subst.
      iDestruct (mapsto_agree with "Hstatus Hstatus_auth") as %Heq; subst.
      iMod (gen_heap_update' (hG := hL0) _ _ v1'' with "Hctx0 [Hl0 Hl0_auth]") as "(Hctx0&Hl0)".
      { iCombine "Hl0 Hl0_auth" as "$". }
      iDestruct "Hl0" as "(Hl0&Hl0_auth)".
      iMod (gen_heap_update' _ _ Sync with "Hctx_stat [Hstatus Hstatus_auth]") as
          "(Hctx_stat&Hstatus)".
      { iCombine "Hstatus Hstatus_auth" as "$". }
      iDestruct "Hstatus" as "(Hstatus&Hstatus_auth)".
      iModIntro. iFrame.
      iIntros "Hd0".
      iMod ("Hclo" with "[Hstate Hctx0 Hctx1 Hctx_stat Hdur Hd0 Hd1 Hl0_auth Hl1_auth Hstatus_auth Hstat]").
      { destruct stat'.
        * iExists _. iFrame. iSplitL ""; first by iPureIntro.
          iSpecialize ("Hdur" $! v1'').
          rewrite insert_id; last auto.
          iApply "Hdur".
          iDestruct "Hstat" as %Heq; subst.
          iExists _, _. by iFrame.
        * iExists _. iFrame. iSplitL ""; first by iPureIntro.
          iSpecialize ("Hdur" $! v1'').
          rewrite insert_id; last auto.
          iApply "Hdur".
          iExists v1'', Sync. iFrame.
          rewrite /status_interp.
          auto.
      }
      wp_bind. wp_ret. wp_ret.
      iModIntro. iApply ("IH" with "[] Hreg [Hrest Hl0 Hl1 Hstatus Hmem]").
      { iPureIntro. lia. }
      iApply big_sepS_delete; first eauto.
      iSplitR "Hrest".
      { destruct lt_dec; try lia; [].
        iFrame. iExists _. iFrame. }
      { iApply (big_sepS_mono with "Hrest").
        iIntros (x Hin') "H".
        assert (x ≠ n).
        { apply elem_of_difference in Hin' as (?&Hsingle). intros Heq; subst.
          apply Hsingle, elem_of_singleton; auto. }
        do 2 destruct (lt_dec); auto.
        { lia. }
        { iDestruct "H" as "($&H)". iDestruct "H" as (?) "(?&?&?)".
          iExists _, _, _. iFrame. }
      }
  Qed.

  Lemma init_wf: ∀ σ1a σ1c, init_absr σ1a σ1c → σ1c = TwoDisk.init_state.
  Proof.
    intros ?? (H&?). by inversion H.
  Qed.

  Lemma init_exec_inner : init_exec_inner_type.
  Proof.
    intros ?? (H&Hinit) ??. inversion H. inversion Hinit. subst.
    iIntros "(Hmem&Hdisk0&Hdisk1&#?&Hstate)".
    iMod (gen_heap_strong_init init_zero) as (hL0 <-) "(hL0&hL0frag)".
    iPoseProof (gen_heap_init_to_bigOp (hG := hL0) with "hL0frag") as "hL0frag".
    iMod (gen_heap_strong_init init_zero) as (hL1 <-) "(hL1&hL1frag)".
    iPoseProof (gen_heap_init_to_bigOp (hG := hL1) with "hL1frag") as "hL1frag".
    iMod (gen_heap_strong_init ((λ x, Sync) <$> init_zero)) as (hS <-) "(hS&hSfrag)".
    iPoseProof (gen_heap_init_to_bigOp (hG := hS) with "hSfrag") as "hSfrag".
    iDestruct (gen_heap_bigOp_split with "hL0frag") as "(hL0a&hL0b)".
    iDestruct (gen_heap_bigOp_split with "hL1frag") as "(hL1a&hL1b)".
    iDestruct (gen_heap_bigOp_split with "hSfrag") as "(hSa&hSb)".
    rewrite big_opM_fmap.
    iExists hL0, hL1, hS.
    rewrite /ExecInner.
    iSplitL "Hmem hL0a hL1a hSa".
    { iModIntro. iApply big_opM_dom.
      repeat (iDestruct (@big_sepM_sep with "[$]") as "H").
      iApply (big_sepM_mono with "H").
      iIntros (k x Hlookup) "(((?&?)&?)&?)".
      rewrite (init_zero_lookup_is_zero k x); last auto.
      iFrame. iExists _. iFrame.
    }
    iExists _. iFrame "Hstate".
    iSplitL ""; first by auto.
    iSplitL "hL0".
    { iExists _. by iFrame. }
    iSplitL "hL1".
    { iExists _. by iFrame. }
    iSplitL "hS".
    { iExists _. iFrame "hS". rewrite dom_fmap_L. auto. }
    iModIntro.
    repeat (iDestruct (@big_sepM_sep with "[$]") as "H").
    iApply (big_sepM_mono with "H").
    iIntros (k x Hlookup) "((((?&?)&?)&?)&?)".
    rewrite (init_zero_lookup_is_zero k x); last auto.
    iFrame. iExists _, _. iFrame.
    auto.
  Qed.

  Lemma exec_inv_preserve_crash: exec_inv_preserve_crash_type.
  Proof.
    iIntros (??) "H".
    iDestruct "H" as (hL0 hL1 hS) "(#Hsrc&#Hlocks&#Hinv)".
    iInv "Hinv" as "H" "_".
    iDestruct "H" as (σ) "(>Hdom1&>Hstate&>Hctx0&>Hctx1&>Hctx_stat&>Hdur)".
    iDestruct "Hdom1" as %Hdom1.
    iApply fupd_mask_weaken; first by solve_ndisj.
    iIntros (??) "Hmem".
    iDestruct "Hctx0" as (σL0 HdomL0) "Hctx0".
    iMod (gen_heap_strong_init σL0) as (hL0' <-) "(hL0&hL0frag)".
    iPoseProof (gen_heap_init_to_bigOp (hG := hL0') with "hL0frag") as "hL0frag".

    iDestruct "Hctx1" as (σL1 HdomL1) "Hctx1".
    iMod (gen_heap_strong_init σL1) as (hL1' <-) "(hL1&hL1frag)".
    iPoseProof (gen_heap_init_to_bigOp (hG := hL1') with "hL1frag") as "hL1frag".

    iDestruct "Hctx_stat" as (σS HdomS) "Hctx_stat".
    iMod (gen_heap_strong_init σS) as (hS' <-) "(hS&hSfrag)".
    iPoseProof (gen_heap_init_to_bigOp (hG := hS') with "hSfrag") as "hSfrag".

    iDestruct (gen_heap_bigOp_split with "hL0frag") as "(hL0a&hL0b)".
    iDestruct (gen_heap_bigOp_split with "hL1frag") as "(hL1a&hL1b)".
    iDestruct (gen_heap_bigOp_split with "hSfrag") as "(hSa&hSb)".

    iDestruct (gen_heap_bigOpM_dom with "hL0a") as "hL0a".
    iDestruct (gen_heap_bigOpM_dom with "hL1a") as "hL1a".
    iDestruct (gen_heap_bigOpM_dom with "hSa") as "hSa".
    rewrite ?HdomL0 ?HdomL1 ?HdomS.
    iDestruct (big_sepM_dom with "hL0a") as "hL0a".
    iDestruct (big_sepM_dom with "hL1a") as "hL1a".
    iDestruct (big_sepM_dom with "hSa") as "hSa".

    iExists hL0', hL1', hS'. iModIntro.
    rewrite /CrashInner/CrashInv/CrashStarter.
    iFrame "Hsrc".
    iSplitR "Hmem hL0a hL1a hSa"; last first.
    { iApply big_opM_dom.
      repeat (iDestruct (@big_sepM_sep with "[$]") as "H").
      iApply (big_sepM_mono with "H").
      iIntros (k x Hlookup) "(((Hs&Hl0)&Hl1)&?)".
      iDestruct "Hs" as (??) "Hs".
      iDestruct "Hl0" as (??) "Hl0".
      iDestruct "Hl1" as (??) "Hl1".
      rewrite (init_zero_lookup_is_zero k x); last auto.
      iFrame. iExists _, _, _. iFrame.
    }
    iExists _. iFrame "Hstate".
    iDestruct (gen_heap_bigOpM_dom with "hL0b") as "hL0b".
    iDestruct (gen_heap_bigOpM_dom with "hL1b") as "hL1b".
    iDestruct (gen_heap_bigOpM_dom with "hSb") as "hSb".
    rewrite ?HdomL0 ?HdomL1 ?HdomS.
    rewrite -?Hdom1.
    iDestruct (big_sepM_dom with "hL0b") as "hL0b".
    iDestruct (big_sepM_dom with "hL1b") as "hL1b".
    iDestruct (big_sepM_dom with "hSb") as "hSb".
    iSplitL "".
    { iPureIntro. auto. }
    iSplitL "hL0".
    { iExists _. iFrame. by iPureIntro. }
    iSplitL "hL1".
    { iExists _. iFrame. by iPureIntro. }
    iSplitL "hS".
    { iExists _. iFrame. by iPureIntro. }
    repeat (iDestruct (@big_sepM_sep with "[$]") as "H").
    iCombine "Hctx0 Hctx1 Hctx_stat" as "Hctx".
    iDestruct (big_sepM_mono_with_inv with "Hctx H") as "(?&$)".
    iIntros (k x Hlookup) "H".
    iDestruct "H" as "((Hctx0&Hctx1&Hctx_stat)&H&Hdur)".
    iDestruct "H" as "((Hs&Hl0)&Hl1)".
    iDestruct "Hs" as (??) "Hs".
    iDestruct "Hl0" as (??) "Hl0".
    iDestruct "Hl1" as (??) "Hl1".
    iDestruct "Hdur" as (? stat) "(Hd0&Hd1&Hl0'&Hl1'&Hs'&Hstatus)".
    iDestruct (@gen_heap_valid with "Hctx0 Hl0'") as %?.
    iDestruct (@gen_heap_valid with "Hctx1 Hl1'") as %?.
    iDestruct (@gen_heap_valid with "Hctx_stat Hs'") as %?.
    repeat match goal with
           |[ H1 : ?x = Some ?y, H2 : ?x = Some ?z |- _ ] =>
            rewrite H1 in H2; inversion H2; clear H1 H2; subst
           end.
    iFrame. iExists _, _. iFrame.
    destruct stat; auto.
    iDestruct "Hstatus" as "(?&?)"; iFrame.
  Qed.

  Lemma crash_inv_preserve_crash: crash_inv_preserve_crash_type.
  Proof.
    iIntros (?? ((hL0&hL1)&hS)) "H".
    iDestruct "H" as "(#Hsrc&#Hinv)".
    iInv "Hinv" as "H" "_".
    iDestruct "H" as (σ) "(>Hdom1&>Hstate&>Hctx0&>Hctx1&>Hctx_stat&>Hdur)".
    iDestruct "Hdom1" as %Hdom1.
    iApply fupd_mask_weaken; first by solve_ndisj.
    iIntros (??) "Hmem".
    iDestruct "Hctx0" as (σL0 HdomL0) "Hctx0".
    iMod (gen_heap_strong_init σL0) as (hL0' <-) "(hL0&hL0frag)".
    iPoseProof (gen_heap_init_to_bigOp (hG := hL0') with "hL0frag") as "hL0frag".

    iDestruct "Hctx1" as (σL1 HdomL1) "Hctx1".
    iMod (gen_heap_strong_init σL1) as (hL1' <-) "(hL1&hL1frag)".
    iPoseProof (gen_heap_init_to_bigOp (hG := hL1') with "hL1frag") as "hL1frag".

    iDestruct "Hctx_stat" as (σS HdomS) "Hctx_stat".
    iMod (gen_heap_strong_init σS) as (hS' <-) "(hS&hSfrag)".
    iPoseProof (gen_heap_init_to_bigOp (hG := hS') with "hSfrag") as "hSfrag".

    iDestruct (gen_heap_bigOp_split with "hL0frag") as "(hL0a&hL0b)".
    iDestruct (gen_heap_bigOp_split with "hL1frag") as "(hL1a&hL1b)".
    iDestruct (gen_heap_bigOp_split with "hSfrag") as "(hSa&hSb)".

    iDestruct (gen_heap_bigOpM_dom with "hL0a") as "hL0a".
    iDestruct (gen_heap_bigOpM_dom with "hL1a") as "hL1a".
    iDestruct (gen_heap_bigOpM_dom with "hSa") as "hSa".
    rewrite ?HdomL0 ?HdomL1 ?HdomS.
    iDestruct (big_sepM_dom with "hL0a") as "hL0a".
    iDestruct (big_sepM_dom with "hL1a") as "hL1a".
    iDestruct (big_sepM_dom with "hSa") as "hSa".

    iExists hL0', hL1', hS'. iModIntro.
    rewrite /CrashInner/CrashInv/CrashStarter.
    iFrame "Hsrc".
    iSplitR "Hmem hL0a hL1a hSa"; last first.
    { iApply big_opM_dom.
      repeat (iDestruct (@big_sepM_sep with "[$]") as "H").
      iApply (big_sepM_mono with "H").
      iIntros (k x Hlookup) "(((Hs&Hl0)&Hl1)&?)".
      iDestruct "Hs" as (??) "Hs".
      iDestruct "Hl0" as (??) "Hl0".
      iDestruct "Hl1" as (??) "Hl1".
      rewrite (init_zero_lookup_is_zero k x); last auto.
      iFrame. iExists _, _, _. iFrame.
    }
    iExists _. iFrame "Hstate".
    iDestruct (gen_heap_bigOpM_dom with "hL0b") as "hL0b".
    iDestruct (gen_heap_bigOpM_dom with "hL1b") as "hL1b".
    iDestruct (gen_heap_bigOpM_dom with "hSb") as "hSb".
    rewrite ?HdomL0 ?HdomL1 ?HdomS.
    rewrite -?Hdom1.
    iDestruct (big_sepM_dom with "hL0b") as "hL0b".
    iDestruct (big_sepM_dom with "hL1b") as "hL1b".
    iDestruct (big_sepM_dom with "hSb") as "hSb".
    iSplitL "".
    { iPureIntro. auto. }
    iSplitL "hL0".
    { iExists _. iFrame. by iPureIntro. }
    iSplitL "hL1".
    { iExists _. iFrame. by iPureIntro. }
    iSplitL "hS".
    { iExists _. iFrame. by iPureIntro. }
    repeat (iDestruct (@big_sepM_sep with "[$]") as "H").
    iCombine "Hctx0 Hctx1 Hctx_stat" as "Hctx".
    iDestruct (big_sepM_mono_with_inv with "Hctx H") as "(?&$)".
    iIntros (k x Hlookup) "H".
    iDestruct "H" as "((Hctx0&Hctx1&Hctx_stat)&H&Hdur)".
    iDestruct "H" as "((Hs&Hl0)&Hl1)".
    iDestruct "Hs" as (??) "Hs".
    iDestruct "Hl0" as (??) "Hl0".
    iDestruct "Hl1" as (??) "Hl1".
    iDestruct "Hdur" as (? stat) "(Hd0&Hd1&Hl0'&Hl1'&Hs'&Hstatus)".
    iDestruct (@gen_heap_valid with "Hctx0 Hl0'") as %?.
    iDestruct (@gen_heap_valid with "Hctx1 Hl1'") as %?.
    iDestruct (@gen_heap_valid with "Hctx_stat Hs'") as %?.
    repeat match goal with
           |[ H1 : ?x = Some ?y, H2 : ?x = Some ?z |- _ ] =>
            rewrite H1 in H2; inversion H2; clear H1 H2; subst
           end.
    iFrame. iExists _, _. iFrame.
  Qed.

  Lemma crash_inner_inv : crash_inner_inv_type.
  Proof.
    red. iIntros (??) "(H&?)".
    iDestruct "H" as (hInv hL0 hL1 hS) "((_&Hinv)&?)".
    iExists (hL0, hL1, hS). iFrame.
    by iMod (@inv_alloc Σ (exm_invG) durN _ _ with "Hinv") as "$".
  Qed.

  Lemma exec_inner_inv : exec_inner_inv_type.
  Proof.
    iIntros (??) "(H&?)".
    iDestruct "H" as (hInv hL0 hL1 hS) "(Hlocks&Hdur)".
    iExists hL0, hL1, hS.
    iFrame. iSplitR "Hdur".
    - rewrite -fupd_big_sepS.
      iApply (big_sepS_mono with "Hlocks").
      iIntros (a Hin) "(Hmem&Hlock)".
      iApply (lock_init with "Hmem [Hlock]"); auto.
    - by iMod (@inv_alloc Σ (exm_invG) durN _ _ with "Hdur") as "$".
  Qed.

  Lemma exec_inv_preserve_finish : exec_inv_preserve_finish_type.
  Proof.
    iIntros (??) "Hdone H".
    iDestruct "H" as (hL0 hL1 hS) "(#Hsrc&#Hlocks&#Hinv)".
    iInv "Hinv" as "H" "_".
    iDestruct "H" as (σ) "(>Hdom1&>Hstate&>Hctx0&>Hctx1&>Hctx_stat&>Hdur)".
    iDestruct "Hdom1" as %Hdom1.
    iApply fupd_mask_weaken; first by solve_ndisj.
    iExists _, _. iFrame.
    iSplitL "".
    { iPureIntro. econstructor. }
    iClear "Hsrc".
    iIntros (????) "(Hctx&Hstate&Hmem)".
    iMod (gen_heap_strong_init σ.(OneDisk.disk_state)) as (hL0' <-) "(hL0&hL0frag)".
    iPoseProof (gen_heap_init_to_bigOp (hG := hL0') with "hL0frag") as "hL0frag".

    iMod (gen_heap_strong_init σ.(OneDisk.disk_state)) as (hL1' <-) "(hL1&hL1frag)".
    iPoseProof (gen_heap_init_to_bigOp (hG := hL1') with "hL1frag") as "hL1frag".

    iMod (gen_heap_strong_init ((λ _, Sync) <$> init_zero)) as (hS' <-) "(hS&hSfrag)".
    iPoseProof (gen_heap_init_to_bigOp (hG := hS') with "hSfrag") as "hSfrag".

    iDestruct (gen_heap_bigOp_split with "hL0frag") as "(hL0a&hL0b)".
    iDestruct (gen_heap_bigOp_split with "hL1frag") as "(hL1a&hL1b)".
    iDestruct (gen_heap_bigOp_split with "hSfrag") as "(hSa&hSb)".

    iDestruct (gen_heap_bigOpM_dom with "hL0a") as "hL0a".
    iDestruct (gen_heap_bigOpM_dom with "hL1a") as "hL1a".
    iDestruct (gen_heap_bigOpM_dom with "hSa") as "hSa".
    rewrite ?Hdom1.
    iDestruct (big_sepM_dom with "hL0a") as "hL0a".
    iDestruct (big_sepM_dom with "hL1a") as "hL1a".
    iDestruct (big_sepM_dom with "hSa") as "hSa".

    iExists hL0', hL1', hS'.
    iSplitL "Hmem hL0a hL1a hSa".
    { iApply big_opM_dom.
      rewrite big_sepM_fmap.
      repeat (iDestruct (@big_sepM_sep with "[$]") as "H").
      iApply (big_sepM_mono with "H").
      iIntros (k x Hlookup) "(((Hs&Hl0)&Hl1)&?)".
      iDestruct "Hs" as (? Hlookup') "Hs".
      rewrite lookup_fmap in Hlookup'.
      apply fmap_Some_1 in Hlookup' as (?&Heq1&Heq2).
      subst.
      rewrite (init_zero_lookup_is_zero k x); last auto.
      iDestruct "Hl0" as (??) "Hl0".
      iDestruct "Hl1" as (??) "Hl1".
      repeat match goal with
             |[ H1 : ?x = Some ?y, H2 : ?x = Some ?z |- _ ] =>
              rewrite H1 in H2; inversion H2; clear H1 H2; subst
             end.
      iFrame. iExists _. iFrame.
    }
    rewrite big_sepM_fmap.
    iDestruct (big_sepM_dom with "hSb") as "hSb".
    replace (dom (gset addr) init_zero) with addrset; last trivial.
    rewrite -{2}Hdom1.
    iDestruct (big_sepM_dom with "hSb") as "hSb".
    repeat (iDestruct (@big_sepM_sep with "[$]") as "H").
    iExists _. iFrame.
    iSplitL "".
    { iPureIntro. auto. }
    iSplitL "hL0".
    { iExists _. iFrame. by iPureIntro. }
    iSplitL "hL1".
    { iExists _. iFrame. by iPureIntro. }
    iSplitL "hS".
    { iExists _. iFrame. iPureIntro. rewrite dom_fmap_L. auto. }
    iDestruct (big_sepM_mono_with_inv with "Hdone H") as "(?&$)"; last by iPureIntro.
    iIntros (k x Hlookup) "H".
    iDestruct "H" as "(Hdone&H)".
    iDestruct "H" as "(((Hs&Hl0)&Hl1)&Hdur)".
    iDestruct "Hdur" as (? stat) "(Hd0&Hd1&Hl0'&Hl1'&Hs'&Hstatus)".
    destruct stat; last first.
    { iDestruct "Hstatus" as "(?&Hreg)".
      iExFalso; iApply (@AllDone_Register_excl with "Hdone Hreg").
    }
    iFrame. iDestruct "Hstatus" as %Heq. subst.
    iExists _, _. iFrame. eauto.
  Qed.
End repRO.

Module repR := twodisk_refinement repRT repRO.
Import repR.

Lemma rep_crash_refinement_seq {T} σ1c σ1a (es: proc_seq OneDisk.Op T) :
  repRT.init_absr σ1a σ1c →
  wf_client_seq es →
  ¬ proc_exec_seq OneDisk.l es (rec_singleton (Ret ())) (1, σ1a) Err →
  ∀ σ2c res, proc_exec_seq TwoDisk.l (compile_proc_seq ReplicatedDiskImpl.impl es)
                                      (rec_singleton recv) (1, σ1c) (Val σ2c res) →
  ∃ σ2a, proc_exec_seq OneDisk.l es (rec_singleton (Ret tt)) (1, σ1a) (Val σ2a res).
Proof. apply repR.R.crash_refinement_seq. Qed.
