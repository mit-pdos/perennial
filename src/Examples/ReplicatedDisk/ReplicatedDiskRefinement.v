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

  Definition status_interp (a: addr) v0 v1 (s: addr_status) :=
    (match s with
     | Sync => ⌜ v0 = v1 ⌝
     | Unsync j K => j ⤇ K (Call (OneDisk.Write_Disk a v0))
     end)%I.

  Global Instance status_interp_timeless a v0 v1 s:
    Timeless (status_interp a v0 v1 s).
  Proof. destruct s; apply _. Qed.

  Definition DurInv (a: addr) v1 :=
    (∃ v0 stat, a d0↦ v0 ∗ a d1↦ v1 ∗ a l0↦{1/2} v0 ∗ a l1↦{1/2} v1 ∗ a s↦{1/2} stat
                  ∗ status_interp a v0 v1 stat)%I.

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
    iSplitL "Hdur Hd0 Hd1 Hl0_auth Hl1_auth Hstatus_auth Hj".
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
    iMod (ghost_step_call with "Hstat Hsrc [$]") as "(Hj&Hstate&_)".
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

End refinement_triples.