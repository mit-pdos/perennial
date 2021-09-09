From stdpp Require Import namespaces.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import excl.
From Perennial.base_logic.lib Require Import invariants.
From Perennial.program_logic Require Export weakestpre.
From Perennial.Helpers Require Import Qextra.

From Perennial.goose_lang Require Export lang typing.
From Perennial.goose_lang Require Import proofmode wpc_proofmode notation crash_borrow.
From Perennial.goose_lang Require Import persistent_readonly.
From Perennial.goose_lang.lib Require Import typed_mem.
From Perennial.goose_lang.lib Require Export rwlock.impl.
Require Import Field.
Add Field Qcfield : Qcanon.Qcft.
Set Default Proof Using "Type".
Opaque crash_borrow.

Section goose_lang.
Context `{ffi_sem: ffi_semantics}.
Context `{!ffi_interp ffi}.
Context {ext_tys: ext_types ext}.

Local Coercion Var' (s:string): expr := Var s.

Section proof.
  Context `{!heapGS Σ} (N : namespace).
  Context `{!stagedG Σ}.

  Definition rfrac: Qp :=
    (Qp_inv (Qp_of_Z (2^64)))%Qp.

  Definition num_readers (n : u64) := 0 `max` int.Z (word.sub n 1).
  Definition remaining_readers (n : u64) : Z :=
    (2^64 - num_readers n).
  Definition remaining_frac (n: u64) :=
    ((Qp_of_Z (remaining_readers n)) * rfrac)%Qp.

  Lemma remaining_frac_read_acquire n :
    1 ≤ int.Z n →
    int.Z n < int.Z (word.add n 1) →
    remaining_frac n = Qp_add (remaining_frac (word.add n 1)) rfrac.
  Proof.
    intros Hle1 Hle2.
    intros.
    rewrite -Qp_to_Qc_inj_iff/Qp_of_Z//=.
    assert (Heq1: Qc_of_Z (1 `max` remaining_readers n) = Qc_of_Z (remaining_readers n)).
    { f_equal. rewrite /remaining_readers.
      rewrite Z.max_r //. rewrite /num_readers.
      word_cleanup.
    }
    assert (Heq2: Qc_of_Z (1 `max` remaining_readers (word.add n 1)) =
                  Qc_of_Z (remaining_readers (word.add n 1))).
    { f_equal. rewrite /remaining_readers.
      rewrite Z.max_r //. rewrite /num_readers.
      word_cleanup.
    }
    rewrite ?Heq1 ?Heq2.
    assert (Heq3: (remaining_readers (word.add n 1)) = remaining_readers n - 1).
    { rewrite /remaining_readers/num_readers.
      word_cleanup.
      assert ((int.Z (word.add n 1) - 1) = int.Z n) as ->.
      { word_cleanup. }
      lia.
    }
    rewrite Heq3 //=.
    rewrite Z2Qc_inj_sub.
    field_simplify => //=.
    f_equal. rewrite Z2Qc_inj_1. field.
  Qed.

  Lemma remaining_frac_read_release n :
    1 < int.Z n →
    Qp_add (remaining_frac n) rfrac = remaining_frac (word.sub n 1).
  Proof.
    intros Hlt.
    rewrite -Qp_to_Qc_inj_iff/Qp_of_Z//=.
    assert (Heq1: Qc_of_Z (1 `max` remaining_readers n) = Qc_of_Z (remaining_readers n)).
    { f_equal. rewrite /remaining_readers.
      rewrite Z.max_r //. rewrite /num_readers.
      word_cleanup.
    }
    assert (Heq2: Qc_of_Z (1 `max` remaining_readers (word.sub n 1)) =
                  Qc_of_Z (remaining_readers (word.sub n 1))).
    { f_equal. rewrite /remaining_readers.
      rewrite Z.max_r //. rewrite /num_readers.
      word_cleanup.
    }
    rewrite ?Heq1 ?Heq2.
    assert (Heq3: (remaining_readers (word.sub n 1)) = remaining_readers n + 1).
    { rewrite /remaining_readers/num_readers.
      word_cleanup.
    }
    rewrite Heq3 //=.
    rewrite Z2Qc_inj_add.
    field_simplify => //=.
  Qed.

  Lemma remaining_free :
    remaining_frac 1 = 1%Qp.
  Proof.
    rewrite -Qp_to_Qc_inj_iff/Qp_of_Z//=.
    assert (Heq1: Qc_of_Z (1 `max` remaining_readers 1) = Qc_of_Z (remaining_readers 1)).
    { f_equal. }
    rewrite Heq1 //=.
    field_simplify => //=.
    rewrite Z2Qc_inj_1. auto.
  Qed.

  Definition rwlock_inv (l : loc) (R Rc: Qp → iProp Σ) : iProp Σ :=
    (∃ u : u64, l ↦{1/4} #u ∗
                if decide (u = U64 0) then
                  True
                else
                  l ↦{3/4} #u ∗
                  crash_borrow (R (remaining_frac u)) (Rc (remaining_frac u))).

  Definition is_rwlock (lk : val) R Rc : iProp Σ :=
    □ (∀ q1 q2, R (q1 + q2)%Qp ∗-∗ R q1 ∗ R q2) ∗
    □ (∀ q1 q2, Rc (q1 + q2)%Qp ∗-∗ Rc q1 ∗ Rc q2) ∗
    □ (∀ q, R q -∗ Rc q) ∗
    (∃ l: loc, ⌜lk = #l⌝ ∧ inv N (rwlock_inv l R Rc))%I.

  Theorem is_rwlock_flat lk R Rc :
    is_rwlock lk R Rc -∗ ⌜∃ (l:loc), lk = #l⌝.
  Proof.
    iIntros "(_&_&_&Hl)"; iDestruct "Hl" as (l) "[-> _]"; eauto.
  Qed.

  Theorem is_rwlock_ty lk R Rc :
    is_rwlock lk R Rc -∗ ⌜val_ty lk rwlockRefT⌝.
  Proof.
    iIntros "Hlk".
    iDestruct (is_rwlock_flat with "Hlk") as (l) "->".
    iPureIntro.
    val_ty.
  Qed.

  Definition wlocked (lk: val) : iProp Σ := ∃ (l:loc), ⌜lk = #l⌝ ∗ l ↦{3/4} #0.

  Lemma locked_loc (l:loc) :
    wlocked #l ⊣⊢ l ↦{3/4} #0.
  Proof.
    rewrite /wlocked.
    iSplit; auto.
    iIntros "Hl".
    iDestruct "Hl" as (l' Heq) "Hl".
    inversion Heq; subst.
    auto.
  Qed.

  Lemma wlocked_exclusive (lk : val) : wlocked lk -∗ wlocked lk -∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct "H1" as (l1 ->) "H1".
    iDestruct "H2" as (l2 ?) "H2".
    inversion H; subst.
    iCombine "H1 H2" as "H".
    iDestruct (heap_mapsto_frac_valid with "H") as %Hval.
    eauto.
  Qed.

  (*
  Global Instance rwlock_inv_ne l : NonExpansive (rwlock_inv l).
  Proof. solve_proper. Qed.
  Global Instance is_lock_ne l : NonExpansive (is_lock l).
  Proof. solve_proper. Qed.
   *)

  (** The main proofs. *)
  Global Instance is_rwlock_persistent l R Rc : Persistent (is_rwlock l R Rc).
  Proof. apply _. Qed.
  Global Instance wlocked_timeless l : Timeless (wlocked l).
  Proof. apply _. Qed.

  Definition is_free_lock (l: loc): iProp Σ := l ↦ #1 ∗ later_tok ∗ later_tok ∗ later_tok ∗ later_tok.

  Theorem is_free_lock_ty lk :
    is_free_lock lk -∗ ⌜val_ty #lk rwlockRefT⌝.
  Proof.
    iIntros "Hlk".
    iPureIntro.
    val_ty.
  Qed.

  Theorem alloc_lock E l R Rc :
    □ (∀ q1 q2, R (q1 + q2)%Qp ∗-∗ R q1 ∗ R q2) -∗
    □ (∀ q1 q2, Rc (q1 + q2)%Qp ∗-∗ Rc q1 ∗ Rc q2) -∗
    □ (∀ q, R q -∗ Rc q) -∗
    l ↦ #1 -∗ crash_borrow (R 1%Qp) (Rc 1%Qp) ={E}=∗ is_rwlock #l R Rc.
  Proof.
    iIntros "? ? ? Hl HR".
    iMod (inv_alloc N _ (rwlock_inv l R Rc) with "[Hl HR]") as "#?".
    { iIntros "!>". iExists _. iFrame.
      rewrite /is_free_lock.
      iEval (rewrite -Qp_quarter_three_quarter) in "Hl".
      iDestruct (fractional.fractional_split_1 with "Hl") as "[Hl1 Hl2]".
      iFrame.
      destruct (decide _); auto.
      rewrite remaining_free. iFrame.
    }
    iModIntro.
    iFrame.
    iExists l.
    iSplit; eauto.
  Qed.

  Lemma wp_new_free_lock:
    {{{ True }}} rwlock.new #() {{{ lk, RET #lk; is_free_lock lk }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_call.
    iApply wp_crash_borrow_generate_pre; first auto.
    wp_apply wp_alloc_untyped; auto.
    iIntros (?) "Hl Htoks".
    iApply "HΦ". iFrame.
 Qed.

  Lemma alloc_rwlock k Φ Φc e lk (R Rc : Qp → iProp Σ):
    □ (∀ q1 q2, R (q1 + q2)%Qp ∗-∗ R q1 ∗ R q2) -∗
    □ (∀ q1 q2, Rc (q1 + q2)%Qp ∗-∗ Rc q1 ∗ Rc q2) -∗
    □ (∀ q, R q -∗ Rc q) -∗
    R 1%Qp ∗
    is_free_lock lk ∗
    (is_rwlock #lk R Rc -∗
          WPC e @ k; ⊤ {{ Φ }} {{ Rc 1%Qp -∗ Φc }}) -∗
    WPC e @ k; ⊤ {{ Φ }} {{ Φc }}.
  Proof.
    clear.
    iIntros "#Hwand1 #Hwand2 #Hwand3 (HR&Hfree&Hwp)".
    iDestruct "Hfree" as "(Hfree1&Htoks)".
    iApply (wpc_crash_borrow_inits with "[$] HR []").
    { iModIntro. iApply "Hwand3". }
    iIntros "Hborrow".
    iMod (alloc_lock with "[] [] [] [$] Hborrow") as "H"; try eauto.
    iApply "Hwp". eauto.
  Qed.

  Lemma try_read_acquire_spec E lk R Rc :
    ↑N ⊆ E →
    {{{ is_rwlock lk R Rc }}} rwlock.try_read_acquire lk @ NotStuck; E
    {{{ b, RET #b; if b is true then crash_borrow (R rfrac) (Rc rfrac) else True }}}.
  Proof.
    iIntros (? Φ) "(#Hwand1&#Hwand2&#Hwand3&#Hl) HΦ". iDestruct "Hl" as (l ->) "#Hinv".
    wp_rec. wp_bind (!#l)%E.
    iInv N as (u) "[Hl HR]".
    iApply (wp_load with "[$]").
    iNext. iIntros "Hl".
    iModIntro.
    iSplitL "Hl HR".
    { iNext. iExists _. iFrame. }
    wp_pures.
    destruct (decide (int.Z 1 ≤ int.Z u ∧ int.Z u < int.Z (word.add u 1))).
    - rewrite ?bool_decide_eq_true_2; try naive_solver.
      wp_pures. wp_bind (CmpXchg _ _ _). iInv N as (u') "[>Hl HR]".
      destruct (decide (u' = u)).
      * subst.
        rewrite (decide_False); last first.
        { destruct a. intros Hu. subst. auto. }
        iDestruct "HR" as "[>Hl2 HR]".
        iCombine "Hl Hl2" as "Hl".
        rewrite Qp_quarter_three_quarter.
        iApply (wpc_wp NotStuck 0 _ _ _ True).
        iApply (wpc_crash_borrow_split _ _ _ _ _ _ _
                                       (R (remaining_frac (word.add u 1)))
                                       (R rfrac)
                                       (Rc (remaining_frac (word.add u 1)))
                                       (Rc rfrac)
                  with "HR"); auto.
        { rewrite remaining_frac_read_acquire; try naive_solver.
          iDestruct ("Hwand1" $! _ _) as "(H&?)".
          iApply "H".
        }
        {
          iDestruct ("Hwand2" $! _ _) as "(_&H)".
          iIntros "!>". iIntros. iDestruct ("H" with "[$]") as "Hcomb".
          iExactEq "Hcomb".
          f_equal. rewrite -remaining_frac_read_acquire //; try naive_solver.
        }
        iApply wp_wpc.
        wp_cmpxchg_suc.
        iModIntro.
        iEval (rewrite -Qp_quarter_three_quarter) in "Hl".
        iDestruct (fractional.fractional_split_1 with "Hl") as "[Hl1 Hl2]".
        iIntros "(Hc1&Hc2)".
        iSplit; first done. iModIntro.
        iSplitL "Hl1 Hl2 Hc1"; first (iNext; iExists (word.add u 1); eauto).
        { iFrame.
          rewrite (decide_False); last first.
          { intros Heq0. rewrite Heq0 in a. word_cleanup.
            assert (int.Z 0 = 0%Z) by word.
            lia. }
          iFrame.
        }
        wp_pures. iModIntro. iApply "HΦ". eauto.
      * wp_cmpxchg_fail. iModIntro.
        iSplitL "Hl HR".
        { iNext. iExists _. iFrame. }
        wp_pures. iModIntro. iApply "HΦ". eauto.
    - case_bool_decide; first (case_bool_decide; first naive_solver).
      * wp_pures. iModIntro. iApply "HΦ". eauto.
      * wp_pures. iModIntro. iApply "HΦ". eauto.
  Qed.

  Lemma read_acquire_spec lk R Rc :
    {{{ is_rwlock lk R Rc }}} rwlock.read_acquire lk {{{ RET #(); crash_borrow (R rfrac) (Rc rfrac) }}}.
  Proof.
    iIntros (Φ) "#Hl HΦ". iLöb as "IH". wp_rec.
    wp_apply (try_read_acquire_spec with "Hl"); auto. iIntros ([]).
    - iIntros "H". wp_if. iApply "HΦ"; by iFrame.
    - iIntros "_". wp_if. iApply ("IH" with "[HΦ]"). auto.
  Qed.

  Lemma try_read_release_spec lk R Rc :
    {{{ is_rwlock lk R Rc ∗ crash_borrow (R rfrac) (Rc rfrac) }}} rwlock.try_read_release lk
    {{{ b, RET #b; if b is false then crash_borrow (R rfrac) (Rc rfrac) else True }}}.
  Proof.
    iIntros (Φ) "((#Hwand1&#Hwand2&#Hwand3&#Hl)&Hborrow) HΦ". iDestruct "Hl" as (l ->) "#Hinv".
    wp_rec. wp_bind (!#l)%E.
    iInv N as (u) "[Hl HR]".
    iApply (wp_load with "[$]").
    iNext. iIntros "Hl".
    iModIntro.
    iSplitL "Hl HR".
    { iNext. iExists _. iFrame. }
    wp_pures.
    case_bool_decide.
    - wp_pures. wp_bind (CmpXchg _ _ _). iInv N as (u') "[>Hl HR]".
      destruct (decide (u' = u)).
      * subst.
        rewrite (decide_False); last first.
        {  intros Hu. subst. inversion H.  }
        iDestruct "HR" as "[>Hl2 HR]".
        iCombine "Hl Hl2" as "Hl".
        rewrite Qp_quarter_three_quarter.
        iApply (wpc_wp NotStuck 0 _ _ _ True).
        iApply (wpc_crash_borrow_combine _ _ _ _ _ (R (remaining_frac (word.sub u 1))) _
                                       (R (remaining_frac u))
                                       (R rfrac)
                                       (Rc (remaining_frac u))
                                       (Rc rfrac)
                  with "HR Hborrow"); auto.
        { rewrite -remaining_frac_read_release; last naive_solver.
          iDestruct ("Hwand2" $! _ _) as "(H&?)".
          iApply "H".
        }
        {
          iDestruct ("Hwand1" $! _ _) as "(_&H)".
          iIntros "!>". iIntros. iModIntro. iDestruct ("H" with "[$]") as "Hcomb".
          iExactEq "Hcomb".
          f_equal. rewrite -remaining_frac_read_release; auto.
        }
        iApply wp_wpc.
        wp_cmpxchg_suc.
        iModIntro.
        iEval (rewrite -Qp_quarter_three_quarter) in "Hl".
        iDestruct (fractional.fractional_split_1 with "Hl") as "[Hl1 Hl2]".
        iIntros "Hc".
        iSplit; first done. iModIntro.
        iSplitL "Hl1 Hl2 Hc"; first (iNext; iExists (word.sub u 1); eauto).
        { iFrame.
          rewrite (decide_False); last first.
          { intros Heq.
            assert (int.Z (word.sub u 1) = int.Z 0) as Heqsub.
            { rewrite Heq //. }
            rewrite word.unsigned_sub in Heqsub.
            rewrite wrap_small in Heqsub.
            {
              replace (int.Z 0) with 0 in * by auto.
              replace (int.Z 1) with 1 in * by auto.
              lia.
            }
            split.
            - lia.
            - word_cleanup.
          }
          iFrame.
        }
        wp_pures. iModIntro. iApply "HΦ". eauto.
      * wp_cmpxchg_fail. iModIntro.
        iSplitL "Hl HR".
        { iNext. iExists _. iFrame. }
        wp_pures. iModIntro. iApply "HΦ". eauto.
    - wp_pures. iModIntro. iApply "HΦ". eauto.
  Qed.

  Lemma read_release_spec lk R Rc :
    {{{ is_rwlock lk R Rc ∗ crash_borrow (R rfrac) (Rc rfrac) }}} rwlock.read_release lk {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "(#Hl&Hcb) HΦ". iLöb as "IH". wp_rec.
    wp_apply (try_read_release_spec with "[$Hl $Hcb]"); auto. iIntros ([]).
    - iIntros "H". wp_if. iApply "HΦ"; by iFrame.
    - iIntros "H". wp_if. iApply ("IH" with "[$] [HΦ]"). auto.
  Qed.

  Lemma try_write_acquire_spec lk R Rc :
    {{{ is_rwlock lk R Rc }}} rwlock.try_write_acquire lk
    {{{ b, RET #b; if b is true then wlocked lk ∗ crash_borrow (R 1%Qp) (Rc 1%Qp) else True }}}.
  Proof.
    iIntros (Φ) "(#Hwand1&#Hwand2&#Hwand3&#Hl) HΦ". iDestruct "Hl" as (l ->) "#Hinv".
    wp_rec.
    wp_bind (CmpXchg _ _ _). iInv N as (u') "[>Hl HR]".
    destruct (decide (u' = 1)).
    - rewrite decide_False; last first.
      { intros Heq0. subst. inversion Heq0. }
      subst.
      iDestruct "HR" as "(>Hl2&Hb)".
      iCombine "Hl Hl2" as "Hl".
      rewrite Qp_quarter_three_quarter.
      wp_cmpxchg_suc.
      iModIntro.
      iEval (rewrite -Qp_quarter_three_quarter) in "Hl".
      iDestruct (fractional.fractional_split_1 with "Hl") as "[Hl1 Hl2]".
      iSplitL "Hl1"; first (iNext; iExists (U64 0); eauto).
      wp_pures.
      iApply "HΦ".
      rewrite remaining_free.
      iFrame. rewrite /wlocked.
      eauto with iFrame.
    - wp_cmpxchg_fail.
      iModIntro.
      iSplitL "Hl HR".
      { iExists u'. iFrame. }
      wp_pures. by iApply "HΦ".
  Qed.

  Lemma write_acquire_spec lk R Rc :
    {{{ is_rwlock lk R Rc }}}
      rwlock.write_acquire lk
    {{{ RET #(); wlocked lk ∗ crash_borrow (R 1%Qp) (Rc 1%Qp) }}}.
  Proof.
    iIntros (Φ) "#Hl HΦ". iLöb as "IH". wp_rec.
    wp_apply (try_write_acquire_spec with "Hl"); auto. iIntros ([]).
    - iIntros "[Hlked HR]". wp_if. iApply "HΦ"; by iFrame.
    - iIntros "_". wp_if. iApply ("IH" with "[HΦ]"). auto.
  Qed.

  Lemma release_spec lk R Rc :
    {{{ is_rwlock lk R Rc ∗ wlocked lk ∗ crash_borrow (R 1%Qp) (Rc 1%Qp) }}}
      rwlock.write_release lk
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "((#Hwand1&#Hwand2&#Hwand3&#Hl)&Hlocked&Hborrow) HΦ". iDestruct "Hl" as (l ->) "#Hinv".
    wp_rec.
    wp_bind (CmpXchg _ _ _).
    iInv N as (b) "[>Hl _]".

    iDestruct (locked_loc with "Hlocked") as "Hl2".
    iDestruct (heap_mapsto_agree with "[$Hl $Hl2]") as %->.
    iCombine "Hl Hl2" as "Hl".
    rewrite Qp_quarter_three_quarter.
    wp_cmpxchg_suc.
    iModIntro.
    iSplitR "HΦ"; last by wp_seq; iApply "HΦ".
    iEval (rewrite -Qp_quarter_three_quarter) in "Hl".
    iDestruct (fractional.fractional_split_1 with "Hl") as "[Hl1 Hl2]".
    iNext. iExists (U64 1). iFrame.
    rewrite remaining_free. eauto.
  Qed.

End proof.
End goose_lang.

Typeclasses Opaque is_rwlock.
