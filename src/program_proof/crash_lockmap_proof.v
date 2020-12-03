From Perennial.program_proof Require Import proof_prelude.
From Perennial.algebra Require Import deletable_heap.
From Goose.github_com.mit_pdos.goose_nfsd Require Import lockmap.
From Perennial.goose_lang.lib Require Import wp_store.
From Perennial.goose_lang.lib Require Import slice.typed_slice.

From Perennial.Helpers Require Import NamedProps range_set.
From Perennial.program_proof Require Import lockmap_proof.
From Perennial.program_logic Require Export na_crash_inv.
From Perennial.goose_lang Require Import proofmode wpc_proofmode notation.

Section proof.
  Context `{!heapG Σ, stagedG Σ}.
  Context `{!gen_heapPreG u64 bool Σ}.

  Implicit Types s : Slice.t.
  Implicit Types (stk:stuckness) (E: coPset).

  Definition is_crash_lockMap k (l: loc) (ghs: list (gen_heapG u64 bool Σ)) (covered: gset u64)
             (P Pcrash: u64 -> iProp Σ) : iProp Σ :=
    is_lockMap l ghs covered (fun i => na_crash_inv k (P i) (Pcrash i)).

  Definition CrashLocked k lk (ghs : list (gen_heapG u64 bool Σ)) (addr : u64) P Pcrash : iProp Σ :=
    ∃ covered,
    na_crash_inv k (P addr) (Pcrash addr) ∗
    is_lockMap lk ghs covered (fun i => na_crash_inv k (P i) (Pcrash i)) ∗
    Locked ghs addr.

  Theorem wpc_MkLockMap k covered (P Pcrash : u64 -> iProp Σ) :
    {{{ [∗ set] a ∈ covered, P a ∗ □ (▷ P a -∗ |C={⊤}_k=> ▷ Pcrash a) }}}
      MkLockMap #() @ NotStuck; (S k); ⊤
    {{{ l ghs, RET #l; is_crash_lockMap (S k) l ghs covered P Pcrash ∗
                       <disc> (|C={⊤}_(S k)=> [∗ set] a ∈ covered, ▷ Pcrash a) }}}
    {{{ [∗ set] a ∈ covered, ▷ Pcrash a }}}.
  Proof using gen_heapPreG0.
    iIntros (Φ Φc) "HP HΦ".
    iAssert (|={⊤}=> [∗ set] a ∈ covered, na_crash_inv (S k) (P a) (Pcrash a) ∗
                                          <disc> (|C={⊤}_S k=> ▷ Pcrash a))%I
      with "[HP]" as "Hcrash_inv".
    { iApply big_sepS_fupd. iApply (big_sepS_mono with "HP").
      iIntros (a Hin) "(HP&#HPwand)".
      iMod (na_crash_inv_alloc _ ⊤ (Pcrash a) (P a) with "[$] [$]") as "($&$)".
      auto. }
    iMod "Hcrash_inv" as "H".
    iDestruct (big_sepS_sep with "H") as "(Hna&Hcfupd)".
    rewrite big_sepS_own_disc_fupd.
    iApply (wpc_crash_frame_wand' with "[-Hcfupd] [Hcfupd]"); last first.
    { iModIntro.
      iApply cfupd_big_sepS in "Hcfupd".
      rewrite big_sepS_later_2.
      iAssumption. }
    2: set_solver.
    2: lia.
    iPoseProof (wp_wpc_step_frame' _ _ _ _ _
                (([∗ set] a ∈ covered, ▷ Pcrash a) -∗ Φc)%I
                (∀ (l : loc) (ghs : list (gen_heapG u64 bool Σ)),
                    is_crash_lockMap (S k) l ghs covered P Pcrash
                                     ∗ <disc> (|C={⊤}_S k=> [∗ set] a ∈ covered, ▷ Pcrash a) -∗ Φ #l)%I
                  with "[HΦ Hna]") as "H".
    3: {
      iApply (wpc_mono with "H"); eauto.
      repeat (f_equiv; simpl).
      by rewrite big_sepS_later.
    }
    { eauto. }
    iSplitL "HΦ".
    {
      iApply (and_mono_l with "HΦ").
      f_equiv.
    }
    wp_apply (wp_MkLockMap with "Hna").
    iIntros (l ghs) "His_lockMap". iIntros "HΦ Hcfupd".
    iApply "HΦ". iFrame.
    rewrite big_sepS_later //.
  Qed.

  Theorem wp_LockMap__Acquire k l ghs covered (addr : u64) (P Pcrash : u64 -> iProp Σ) :
    {{{ is_crash_lockMap k l ghs covered P Pcrash ∗
                   ⌜addr ∈ covered⌝ }}}
      LockMap__Acquire #l #addr
    {{{ RET #(); CrashLocked k l ghs addr P Pcrash }}}.
  Proof.
    iIntros (Φ) "#H HΦ".
    wp_apply (wp_LockMap__Acquire with "H").
    iIntros "(Hna&Hlocked)".
    iApply "HΦ". iExists _; iFrame.
    iDestruct "H" as "($&%)".
  Qed.

  Lemma use_CrashLocked E1 k k' e lk ghs addr R Rcrash Φ Φc {HL: AbsLaterable Φc}:
    (S k ≤ k')%nat →
    CrashLocked (S k') lk ghs addr R Rcrash -∗
    <disc> Φc ∧ (▷ R addr -∗
         WPC e @ (S k); E1 {{ λ v, (CrashLocked (S k') lk ghs addr R Rcrash -∗ (<disc> Φc ∧ Φ v)) ∗ ▷ R addr }}
                                         {{ Φc ∗ ▷ Rcrash addr }}) -∗
    WPC e @ (S k); E1 {{ Φ }} {{ Φc }}.
  Proof.
    iIntros (?) "Hcrash_locked H".
    iDestruct "Hcrash_locked" as (?) "(Hfull&#His_lock&Hlocked)".
    iApply (wpc_na_crash_inv_open _ k k' (S k) with "[$] [H Hlocked]"); try iFrame; auto.
    iSplit.
    - iDestruct "H" as "($&_)".
    - iIntros "HR". iDestruct "H" as "(_&H)".
      iSpecialize ("H" with "[$]").
      iApply (wpc_strong_mono with "H"); eauto.
      iSplit.
      * iIntros (?) "(Hclose&?)". iModIntro. iFrame. iFrame "#".
        iIntros. iApply "Hclose". iFrame; eauto.
      * iIntros.  iIntros "!> $". eauto.
  Qed.

  Theorem wp_LockMap__Release k l ghs (addr : u64) (P Pcrash : u64 -> iProp Σ) :
    {{{ CrashLocked k l ghs addr P Pcrash }}}
      LockMap__Release #l #addr
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "Hcrash_locked HΦ".
    iDestruct "Hcrash_locked" as (covered) "(Hfull&#His_lock&Hlocked)".
    wp_apply (wp_LockMap__Release with "[His_lock Hlocked Hfull]").
    { iFrame "His_lock". iFrame. }
    by iApply "HΦ".
  Qed.

End proof.
