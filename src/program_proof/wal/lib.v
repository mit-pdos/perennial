From Goose.github_com.mit_pdos.goose_nfsd Require Import wal.

From Perennial.program_proof Require Export wal.abstraction.
From Perennial.program_proof Require Import proof_prelude disk_lib.

Section heap.
Context `{!heapG Σ}.
Definition update_val (up:u64*Slice.t): val :=
  (#(fst up), (slice_val (snd up), #()))%V.

Theorem update_val_t u : val_ty (update_val u) (struct.t Update.S).
Proof.
  repeat constructor.
  destruct u; rewrite /blockT; val_ty.
Qed.

Definition updates_slice (bk_s: Slice.t) (bs: list update.t): iProp Σ :=
  ∃ bks, is_slice bk_s (struct.t Update.S) 1 (update_val <$> bks) ∗
   [∗ list] _ ↦ b_upd;upd ∈ bks;bs , let '(update.mk a b) := upd in
                                     is_block (snd b_upd) 1 b ∗
                                     ⌜fst b_upd = a⌝.

Definition updates_slice_frag (bk_s: Slice.t) (q:Qp) (bs: list update.t): iProp Σ :=
  ∃ bks, is_slice_small bk_s (struct.t Update.S) q (update_val <$> bks) ∗
   [∗ list] _ ↦ b_upd;upd ∈ bks;bs,
       is_block (snd b_upd) q upd.(update.b) ∗
       ⌜fst b_upd = upd.(update.addr)⌝.

Theorem updates_slice_frag_acc bk_s bs :
  updates_slice bk_s bs -∗
  updates_slice_frag bk_s 1 bs ∗
   (updates_slice_frag bk_s 1 bs -∗ updates_slice bk_s bs).
Proof.
  iIntros "Hupds".
  iDestruct "Hupds" as (bks) "[Hbks Hupds]".
  iDestruct (is_slice_small_acc with "Hbks") as "[Hbks_small Hbks]".
  iSplitR "Hbks".
  - iExists _; iFrame.
    iApply (big_sepL2_mono with "Hupds").
    intros ? ? [a b]; auto.
  - iIntros "Hupds".
    iDestruct "Hupds" as (bks') "[Hs Hupds]".
    iSpecialize ("Hbks" with "Hs").
    iExists _; iFrame.
    iApply (big_sepL2_mono with "Hupds").
    intros ? ? [a b]; auto.
Qed.

Lemma updates_slice_frag_len bk_s q bs :
  updates_slice_frag bk_s q bs -∗ ⌜int.val bk_s.(Slice.sz) = length bs⌝.
Proof.
  iIntros "Hupds".
  iDestruct "Hupds" as (bks) "[Hbs Hbks]".
  iDestruct (is_slice_small_sz with "Hbs") as %Hbs_sz.
  iDestruct (big_sepL2_length with "Hbks") as %Hbks_len.
  rewrite fmap_length in Hbs_sz.
  iPureIntro.
  rewrite -Hbks_len.
  rewrite Hbs_sz.
  destruct bk_s; simpl.
  word.
Qed.

Lemma updates_slice_len bk_s bs :
  updates_slice bk_s bs -∗ ⌜int.val bk_s.(Slice.sz) = length bs⌝.
Proof.
  iIntros "Hupds".
  iDestruct (updates_slice_frag_acc with "Hupds") as "[Hupds _]".
  iDestruct (updates_slice_frag_len with "Hupds") as %Hlen.
  auto.
Qed.

Existing Instance is_slice_small_Fractional.

Global Instance fractional_big_sepL2:
  ∀ (PROP : bi) (A B : Type) (l1 : list A) (l2: list B) (Ψ : nat → A → B -> Qp → PROP),
    (∀ (k : nat) (x : A) (y:B), fractional.Fractional (Ψ k x y))
    → fractional.Fractional (λ q : Qp, ([∗ list] k↦x;y ∈ l1; l2, Ψ k x y q)%I).
Proof.
  intros.
  intros q1 q2.
  rewrite -big_sepL2_sep.
  setoid_rewrite H.
  auto.
Qed.

Instance is_blocks_AsFractional bks q v :
  fractional.AsFractional
    ([∗ list] b_upd;upd ∈ bks;v,
                                (is_block b_upd.2 q upd.(update.b) ∗ ⌜b_upd.1 = upd.(update.addr)⌝))%I
    (λ q, [∗ list] b_upd;upd ∈ bks;v, (is_block b_upd.2 q upd.(update.b) ∗ ⌜b_upd.1 = upd.(update.addr)⌝))%I
    q.
Proof.
  constructor; auto.
  apply _.
  Grab Existential Variables.
  exact 1%Qp.
Qed.

Instance update_val_inj : Inj eq eq update_val.
Proof.
  intros u1 u2.
  rewrite /update_val.
  destruct u1, u2; simpl.
  destruct t, t0; simpl in *; subst.
  inversion 1; subst.
  congruence.
Qed.

Global Instance updates_slice_frag_AsMapsTo bk_s bs :
  AsMapsTo (updates_slice_frag bk_s 1 bs) (λ bk_s q bs, updates_slice_frag bk_s q bs) bk_s bs.
Proof.
  constructor; auto; intros.
  - intros q1 q2.
    iSplit.
    + iIntros "Hupds".
      iDestruct "Hupds" as (bks) "[Hupds Hbs]".
      iDestruct (fractional.fractional_split_1 with "Hupds") as "[Hupds1 Hupds2]".
      iDestruct (fractional.fractional_split_1 with "Hbs") as "[Hbs1 Hbs2]".
      iSplitL "Hupds1 Hbs1".
      * iExists _; iFrame.
      * iExists _; iFrame.
    + iIntros "[Hupds1 Hupds2]".
      iDestruct "Hupds1" as (bks) "[Hbs1 Hupds1]".
      iDestruct "Hupds2" as (bks') "[Hbs2 Hupds2]".
      iDestruct (is_slice_small_agree with "Hbs1 Hbs2") as %Heq.
      apply (fmap_inj update_val) in Heq; auto using update_val_inj; subst.
      iDestruct (fractional.fractional_split_2 with "Hbs1 Hbs2") as "Hbs".
      { apply _. }
      iDestruct (fractional.fractional_split_2 _ _ _ _ q1 q2 with "Hupds1 Hupds2") as "Hupds".
      { apply _. }
      iExists _; iFrame.
  - apply _.
Qed.

Theorem wp_SliceGet_updates stk E bk_s bs (i: u64) (u: update.t) :
  {{{ updates_slice bk_s bs ∗ ⌜bs !! int.nat i = Some u⌝ }}}
    SliceGet (struct.t Update.S) (slice_val bk_s) #i @ stk; E
  {{{ uv, RET (update_val uv);
      ⌜uv.1 = u.(update.addr)⌝ ∗
      is_block uv.2 1 u.(update.b) ∗
      (is_block uv.2 1 u.(update.b) -∗ updates_slice bk_s bs)
  }}}.
Proof.
  iIntros (Φ) "[Hupds %Hlookup] HΦ".
  iDestruct "Hupds" as (bks) "[Hbk_s Hbks]".
  iDestruct (big_sepL2_lookup_2_some _ _ _ _ _ Hlookup with "Hbks")
    as %[b_upd Hlookup_bs].
  iDestruct (is_slice_small_acc with "Hbk_s") as "[Hbk_s Hbk_s_rest]".
  wp_apply (wp_SliceGet with "[$Hbk_s]").
  { iPureIntro.
    rewrite list_lookup_fmap.
    rewrite Hlookup_bs //. }
  iIntros "[Hbk_s _]".
  iDestruct ("Hbk_s_rest" with "Hbk_s") as "Hbk_s".
  iApply "HΦ".
  iDestruct (big_sepL2_lookup_acc with "Hbks") as "[Hbi Hbks]"; eauto.
  destruct u as [a b]; simpl.
  iDestruct "Hbi" as "[Hbi <-]".
  iSplit; first by auto.
  iFrame.
  iIntros "Hbi".
  iSpecialize ("Hbks" with "[$Hbi //]").
  rewrite /updates_slice.
  iExists _; iFrame.
Qed.

Lemma has_zero_update : has_zero (struct.t Update.S).
Proof.
  repeat constructor.
Qed.

Hint Resolve has_zero_update.

Transparent slice.T.
Theorem val_ty_update uv :
  val_ty (update_val uv) (struct.t Update.S).
Proof.
  val_ty.
Qed.
Opaque slice.T.

Hint Resolve val_ty_update : val_ty.

Theorem wp_SliceAppend_updates {stk E bk_s bs} {uv: u64 * Slice.t} {b} :
  length bs + 1 < 2^64 ->
  {{{ updates_slice bk_s bs ∗ is_block uv.2 1 b }}}
    SliceAppend (struct.t Update.S) (slice_val bk_s) (update_val uv) @ stk; E
  {{{ bk_s', RET slice_val bk_s';
      updates_slice bk_s' (bs ++ [update.mk uv.1 b])
  }}}.
Proof.
  iIntros (Hlen_overflow Φ) "[Hupds Hub] HΦ".
  iDestruct (updates_slice_len with "Hupds") as %Hlen.
  iDestruct "Hupds" as (bks) "[Hbks Hupds]".
  wp_apply (wp_SliceAppend with "[$Hbks]"); auto.
  { iPureIntro.
    split; auto. word. }
  iIntros (s') "Hs".
  iApply "HΦ".
  change ([update_val uv]) with (update_val <$> [uv]).
  rewrite -fmap_app.
  rewrite /updates_slice.
  iExists (bks ++ [uv]).
  iFrame "Hs".
  iApply (big_sepL2_app with "Hupds").
  simpl. auto.
Qed.

Theorem wp_copyUpdateBlock stk E (u: u64 * Slice.t) q b :
  {{{ is_block (snd u) q b }}}
    copyUpdateBlock (update_val u) @ stk; E
  {{{ (s':Slice.t), RET (slice_val s'); is_block (snd u) q b ∗ is_block s' 1 b }}}.
Proof.
  iIntros (Φ) "Hb HΦ".
  destruct u as [a s]; simpl.
  wp_call.
  wp_apply wp_new_slice; first by auto.
  iIntros (s') "Hs'".
  iDestruct (is_slice_to_small with "Hs'") as "Hs'".
  wp_pures.
  wp_apply (wp_SliceCopy_full with "[$Hb $Hs']").
  { iPureIntro.
    autorewrite with len.
    rewrite length_Block_to_vals.
    reflexivity. }
  iIntros "(Hs&Hs')".
  wp_pures.
  iApply ("HΦ" with "[$]").
Qed.

End heap.

Hint Resolve update_val_t : val_ty.
