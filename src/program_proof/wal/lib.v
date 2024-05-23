From Goose.github_com.mit_pdos.go_journal Require Import wal.

From Perennial.Helpers Require Import List.
From Perennial.program_proof Require Export wal.abstraction.
From Perennial.program_proof Require Import disk_prelude disk_lib.
From Perennial.program_proof Require util_proof.

Section heap.
Context `{!heapGS Σ}.
Definition update_val (up:u64*Slice.t): val :=
  (#(fst up), (slice_val (snd up), #()))%V.

Theorem update_val_t u : val_ty (update_val u) (struct.t Update).
Proof.
  repeat constructor.
  destruct u; rewrite /blockT; val_ty.
Qed.

Hint Resolve update_val_t : core.

Definition is_update (uv: u64*Slice.t) (q:dfrac) (u: update.t): iProp Σ :=
  ⌜uv.1 = u.(update.addr)⌝ ∗
  is_block uv.2 q u.(update.b).

Theorem is_update_addr uv q u :
  is_update uv q u -∗ ⌜uv.1 = u.(update.addr)⌝.
Proof.
  iIntros "[$ _]".
Qed.

Definition updates_slice' q (bk_s: Slice.t) (bs: list update.t): iProp Σ :=
  ∃ bks, own_slice bk_s (struct.t Update) (DfracOwn 1) (update_val <$> bks) ∗
   [∗ list] _ ↦ b_upd;upd ∈ bks;bs , let '(update.mk a b) := upd in
                                     is_block (snd b_upd) q b ∗
                                     ⌜fst b_upd = a⌝.

Definition updates_slice (bk_s: Slice.t) (bs: list update.t): iProp Σ :=
  updates_slice' (DfracOwn 1) bk_s bs.

Definition updates_slice_frag' (bk_s: Slice.t) (q1 q2:dfrac) (bs: list update.t): iProp Σ :=
  ∃ bks, own_slice_small bk_s (struct.t Update) q1 (update_val <$> bks) ∗
   [∗ list] _ ↦ uv;upd ∈ bks;bs, is_update uv q2 upd.

Definition updates_slice_frag (bk_s: Slice.t) (q:dfrac) (bs: list update.t): iProp Σ :=
  updates_slice_frag' bk_s q q bs.

Theorem updates_slice_cap_acc' bk_s q bs :
  updates_slice' q bk_s bs ⊣⊢
  updates_slice_frag' bk_s (DfracOwn 1) q bs ∗ own_slice_cap bk_s (struct.t Update).
Proof.
  iSplit.
  - iIntros "Hupds".
    iDestruct "Hupds" as (bks) "[Hbks Hupds]".
    iDestruct (own_slice_split with "Hbks") as "[Hbks_small $]".
    iExists _; iFrame.
    iApply (big_sepL2_mono with "Hupds").
    intros ? ? [a b] **.
      by iIntros "[$ %]".
  - iIntros "[Hupds Hcap]".
    iDestruct "Hupds" as (bks) "[Hbks Hupds]".
    iDestruct (own_slice_split with "[$Hbks $Hcap]") as "Hbks".
    iExists _; iFrame.
    iApply (big_sepL2_mono with "Hupds").
    intros ? ? [a b] **.
      by iIntros "[% $]".
Qed.

Theorem updates_slice_cap_acc bk_s bs :
  updates_slice bk_s bs ⊣⊢
  updates_slice_frag bk_s (DfracOwn 1) bs ∗ own_slice_cap bk_s (struct.t Update).
Proof. iApply updates_slice_cap_acc'. Qed.

Theorem updates_slice_frag_acc q bk_s bs :
  updates_slice' q bk_s bs -∗
  updates_slice_frag' bk_s (DfracOwn 1) q bs ∗
   (∀ bs', updates_slice_frag' bk_s (DfracOwn 1) q bs' -∗ updates_slice' q bk_s bs').
Proof.
  iIntros "Hupds".
  rewrite updates_slice_cap_acc'.
  iDestruct "Hupds" as "[$ Hcap]".
  iIntros (bs') "Hupds".
  rewrite updates_slice_cap_acc'.
  iFrame.
Qed.

Theorem updates_slice_to_frag bk_s q bs :
  updates_slice' q bk_s bs -∗
  updates_slice_frag' bk_s (DfracOwn 1) q bs.
Proof.
  rewrite updates_slice_cap_acc'.
  iIntros "[$ _]".
Qed.

Lemma updates_slice_frag_len bk_s q1 q2 bs :
  updates_slice_frag' bk_s q1 q2 bs -∗ ⌜uint.Z bk_s.(Slice.sz) = length bs⌝.
Proof.
  iIntros "Hupds".
  iDestruct "Hupds" as (bks) "[Hbs Hbks]".
  iDestruct (own_slice_small_sz with "Hbs") as %Hbs_sz.
  iDestruct (big_sepL2_length with "Hbks") as %Hbks_len.
  rewrite fmap_length in Hbs_sz.
  iPureIntro.
  rewrite -Hbks_len.
  rewrite Hbs_sz.
  destruct bk_s; simpl.
  word.
Qed.

Lemma updates_slice_frag_wf bk_s q1 q2 bs :
  updates_slice_frag' bk_s q1 q2 bs -∗ ⌜uint.Z bk_s.(Slice.sz) ≤ uint.Z bk_s.(Slice.cap)⌝.
Proof.
  iIntros "Hupds".
  iDestruct "Hupds" as (bks) "[Hbs Hbks]".
  iDestruct (own_slice_small_wf with "Hbs") as %Hbs_wf.
  auto.
Qed.

Lemma updates_slice_len bk_s q bs :
  updates_slice' q bk_s bs -∗ ⌜uint.Z bk_s.(Slice.sz) = length bs⌝.
Proof.
  iIntros "Hupds".
  iDestruct (updates_slice_frag_acc with "Hupds") as "[Hupds _]".
  iDestruct (updates_slice_frag_len with "Hupds") as %Hlen.
  auto.
Qed.

Lemma updates_slice_wf bk_s q bs :
  updates_slice' q bk_s bs -∗ ⌜uint.Z bk_s.(Slice.sz) ≤ uint.Z bk_s.(Slice.cap)⌝.
Proof.
  iIntros "Hupds".
  iDestruct (updates_slice_frag_acc with "Hupds") as "[Hupds _]".
  iDestruct (updates_slice_frag_wf with "Hupds") as %Hwf.
  auto.
Qed.

Existing Instance own_slice_small_as_fractional.

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
    ([∗ list] b_upd;upd ∈ bks;v, is_update b_upd (DfracOwn q) upd)
    (λ q, [∗ list] b_upd;upd ∈ bks;v, is_update b_upd (DfracOwn q) upd)%I
    q.
Proof.
  constructor; auto.
  apply _.
Qed.

Global Instance update_into_val : IntoVal (u64 * Slice.t).
Proof.
  refine {| to_val := update_val;
           from_val := λ v, match v with
                            | (#(LitInt a), (slice_v, #()))%V =>
                                match from_val slice_v with
                                | Some s => Some (a, s)
                                | None => None
                                end
                            | _ => None
                            end;
           IntoVal_def := (W64 0, IntoVal_def Slice.t);
         |}.
  destruct v as [a []]; done.
Defined.

Global Instance update_into_val_for_type : IntoValForType (u64 * Slice.t) (uint64T * (blockT * unitT)%ht).
Proof. constructor; simpl; done. Qed.

Instance update_val_inj : Inj eq eq update_val.
Proof.
  intros u1 u2.
  rewrite /update_val.
  destruct u1, u2; simpl.
  destruct t, t0; simpl in *; subst.
  inversion 1; subst.
  congruence.
Qed.

Global Instance updates_slice_frag_fractional bk_s bs :
  fractional.Fractional (λ q, updates_slice_frag bk_s (DfracOwn q) bs).
Proof.
  hnf; intros q1 q2.
  iSplit.
  + iIntros "Hupds".
    iDestruct "Hupds" as (bks) "[Hupds Hbs]".
    iDestruct "Hupds" as "[Hupds1 Hupds2]".
    iDestruct "Hbs" as "[Hbs1 Hbs2]".
    iSplitL "Hupds1 Hbs1".
    * iExists _; iFrame.
    * iExists _; iFrame.
  + iIntros "[Hupds1 Hupds2]".
    iDestruct "Hupds1" as (bks) "[Hbs1 Hupds1]".
    iDestruct "Hupds2" as (bks') "[Hbs2 Hupds2]".
    iDestruct (own_slice_small_agree with "Hbs1 Hbs2") as %Heq.
    apply (list_fmap_eq_inj update_val) in Heq; auto using update_val_inj; subst.
    iCombine "Hbs1 Hbs2" as "Hbs".
    iCombine "Hupds1 Hupds2" as "Hupds".
    iExists _; iFrame.
Qed.

Global Instance updates_slice_frag_as_fractional bk_s q bs :
  fractional.AsFractional (updates_slice_frag bk_s (DfracOwn q) bs) (λ q, updates_slice_frag bk_s (DfracOwn q) bs) q.
Proof. split; auto; apply _. Qed.

Global Instance updates_slice_frag_AsMapsTo bk_s bs :
  AsMapsTo (updates_slice_frag bk_s (DfracOwn 1) bs) (λ q, updates_slice_frag bk_s (DfracOwn q) bs).
Proof. constructor; auto; apply _. Qed.

Theorem wp_SliceGet_updates stk E bk_s bs (i: u64) q (u: update.t) :
  {{{ updates_slice_frag bk_s q bs ∗ ⌜bs !! uint.nat i = Some u⌝ }}}
    SliceGet (struct.t Update) (slice_val bk_s) #i @ stk; E
  {{{ uv, RET (update_val uv);
      is_update uv q u ∗
      (is_block uv.2 q u.(update.b) -∗ updates_slice_frag bk_s q bs)
  }}}.
Proof.
  iIntros (Φ) "[Hupds %Hlookup] HΦ".
  iDestruct "Hupds" as (bks) "[Hbk_s Hbks]".
  iDestruct (big_sepL2_lookup_2_some _ _ _ _ _ Hlookup with "Hbks")
    as %[b_upd Hlookup_bs].
  wp_apply (wp_SliceGet with "[$Hbk_s]").
  { iPureIntro.
    rewrite list_lookup_fmap.
    rewrite Hlookup_bs //. }
  iIntros "[Hbk_s _]".
  iApply "HΦ".
  iDestruct (big_sepL2_lookup_acc with "Hbks") as "[Hbi Hbks]"; eauto.
  destruct u as [a b]; simpl.
  iDestruct "Hbi" as "[%Heq Hbi]".
  iSplitL "Hbi".
  { by iFrame. }
  iIntros "Hbi".
  iSpecialize ("Hbks" with "[$Hbi //]").
  iExists _; iFrame.
Qed.

Theorem wp_SliceSet_updates stk E bk_s q_b bs (i: u64) (u0 u: update.t) uv :
  bs !! uint.nat i = Some u0 ->
  {{{ updates_slice_frag' bk_s (DfracOwn 1) q_b bs ∗ is_update uv q_b u }}}
    SliceSet (struct.t Update) (slice_val bk_s) #i (update_val uv) @ stk; E
  {{{ RET #(); updates_slice_frag' bk_s (DfracOwn 1) q_b (<[uint.nat i := u]> bs)
  }}}.
Proof.
  iIntros (Hlookup Φ) "[Hupds Hu] HΦ".
  iDestruct "Hupds" as (bks) "[Hbk_s Hbks]".
  iDestruct (big_sepL2_length with "Hbks") as %Hlen.
  assert (exists uv0, bks !! uint.nat i = Some uv0) as [uv0 Hlookup_bks].
  { apply lookup_lt_Some in Hlookup.
    apply list_lookup_lt.
    lia. }
  iDestruct (big_sepL2_insert_acc _ _ _ _ _ _ Hlookup_bks Hlookup with "Hbks")
    as "[Hbki Hbks]".
  wp_apply (wp_SliceSet with "[$Hbk_s]").
  { iPureIntro.
    split; last val_ty.
    rewrite list_lookup_fmap.
    apply fmap_is_Some.
    eauto. }
  iIntros "Hbk_s".
  iApply "HΦ".
  iSpecialize ("Hbks" with "[$Hu //]").
  rewrite -list_fmap_insert.
  iExists _; iFrame.
Qed.

Theorem wp_SliceSet_updates' stk E bk_s q_b bs (i: u64) (u0 u: update.t) uv :
  bs !! uint.nat i = Some u0 ->
  {{{ updates_slice_frag' bk_s (DfracOwn 1) q_b bs ∗ is_update uv q_b u }}}
    SliceSet (struct.t Update) (slice_val bk_s) #i (update_val uv) @ stk; E
  {{{ RET #(); updates_slice_frag' bk_s (DfracOwn 1) q_b (<[uint.nat i := u]> bs)
  }}}.
Proof.
  iIntros (Hlookup Φ) "[Hupds Hu] HΦ".
  iDestruct "Hupds" as (bks) "[Hbk_s Hbks]".
  iDestruct (big_sepL2_length with "Hbks") as %Hlen.
  assert (exists uv0, bks !! uint.nat i = Some uv0) as [uv0 Hlookup_bks].
  { apply lookup_lt_Some in Hlookup.
    apply list_lookup_lt.
    lia. }
  iDestruct (big_sepL2_insert_acc _ _ _ _ _ _ Hlookup_bks Hlookup with "Hbks")
    as "[Hbki Hbks]".
  wp_apply (wp_SliceSet with "[$Hbk_s]").
  { iPureIntro.
    split; auto.
    rewrite list_lookup_fmap.
    apply fmap_is_Some.
    eauto. }
  iIntros "Hbk_s".
  iApply "HΦ".
  iSpecialize ("Hbks" with "[$Hu //]").
  rewrite -list_fmap_insert.
  iExists _; iFrame.
Qed.

Lemma has_zero_update : has_zero (struct.t Update).
Proof.
  repeat constructor.
Qed.

Hint Resolve has_zero_update : core.

Theorem wp_SliceAppend_updates {stk E bk_s q bs} {uv: u64 * Slice.t} {b} :
  {{{ updates_slice' q bk_s bs ∗ is_block uv.2 q b }}}
    SliceAppend (struct.t Update) (slice_val bk_s) (update_val uv) @ stk; E
  {{{ bk_s', RET slice_val bk_s';
      updates_slice' q bk_s' (bs ++ [update.mk uv.1 b])
  }}}.
Proof.
  iIntros (Φ) "[Hupds Hub] HΦ".
  iDestruct (updates_slice_len with "Hupds") as %Hlen.
  iDestruct "Hupds" as (bks) "[Hbks Hupds]".
  wp_apply (wp_SliceAppend with "[$Hbks]"); auto.
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

Theorem wp_SliceAppend_updates_frag {stk E bk_s bs} {uv: u64 * Slice.t} {b} (n : u64) (q : Qp) (q_b q_b' : dfrac) :
  0 ≤ uint.Z n ≤ uint.Z (Slice.sz bk_s) ≤ uint.Z (Slice.cap bk_s) ->
  (q < 1)%Qp ->
  {{{ updates_slice_frag' (slice_take bk_s n) (DfracOwn q) q_b (take (uint.nat n) bs) ∗
      updates_slice' q_b' (slice_skip bk_s (struct.t Update) n) (drop (uint.nat n) bs) ∗
      is_block uv.2 q_b' b }}}
    SliceAppend (struct.t Update) (slice_val bk_s) (update_val uv) @ stk; E
  {{{ bk_s', RET slice_val bk_s';
      updates_slice_frag' (slice_take bk_s' n) (DfracOwn q) q_b (take (uint.nat n) (bs ++ [update.mk uv.1 b])) ∗
      updates_slice' q_b' (slice_skip bk_s' (struct.t Update) n) (drop (uint.nat n) (bs ++ [update.mk uv.1 b])) ∗
      ⌜uint.Z (Slice.sz bk_s') ≤ uint.Z (Slice.cap bk_s') ∧
       uint.Z (Slice.sz bk_s') = (uint.Z (Slice.sz bk_s) + 1)%Z⌝
  }}}.
Proof.
  iIntros (Hn Hq Φ) "(Hfrag & Hupds & Hub) HΦ".
  iDestruct (updates_slice_frag_len with "Hfrag") as %Hfraglen.
  iDestruct (updates_slice_len with "Hupds") as %Hlen.
  iDestruct "Hfrag" as (bks1) "[Hbks1 Hfrag]".
  iDestruct "Hupds" as (bks2) "[Hbks2 Hupds]".
  wp_apply (wp_SliceAppend'' with "[$Hbks1 $Hbks2]"); auto.
  iIntros (s') "(Hbks1 & Hbks2 & %Hn')".
  iApply "HΦ".
  change ([update_val uv]) with (update_val <$> [uv]).
  rewrite -fmap_app.
  rewrite /updates_slice /updates_slice_frag.
  iSplitL "Hbks1 Hfrag".
  {
    iExists (bks1).
    iFrame "Hbks1".
    rewrite take_app_le; first by iFrame.
    revert Hfraglen.
    rewrite /slice_take /= take_length. word. }
  iSplitL; last by eauto.
  iExists (bks2 ++ [uv]).
  iFrame "Hbks2".
  rewrite drop_app_le.
  2: { revert Hfraglen. rewrite /slice_take /= take_length. word. }
  iApply (big_sepL2_app with "Hupds").
  simpl. auto.
Qed.

Theorem wp_forSlice_updates (I: u64 -> iProp Σ) stk E s q q_b us (body: val) :
  (∀ (i: u64) (uv: u64 * Slice.t) (u: update.t),
      {{{ I i ∗ ⌜(uint.nat i < length us)%nat⌝ ∗
                is_update uv q_b u ∗
                ⌜us !! uint.nat i = Some u⌝ }}}
        body #i (update_val uv) @ stk; E
      {{{ RET #(); I (word.add i (W64 1)) ∗
                   is_block uv.2 q_b u.(update.b) }}}) -∗
    {{{ I (W64 0) ∗ updates_slice_frag' s q q_b us }}}
      forSlice (struct.t Update) body (slice_val s) @ stk; E
    {{{ RET #(); I s.(Slice.sz) ∗ updates_slice_frag' s q q_b us }}}.
Proof.
  iIntros "#Hwp".
  iIntros "!>" (Φ) "(I0&Hupds) HΦ".
  iDestruct "Hupds" as (bks) "(Hs&Hbs)".
  iDestruct (own_slice_small_sz with "Hs") as %Hslen.
  autorewrite with len in Hslen.
  iDestruct (big_sepL2_length with "Hbs") as %Hlen_eq.
  wp_apply (wp_forSlice
              (fun i => I i ∗
               [∗ list] b_upd;upd ∈ bks;us, is_update b_upd q_b upd)%I
    with "[] [$I0 $Hs $Hbs]").
  {
    clear Φ.
    iIntros (i x).
    iIntros "!>" (Φ) "[(HI&Hbs) %] HΦ".
    destruct H as [Hbound Hlookup].
    rewrite list_lookup_fmap in Hlookup.
    apply fmap_Some_1 in Hlookup as [uv [Hlookup ->]].
    list_elem us i as u.
    iDestruct (big_sepL2_lookup_acc with "Hbs") as "[[% Hb] Hbs]"; eauto.
    wp_apply ("Hwp" with "[$HI $Hb]").
    - iPureIntro.
      split; auto.
      word.
    - iIntros "(HI&Hb)".
      iSpecialize ("Hbs" with "[$Hb //]").
      iApply ("HΦ" with "[$]").
  }
  iIntros "[(HI&Hbs) Hs]".
  iApply "HΦ".
  iFrame.
Qed.

Theorem wp_forSlice_updates_consume {stk E}
        (I: u64 -> iProp Σ) s q q_b us (body: val) :
  (∀ (i: u64) (uv: u64 * Slice.t) (u: update.t),
      {{{ I i ∗ ⌜(uint.nat i < length us)%nat⌝ ∗
                is_update uv q_b u ∗
                ⌜us !! uint.nat i = Some u⌝ }}}
        body #i (update_val uv) @ stk; E
      {{{ RET #(); I (word.add i (W64 1)) }}}) -∗
    {{{ I (W64 0) ∗ updates_slice_frag' s q q_b us }}}
      forSlice (struct.t Update) body (slice_val s) @ stk; E
    {{{ RET #(); I s.(Slice.sz) }}}.
Proof.
  iIntros "#Hwp".
  iIntros "!>" (Φ) "(I0&Hupds) HΦ".
  iDestruct "Hupds" as (bks) "(Hs&Hbs)".
  iDestruct (own_slice_small_sz with "Hs") as %Hslen.
  autorewrite with len in Hslen.
  iDestruct (big_sepL2_length with "Hbs") as %Hlen_eq.
  wp_apply (wp_forSlice
              (fun i => I i ∗
                       [∗ list] b_upd;upd ∈ (drop (uint.nat i) bks);(drop (uint.nat i) us),
                                            is_update b_upd q_b upd)%I
              with "[] [$I0 $Hs $Hbs]").
  {
    clear Φ.
    iIntros (i x).
    iIntros "!>" (Φ) "[(HI&Hbs) %] HΦ".
    destruct H as [Hbound Hlookup].
    rewrite list_lookup_fmap in Hlookup.
    apply fmap_Some_1 in Hlookup as [uv [Hlookup ->]].
    list_elem us i as u.
    erewrite (drop_S bks); eauto.
    erewrite (drop_S us); eauto.
    simpl.
    iDestruct "Hbs" as "[[% Hb] Hbs]".
    wp_apply ("Hwp" with "[$HI $Hb]").
    - iPureIntro.
      split; auto.
      word.
    - iIntros "HI".
      iApply "HΦ".
      iFrame.
      iExactEq "Hbs".
      repeat (f_equal; try word).
  }
  iIntros "[(HI&Hbs) Hs]".
  iApply "HΦ".
  iFrame.
Qed.

(* TODO(tej): not actually used *)
Theorem wp_forSlicePrefix_updates (I: list update.t -> list update.t -> iProp Σ) stk E s q us (body: val) :
  (∀ (i: u64) (uv: u64 * Slice.t) (u: update.t) (upds upds': list update.t),
      {{{ I upds (u :: upds') ∗
            is_update uv q u ∗
            ⌜(uint.nat i < length us)%nat⌝ ∗
            ⌜us !! uint.nat i = Some u⌝ ∗
            ⌜upds ++ u :: upds' = us⌝ ∗
            ⌜length upds = uint.nat i⌝ }}}
        body #i (update_val uv) @ stk; E
      {{{ RET #(); I (upds ++ [u]) upds' ∗
                   is_block uv.2 q u.(update.b) }}}) -∗
    {{{ I [] us ∗ updates_slice_frag s q us }}}
      forSlice (struct.t Update) body (slice_val s) @ stk; E
    {{{ RET #(); I us [] ∗ updates_slice_frag s q us }}}.
Proof.
  iIntros "#Hwp".
  iIntros "!>" (Φ) "[HI Hupds] HΦ".
  iDestruct (updates_slice_frag_len with "Hupds") as %Hsz.
  wp_apply (wp_forSlice_updates
              (λ i, I (take (uint.nat i) us) (drop (uint.nat i) us))
              with "[] [$HI $Hupds]").
  {
    clear Φ.
    iIntros (i uv u) "!>".
    iIntros (Φ) "(HI&%&Hu&%) HΦ".
    wp_apply ("Hwp" with "[HI $Hu]").
    { rewrite (drop_S _ _ _ H0). iFrame.
      iPureIntro.
      split_and!; auto; len.
      rewrite take_drop_middle; auto.
    }
    iIntros "(HI&Hu)".
    iApply "HΦ"; iFrame.
    iExactEq "HI".
    f_equal; auto.
    - apply take_S_r in H0. rewrite -H0. f_equal. word.
    - f_equal; word.
  }
  rewrite -> take_ge, drop_ge by word.
  iFrame.
Qed.

Theorem wp_forSlicePrefix_updates_consume {stk E}
        (I: list update.t -> list update.t -> iProp Σ)
        s q q_b us (body: val) :
  (∀ (i: u64) (uv: u64 * Slice.t) (u: update.t) (upds upds': list update.t),
      {{{ I upds (u :: upds') ∗
            is_update uv q_b u ∗
            ⌜(uint.nat i < length us)%nat⌝ ∗
            ⌜us !! uint.nat i = Some u⌝ ∗
            ⌜upds ++ u :: upds' = us⌝ ∗
            ⌜length upds = uint.nat i⌝ }}}
        body #i (update_val uv) @ stk; E
      {{{ RET #(); I (upds ++ [u]) upds' }}}) -∗
    {{{ I [] us ∗ updates_slice_frag' s q q_b us }}}
      forSlice (struct.t Update) body (slice_val s) @ stk; E
    {{{ RET #(); I us [] }}}.
Proof.
  iIntros "#Hwp".
  iIntros "!>" (Φ) "[HI Hupds] HΦ".
  iDestruct (updates_slice_frag_len with "Hupds") as %Hsz.
  wp_apply (wp_forSlice_updates_consume
              (λ i, I (take (uint.nat i) us) (drop (uint.nat i) us))
              with "[] [$HI $Hupds]").
  {
    clear Φ.
    iIntros (i uv u) "!>".
    iIntros (Φ) "(HI&%&Hu&%) HΦ".
    wp_apply ("Hwp" with "[HI $Hu]").
    { rewrite (drop_S _ _ _ H0). iFrame.
      iPureIntro.
      split_and!; auto; len.
      rewrite take_drop_middle; auto.
    }
    iIntros "HI".
    iApply "HΦ"; iFrame.
    iExactEq "HI".
    f_equal; auto.
    - apply take_S_r in H0. rewrite -H0. f_equal. word.
    - f_equal; word.
  }
  rewrite -> take_ge, drop_ge by word.
  iFrame.
Qed.

Theorem wp_copyUpdateBlock stk E (u: u64 * Slice.t) q b :
  {{{ is_block (snd u) q b }}}
    copyUpdateBlock (update_val u) @ stk; E
  {{{ (s':Slice.t), RET (slice_val s'); is_block (snd u) q b ∗ is_block s' (DfracOwn 1) b }}}.
Proof.
  iIntros (Φ) "Hb HΦ".
  destruct u as [a s]; simpl.
  wp_call.
  wp_apply (util_proof.wp_CloneByteSlice with "Hb").
  iIntros (s') "(Hb&Hb')".
  iDestruct (own_slice_to_small with "Hb'") as "Hb'".
  iApply ("HΦ" with "[$]").
Qed.

End heap.
