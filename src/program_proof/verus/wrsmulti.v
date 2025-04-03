From Perennial.program_proof Require Import disk_prelude.
From Perennial.program_proof Require Import disk_lib std_proof.
From Goose Require github_com.goose_lang.std.

(*
package wrs

import (
	"github.com/goose-lang/goose/machine/disk"
	"github.com/goose-lang/std"
)

func WriteMulti(d disk.Disk, a uint64, vs [][]byte) {
	var off uint64

	for off < uint64(len(vs)) {
		d.Write(std.SumAssumeNoOverflow(a, off), vs[off])
		off = std.SumAssumeNoOverflow(off, 1)
	}
}
*)

Definition WriteMulti: val :=
  rec: "WriteMulti" "d" "a" "vs" :=
    let: "off" := ref (zero_val uint64T) in
    Skip;;
    (for: (λ: <>, (![uint64T] "off") < (slice.len "vs")); (λ: <>, Skip) := λ: <>,
      disk.Write (std.SumAssumeNoOverflow "a" (![uint64T] "off")) (SliceGet (slice.T byteT) "vs" (![uint64T] "off"));;
      "off" <-[uint64T] (std.SumAssumeNoOverflow (![uint64T] "off") #1);;
      Continue);;
    #().

Section proof.

Context `{!heapGS Σ}.
Context `{!stagedG Σ}.

Theorem wpc_Write stk E1 (a: u64) s q b b0 :
  {{{ uint.Z a d↦ b0 ∗ is_block s q b }}}
    disk.Write #a (slice_val s) @ stk; E1
  {{{ RET #(); uint.Z a d↦ b ∗ is_block s q b }}}
  {{{ uint.Z a d↦ b0 ∨ uint.Z a d↦ b }}}.
Proof.
  iIntros (Φ Φc) "Hpre HΦ".
  iDestruct "Hpre" as "[Hda Hs]".
  wpc_apply (wpc_Write' with "[$Hda $Hs]").
  iSplit.
  { iLeft in "HΦ". iIntros "[Hda|Hda]"; iApply "HΦ"; eauto. }
  iIntros "!> [Hda Hb]".
  iRight in "HΦ".
  iApply "HΦ"; iFrame.
Qed.

Theorem wpc_WriteMulti d (a : u64) s q (bslices : list Slice.t) bs bs0 stk E1 :
  {{{ own_slice_small s (slice.T byteT) q (slice_val <$> bslices) ∗
      ([∗ list] bslice;b ∈ bslices;bs, own_slice_small bslice byteT q (Block_to_vals b)) ∗
      ([∗ list] i ↦ b0 ∈ bs0, (uint.Z a + i) d↦ b0) ∗
      ⌜ length bs = length bs0 ⌝
  }}}
    WriteMulti #d #a (slice_val s) @ stk; E1
  {{{ RET #();
      own_slice_small s (slice.T byteT) q (slice_val <$> bslices) ∗
      ([∗ list] bslice;b ∈ bslices;bs, own_slice_small bslice byteT q (Block_to_vals b)) ∗
      ([∗ list] i ↦ b ∈ bs, (uint.Z a + i) d↦ b)
  }}}
  {{{ ∃ crashidx,
      [∗ list] i ↦ b ∈ (firstn crashidx bs ++ skipn crashidx bs0), (uint.Z a + i) d↦ b
  }}}.
Proof.
  iIntros (Φ Φc) "(Hss & Hs & Hb & %Hlen) HΦ".
  wpc_call.
  { iExists 0%nat. rewrite take_0 drop_0 app_nil_l. iFrame. }
  { iExists 0%nat. rewrite take_0 drop_0 app_nil_l. iFrame. }
  iCache with "HΦ Hb".
  { crash_case.
    iExists 0%nat. rewrite take_0 drop_0 app_nil_l. iFrame. }
  wpc_pures.
  wpc_frame_seq.
  wp_apply wp_ref_of_zero.
  { done. }
  iIntros (off) "Hoff".
  iNamed 1.
  wpc_pures.
  replace (zero_val uint64T) with (#0) by reflexivity.
  iAssert (∃ idx, off ↦[uint64T] #(W64 idx) ∗
       ⌜ 0 ≤ idx < 2^64 ⌝ ∗
       [∗ list] i↦b ∈ (take (Z.to_nat idx) bs ++ drop (Z.to_nat idx) bs0), (uint.Z a + i) d↦ b)%I with "[Hoff Hb]" as "Hdisk".
  { iExists 0. iFrame. iPureIntro. lia. }
  wpc_apply (wpc_forBreak_cond_2 with "[-]").
  { iNamedAccu. }
  { iNamed 1.
    crash_case.
    iDestruct "Hdisk" as (idx) "(Hoff & %Hbound & Hdisk)".
    iFrame. }
  iIntros "!# __CTX"; iNamed "__CTX".
  iDestruct "Hdisk" as (idx) "(Hoff & %Hbound & Hdisk)".
  iCache with "HΦ Hdisk".
  { crash_case. iFrame. }
  wpc_pures.
  wpc_bind (load_ty _ _). wpc_frame. wp_load. iModIntro. iNamed 1.
  wpc_bind (slice.len s). wpc_frame. wp_apply (wp_slice_len). iNamed 1.
  wpc_pures.
  iDestruct (own_slice_small_sz with "Hss") as "%Hslicesz".
  iDestruct (big_sepL2_length with "Hs") as "%Hlen2".
  rewrite length_fmap in Hslicesz.
  wpc_if_destruct.
  - wpc_pures.
    edestruct (list_lookup_lt bslices (Z.to_nat idx)); first by word.
    wpc_bind (SliceGet _ _ _). wpc_frame. wp_load.
    wp_apply (wp_SliceGet with "[$Hss]").
    { iPureIntro. rewrite list_lookup_fmap. replace (uint.nat (W64 idx)) with (Z.to_nat idx) by word. rewrite H //. }
    iIntros "[Hss %Hvalty]". iNamed 1.
    wpc_bind (load_ty _ _). wpc_frame. wp_load. iModIntro. iNamed 1.
    wpc_pures.
    wpc_bind (std.SumAssumeNoOverflow _ _). wpc_frame.
    wp_apply (wp_SumAssumeNoOverflow). iIntros "%Hoverflow". iNamed 1.

    edestruct (list_lookup_lt bs (Z.to_nat idx)); first by word.
    edestruct (list_lookup_lt (take (Z.to_nat idx) bs ++ drop (Z.to_nat idx) bs0) (Z.to_nat idx)).
    { rewrite length_app length_drop -Hlen -length_drop -length_app take_drop. word. }
    iDestruct (big_sepL2_lookup_acc with "Hs") as "[Hblk Hs]"; eauto.
    iDestruct (big_sepL_insert_acc with "[Hdisk]") as "[Hdiskblk Hdisk]"; eauto.

    wpc_apply (wpc_Write with "[Hblk Hdiskblk]").
    { nat_cleanup. replace (uint.Z (word.add _ _)) with (uint.Z a + idx) by word. iFrame. }
    rewrite Hoverflow.

    iSplit.
    { iIntros "Hdiskblk". iLeft in "HΦ". iApply "HΦ".
      iDestruct "Hdiskblk" as "[Hdiskblk | Hdiskblk]".
      + iDestruct ("Hdisk" with "[Hdiskblk]") as "Hdisk".
        { iExactEq "Hdiskblk". f_equal. word. }
        rewrite list_insert_id; eauto.
      + iDestruct ("Hdisk" with "[Hdiskblk]") as "Hdisk".
        { iExactEq "Hdiskblk". f_equal. word. }
        iExists (Z.to_nat idx + 1)%nat.
        iExactEq "Hdisk". f_equal.
        rewrite insert_take_drop.
        2: { rewrite length_app length_drop -Hlen -length_drop -length_app take_drop. word. }
        rewrite take_app_le.
        2: { rewrite length_take. word. }
        rewrite take_idemp.
        rewrite drop_app_ge.
        2: { rewrite length_take. word. }
        rewrite length_take_le.
        2: { word. }
        rewrite drop_drop.
        rewrite cons_middle.
        rewrite app_assoc. f_equal.
        2: { f_equal. lia. }
        rewrite -take_S_r; eauto.
        f_equal. lia.
    }

    iModIntro. iIntros "[Hdiskblk Hblk]".
    iDestruct ("Hdisk" with "[Hdiskblk]") as "Hdisk".
    { iExactEq "Hdiskblk"; f_equal; word. }

    iCache with "HΦ Hdisk".
    { crash_case.
        iExists (Z.to_nat idx + 1)%nat.
        iExactEq "Hdisk". f_equal.
        rewrite insert_take_drop.
        2: { rewrite length_app length_drop -Hlen -length_drop -length_app take_drop. word. }
        rewrite take_app_le.
        2: { rewrite length_take. word. }
        rewrite take_idemp.
        rewrite drop_app_ge.
        2: { rewrite length_take. lia. }
        rewrite length_take_le.
        2: { word. }
        rewrite drop_drop.
        rewrite cons_middle.
        rewrite app_assoc. f_equal.
        2: { f_equal. lia. }
        rewrite -take_S_r; eauto.
        f_equal. lia.
    }
    wpc_pures.
    wpc_bind (store_ty _ _). wpc_frame.
    wp_load. wp_apply (wp_SumAssumeNoOverflow). iIntros "%Hoverflow2". wp_store. iModIntro. iNamed 1.

    iDestruct ("Hs" with "Hblk") as "Hs".
    wpc_pures. iModIntro.
    iLeft. iFrame. iSplit; first done. iExists (idx + 1). iSplitL "Hoff".
    { iExactEq "Hoff". f_equal. f_equal. f_equal. word. }
    iSplitR.
    { word. }

        iExactEq "Hdisk". f_equal.
        rewrite insert_take_drop.
        2: { rewrite length_app length_drop -Hlen -length_drop -length_app take_drop. word. }
        rewrite take_app_le.
        2: { rewrite length_take. word. }
        rewrite take_idemp.
        rewrite drop_app_ge.
        2: { rewrite length_take. lia. }
        rewrite length_take_le.
        2: { word. }
        rewrite drop_drop.
        rewrite cons_middle.
        rewrite app_assoc. f_equal.
        2: { f_equal. lia. }
        rewrite -take_S_r; eauto.
        f_equal. lia.

  - wpc_pures. iModIntro.
    iRight. iSplitR; first by done.
    iSplit.
    2: { crash_case. iFrame. }
    wpc_pures. iModIntro.
    iRight in "HΦ". iApply "HΦ".
    iFrame.
    rewrite take_ge.
    2: word.
    rewrite drop_ge.
    2: word.
    rewrite app_nil_r. iFrame.
Qed.

(**
 * Write-restricted storage in Verus:
 *
 *   precondition of serialize_and_write:
 *   https://github.com/microsoft/verified-storage/blob/main/storage_node/src/pmem/wrpm_t.rs
 *
 *   example of a Permission object (check_permission):
 *   https://github.com/microsoft/verified-storage/blob/main/storage_node/src/log/logimpl_t.rs
 *)

Definition disk_state := gmap Z Block.
Definition own_disk (d : disk_state) : iProp Σ :=
  [∗ map] a↦v ∈ d, a d↦ v.

(* P is the equivalent of the opaque check_permission from write-restricted storage *)
Axiom P : disk_state -> iProp Σ.

(* Simplified version of write().can_crash_as() *)
Fixpoint write_blocks (d : disk_state) (a : Z) (blocks : list Block) : disk_state :=
  match blocks with
  | nil => d
  | b :: blocks' => <[a:=b]> (write_blocks d (a+1) blocks')
  end.

Lemma write_blocks_app : ∀ (bs0 bs1 : list Block) (d : disk_state) (a : Z),
  write_blocks d a (bs0 ++ bs1) = write_blocks (write_blocks d (a + length bs0) bs1) a bs0.
Proof.
  induction bs0; intros.
  - simpl. replace (a+0%nat) with a by lia. done.
  - simpl. f_equal.
    rewrite IHbs0. f_equal.
    f_equal. lia.
Qed.

Lemma write_blocks_le : ∀ (bs : list Block) (d : disk_state) (a a' : Z),
  a' < a ->
  write_blocks d a bs !! a' = d !! a'.
Proof.
  induction bs; simpl; intros; eauto.
  rewrite lookup_insert_ne; last by lia.
  apply IHbs. lia.
Qed.

Lemma write_blocks_idem : ∀ (bs : list Block) (d : disk_state) (a : Z),
  (∀ (i : nat) b, bs !! i = Some b -> d !! (a + i) = Some b) ->
  write_blocks d a bs = d.
Proof.
  induction bs; intros.
  - simpl; done.
  - simpl. rewrite insert_id.
    + rewrite IHbs; eauto. intros.
      replace (a0 + 1 + i) with (a0 + (S i)) by lia. erewrite H; eauto.
    + rewrite write_blocks_le; last by lia.
      replace (a0) with (a0 + 0%nat) by lia. apply H. done.
Qed.

Definition write_can_crash_as (d : disk_state) (a : Z) (blocks : list Block) (d' : disk_state) : Prop :=
  ∃ blocks',
    prefix blocks' blocks ∧
    write_blocks d a blocks' = d'.

Fixpoint block_list_to_gmap (a : Z) (vs : list Block) : gmap Z Block :=
  match vs with
  | [] => ∅
  | v :: vs' => {[a := v]} ∪ block_list_to_gmap (a + 1)%Z vs'
  end.

Lemma block_list_to_gmap_lookup l (vs: list Block) w k :
  block_list_to_gmap l vs !! k = Some w ↔
                              ∃ j, 0 ≤ j ∧ k = l + j ∧ vs !! (Z.to_nat j) = Some w.
Proof.
  revert k l; induction vs as [|v' vs IH]=> l' l /=.
  { rewrite lookup_empty. naive_solver lia. }
  rewrite -insert_union_singleton_l lookup_insert_Some IH. split.
  - intros [[-> Heq] | (Hl & j & ? & -> & ?)].
    { inversion Heq; subst. exists 0. naive_solver lia. }
    exists (1 + j)%Z. split; first by lia. split; first by lia.
    rewrite Z.add_1_l Z2Nat.inj_succ; auto.
  - intros (j & ? & -> & Hil). destruct (decide (j = 0)); simplify_eq/=.
    { left; split; eauto; lia. }
    right. split.
    { lia. }
    assert (Z.to_nat j = S (Z.to_nat (j - 1))) as Hj.
    { rewrite -Z2Nat.inj_succ; last lia. f_equal; lia. }
    rewrite Hj /= in Hil.
    exists (j - 1)%Z. intuition lia.
Qed.

Lemma block_list_to_gmap_disjoint (h : gmap Z Block) (a : Z) (vs : list Block) :
  (∀ i, (0 ≤ i) → (i < length vs) → h !! (a + i) = None) →
  (block_list_to_gmap a vs) ##ₘ h.
Proof.
  intros Hdisj. apply map_disjoint_spec=> l' v1 v2.
  intros (j&?&->&Hj%lookup_lt_Some%inj_lt)%block_list_to_gmap_lookup.
  move: Hj. rewrite Z2Nat.id // => ?. by rewrite Hdisj.
Qed.

Lemma big_sep_block_list_to_gmap (a : Z) (vs: list Block) (P: Z -> Block -> iProp Σ) :
  ([∗ map] l↦v ∈ block_list_to_gmap a vs, P l v) ⊣⊢
  ([∗ list] i↦v ∈ vs, P (a + i)%Z v).
Proof.
  (iInduction (vs) as [| v vs] "IH" forall (a)).
  - simpl.
    rewrite big_sepM_empty.
    auto.
  - simpl.
    rewrite big_sepM_union.
    { rewrite big_sepM_singleton.
      replace (a + 0%nat) with a by lia.
      iSpecialize ("IH" $! (a + 1)).
      iSplit.
      + iIntros "($&Hm)".
        iDestruct ("IH" with "Hm") as "Hm".
        iApply (big_sepL_mono with "Hm"). intros. iIntros "H". replace (a + 1 + k) with (a + S k) by lia. done.
      + iIntros "($&Hl)".
        iApply "IH".
        iApply (big_sepL_mono with "Hl"). intros. iIntros "H". replace (a + 1 + k) with (a + S k) by lia. done.
    }
    symmetry.
    apply block_list_to_gmap_disjoint; intros.
    apply (not_elem_of_dom (D := gset Z)).
    rewrite dom_singleton elem_of_singleton. lia.
Qed.


Lemma disk_extract_acc (ds : disk_state) (a : Z) (bs : list Block) :
  own_disk ds -∗
  ( [∗ list] i ↦ _ ∈ bs, ⌜(a+i)%Z ∈ dom ds⌝ ) -∗
  ( [∗ list] i ↦ _ ∈ bs, ∃ b0, (a+i)%Z d↦b0 ∗ ⌜ds !! (a+i)%Z = Some b0⌝ ) ∗
  ( ∀ bs', ⌜length bs' = length bs⌝ -∗ ( [∗ list] i ↦ b ∈ bs', (a+i) d↦b ) -∗
    own_disk (write_blocks ds a bs') ).
Proof.
  iIntros "Hdisk #Hbs_dom".
  rewrite /own_disk /disk_state.
  iDestruct (big_sep_block_list_to_gmap a bs (λ a b, ⌜a ∈ dom ds⌝)%I with "Hbs_dom") as "#Hbs_dom_2".
  replace ds with (filter (λ kv, a ≤ fst kv < a + length bs) ds ∪ filter (λ kv, ¬ (a ≤ fst kv < a + length bs)) ds) at 1.
  2: { rewrite map_filter_union_complement //. }
  iDestruct (big_sepM_union with "Hdisk") as "[Hbs Hdisk]".
  { apply map_disjoint_filter_complement. }
  iSplitL "Hbs".
  { admit. }
  iIntros (bs' Hbslen) "Hbs'".
  admit.
Admitted.

(*
Theorem wpc_WriteMulti_wrs d (a : u64) s q (bslices : list Slice.t) (bs : list Block) ds stk E1 :
  {{{ own_slice_small s (slice.T byteT) q (slice_val <$> bslices) ∗
      ([∗ list] i ↦ bslice;b ∈ bslices;bs, own_slice_small bslice byteT q (Block_to_vals b) ∗ ⌜(uint.Z a + uint.Z i)%Z ∈ dom ds⌝) ∗
      own_disk ds ∗ P ds ∗
      (∀ ds',
        ⌜write_can_crash_as ds (uint.Z a) bs ds'⌝ -∗
        P ds ==∗ P ds')
  }}}
    WriteMulti #d #a (slice_val s) @ stk; E1
  {{{ RET #();
      own_slice_small s (slice.T byteT) q (slice_val <$> bslices) ∗
      ([∗ list] i ↦ bslice;b ∈ bslices;bs, own_slice_small bslice byteT q (Block_to_vals b) ∗ ⌜(uint.Z a + uint.Z i)%Z ∈ dom ds⌝) ∗
      own_disk (write_blocks ds (uint.Z a) bs) ∗ P (write_blocks ds (uint.Z a) bs)
  }}}
  {{{ ∃ crash_disk, own_disk crash_disk ∗ P crash_disk }}}.
Proof.
  iIntros (Φ Φc) "(Hss & Hs & Hdisk & HP & Hwrs) HΦ".
  iDestruct (big_sepL2_sep with "Hs") as "[Hs #Hdom]".
  iDestruct (big_sepL2_const_sepL_r with "Hdom") as "[%Hlen Hdom_bs]".
  iDestruct (disk_extract_acc with "Hdisk Hdom_bs") as "[Hbs0 Hdisk]".
  iDestruct (big_sepL_exists_to_sepL2 with "Hbs0") as (bs0) "Hbs0".
  iDestruct (big_sepL2_const_sepL_r with "Hbs0") as "[%Hlen0 Hbs0]".
  iDestruct (big_sepL_sep with "Hbs0") as "[Hbs0 #Hbs_ds]".
  iApply (wpc_WriteMulti with "[$Hss $Hs $Hbs0]").
  { done. }
  iSplit.
  - iIntros "Hc". iDestruct "Hc" as (crashidx) "Hc".
    iLeft in "HΦ". iApply "HΦ".
    iDestruct ("Hdisk" with "Hc") as "Hdisk".
    iExists _; iFrame. iApply "Hwrs". 2: iFrame.
    iDestruct "Hbs_ds" as "%Hbs_ds".
    iPureIntro. eexists (take crashidx bs). split.
    + apply prefix_take.
    + rewrite write_blocks_app. f_equal.
      rewrite write_blocks_idem; eauto.
      intros.
      rewrite lookup_drop in H.
      assert (crashidx < length bs).
      { apply lookup_lt_Some in H. lia. }
      rewrite length_take_le; last by lia.
      specialize (Hbs_ds (crashidx + i)%nat b H). rewrite -Hbs_ds. f_equal. lia.
  - iModIntro. iIntros "(Hss & Hs & Hd)".
    iRight in "HΦ". iApply "HΦ". iFrame.
    iDestruct (big_sepL2_sep with "[$Hs $Hdom]") as "Hs". iFrame.
    iDestruct ("Hdisk" with "Hd") as "Hdisk". iFrame.
    iApply "Hwrs". 2: iFrame.
    iPureIntro. eexists _; eauto.
Qed.
*)

End proof.
