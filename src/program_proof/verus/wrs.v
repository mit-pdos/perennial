From Perennial.program_proof Require Import disk_prelude.
From Perennial.program_proof Require Import disk_lib std_proof.
From Goose Require github_com.goose_lang.std.

(**
 * This file tries to prove soundness for a write-restricted-storage API,
 * which helps express crash-safety without explicit support for WPCs or
 * crash semantics.
 *)

(* ~/go/bin/goose ~/wrs *)

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
  rewrite fmap_length in Hslicesz.
  wpc_if_destruct.
  - wpc_pures.
    rewrite Z_u64 in Heqb; last by lia.
    edestruct (list_lookup_lt bslices (Z.to_nat idx)); first by lia.
    wpc_bind (SliceGet _ _ _). wpc_frame. wp_load.
    wp_apply (wp_SliceGet with "[$Hss]").
    { iPureIntro. rewrite list_lookup_fmap. rewrite Z_u64; last by lia. rewrite H. done. }
    iIntros "[Hss %Hvalty]". iNamed 1.
    wpc_bind (load_ty _ _). wpc_frame. wp_load. iModIntro. iNamed 1.
    wpc_pures.
    wpc_bind (std.SumAssumeNoOverflow _ _). wpc_frame.
    wp_apply (wp_SumAssumeNoOverflow). iIntros "%Hoverflow". iNamed 1.

    edestruct (list_lookup_lt bs (Z.to_nat idx)); first by lia.
    edestruct (list_lookup_lt (take (Z.to_nat idx) bs ++ drop (Z.to_nat idx) bs0) (Z.to_nat idx)).
    { rewrite app_length drop_length -Hlen -drop_length -app_length take_drop. lia. }
    iDestruct (big_sepL2_lookup_acc with "Hs") as "[Hblk Hs]"; eauto.
    iDestruct (big_sepL_insert_acc with "[Hdisk]") as "[Hdiskblk Hdisk]"; eauto.

    wpc_apply (wpc_Write with "[Hblk Hdiskblk]").
    { rewrite Hoverflow. word_cleanup. iFrame. }
    rewrite Hoverflow.

    iSplit.
    { iIntros "Hdiskblk". iLeft in "HΦ". iApply "HΦ".
      iDestruct "Hdiskblk" as "[Hdiskblk | Hdiskblk]".
      + iDestruct ("Hdisk" with "[Hdiskblk]") as "Hdisk".
        { word_cleanup. iFrame. }
        rewrite list_insert_id; eauto.
      + iDestruct ("Hdisk" with "[Hdiskblk]") as "Hdisk".
        { word_cleanup. iFrame. }
        iExists (Z.to_nat idx + 1)%nat.
        iExactEq "Hdisk". f_equal.
        rewrite insert_take_drop.
        2: { rewrite app_length drop_length -Hlen -drop_length -app_length take_drop. lia. }
        rewrite take_app_le.
        2: { rewrite take_length. lia. }
        rewrite take_idemp.
        rewrite drop_app_ge.
        2: { rewrite take_length. lia. }
        rewrite take_length_le.
        2: { lia. }
        rewrite drop_drop.
        rewrite cons_middle.
        rewrite app_assoc. f_equal.
        2: { f_equal. lia. }
        rewrite -take_S_r; eauto.
        f_equal. lia.
    }

    iModIntro. iIntros "[Hdiskblk Hblk]".
    iDestruct ("Hdisk" with "[Hdiskblk]") as "Hdisk".
    { word_cleanup. iFrame. }

    iCache with "HΦ Hdisk".
    { crash_case.
        iExists (Z.to_nat idx + 1)%nat.
        iExactEq "Hdisk". f_equal.
        rewrite insert_take_drop.
        2: { rewrite app_length drop_length -Hlen -drop_length -app_length take_drop. lia. }
        rewrite take_app_le.
        2: { rewrite take_length. lia. }
        rewrite take_idemp.
        rewrite drop_app_ge.
        2: { rewrite take_length. lia. }
        rewrite take_length_le.
        2: { lia. }
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
    { iExactEq "Hoff". f_equal. f_equal. f_equal. word_cleanup. }
    iSplitR.
    { iPureIntro. word_cleanup. }

        iExactEq "Hdisk". f_equal.
        rewrite insert_take_drop.
        2: { rewrite app_length drop_length -Hlen -drop_length -app_length take_drop. lia. }
        rewrite take_app_le.
        2: { rewrite take_length. lia. }
        rewrite take_idemp.
        rewrite drop_app_ge.
        2: { rewrite take_length. lia. }
        rewrite take_length_le.
        2: { lia. }
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
    2: { rewrite -Hlen2 Hslicesz. rewrite Z_u64 in Heqb; lia. }
    rewrite drop_ge.
    2: { rewrite -Hlen -Hlen2 Hslicesz. rewrite Z_u64 in Heqb; lia. }
    rewrite app_nil_r. iFrame.
Qed.


(*

Definition own_disk (d : gmap u64 Block) :=
  [∗ map] a↦v ∈ d, 

Theorem wp_Write_wrs a s q b :
  {{{ own_slice_small s byteT q (Block_to_vals b) ∗
      
  }}}
    Write #a (slice_val s)
  {{{ RET #();
      own_slice_small s byteT q (Block_to_vals b) }}}.
Proof.
  

*)

End proof.
