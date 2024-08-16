From Perennial.program_proof Require Import async_disk_prelude.
From Perennial.program_proof Require Import async_disk_lib std_proof.
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
	"github.com/goose-lang/goose/machine"
	"github.com/goose-lang/goose/machine/disk"
)

func Simulate(d disk.Disk, rd func() uint64, wr func() (uint64, []byte)) {
	for {
		r := machine.RandomUint64()

		if r == 0 {
			break
		} else if r == 1 {
			a := rd()
			d.Read(a)
		} else if r == 2 {
			a, b := wr()
			d.Write(a, b)
		} else if r == 3 {
			d.Barrier()
		}
	}
}

*)

Definition Simulate: val :=
  rec: "Simulate" "d" "rd" "wr" :=
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      let: "r" := rand.RandomUint64 #() in
      (if: "r" = #0
      then Break
      else
        (if: "r" = #1
        then
          let: "a" := "rd" #() in
          disk.Read "a";;
          Continue
        else
          (if: "r" = #2
          then
            let: ("a", "b") := "wr" #() in
            disk.Write "a" "b";;
            Continue
          else
            (if: "r" = #3
            then
              disk.Barrier #();;
              Continue
            else Continue)))));;
    #().

Section proof.

Context `{!heapGS Σ}.
Context `{!stagedG Σ}.

Theorem wpc_Write stk E1 (a: u64) s q bp0 b0 b :
  {{{ uint.Z a d↦[bp0] b0 ∗ is_block s q b }}}
    disk.Write #a (slice_val s) @ stk; E1
  {{{ RET #(); ∃ bp, uint.Z a d↦[bp] b ∗ is_block s q b ∗ ⌜bp=b ∨ bp=bp0⌝}}}
  {{{ uint.Z a d↦[bp0] b0 ∨
      uint.Z a d↦[bp0] b ∨
      uint.Z a d↦[b] b }}}.
Proof.
  iIntros (Φ Φc) "Hpre HΦ".
  iDestruct "Hpre" as "[Hda Hs]".
  wpc_apply (wpc_Write' with "[$Hda $Hs]").
  iSplit.
  { iLeft in "HΦ". iIntros "[Hda|Hda]"; iApply "HΦ"; eauto.
    iDestruct "Hda" as (bp) "[%Hbp Hda]".
    destruct Hbp; subst; iFrame. }
  iRight in "HΦ".
  iIntros "!> (%bp & %Hbp & Hda & Hb)".
  iApply "HΦ".
  destruct Hbp; subst; iFrame; eauto.
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
Definition own_disk (dcrash d : disk_state) : iProp Σ :=
  [∗ map] a↦vcrash;v ∈ dcrash;d, a d↦[vcrash] v.

Lemma disk_insert_acc (dcrash d : disk_state) (a : Z) :
  ⌜a ∈ dom d⌝ -∗
  own_disk dcrash d -∗
  ∃ vcrash v,
    a d↦[vcrash] v ∗ ⌜dcrash !! a = Some vcrash⌝ ∗ ⌜d !! a = Some v⌝ ∗
    (∀ vcrash' v',
      a d↦[vcrash'] v' -∗
        own_disk (<[a:=vcrash']> dcrash) (<[a:=v']> d)).
Proof.
  iIntros "%Hdom Hdiskmap".
  iDestruct (big_sepM2_dom with "Hdiskmap") as "%Hdomeq".
  destruct (elem_of_dom d a) as [Hd _]. destruct (Hd Hdom).
  rewrite -Hdomeq in Hdom.
  destruct (elem_of_dom dcrash a) as [Hdcrash _]. destruct (Hdcrash Hdom).
  iDestruct (big_sepM2_insert_acc with "Hdiskmap") as "[Ha Hacc]"; eauto.
  iExists _, _. iFrame. done.
Qed.

Lemma disk_lookup_acc (dcrash d : disk_state) (a : Z) :
  ⌜a ∈ dom d⌝ -∗
  own_disk dcrash d -∗
  ∃ vcrash v,
    a d↦[vcrash] v ∗ ⌜dcrash !! a = Some vcrash⌝ ∗ ⌜d !! a = Some v⌝ ∗
    (a d↦[vcrash] v -∗
      own_disk dcrash d).
Proof.
  iIntros "%Hdom Hdiskmap".
  iDestruct (disk_insert_acc with "[] Hdiskmap") as (vcrash v) "(Ha & %Hclookup & %Hlookup & Hacc)".
  { done. }
  iFrame. iSplit; first done. iSplit; first done.
  iIntros "Ha". iSpecialize ("Hacc" with "Ha").
  rewrite insert_id; eauto.
  rewrite insert_id; eauto.
Qed.

Section WRS.

(* Roughly equivalent to the opaque check_permission from write-restricted storage *)
Parameter P : disk_state -> disk_state -> iProp Σ.
Parameter Pcrash : disk_state -> iProp Σ.
Parameter Pcfupd : ∀ cds ds, P cds ds -∗ |C={⊤}=> Pcrash cds.

Theorem wpc_Simulate cds ds d rd wr stk :
  {{{ "Hd" ∷ own_disk cds ds ∗
      "HP" ∷ P cds ds ∗
      "#Hrd" ∷ {{{ True }}}
                  #rd #() @ stk; ⊤
               {{{ (a:u64), RET #a;
                   "%Ha" ∷ ⌜uint.Z a ∈ dom ds⌝ }}} ∗
      "#Hwr" ∷ {{{ True }}}
                  #wr #() @ stk; ⊤
               {{{ (a:u64) (s:Slice.t) q b, RET (#a, slice_val s);
                   "%Ha" ∷ ⌜uint.Z a ∈ dom ds⌝ ∗
                   "Hb" ∷ is_block s q b ∗
                   "Hwr_fupd" ∷ (∀ cds ds, P cds ds ==∗ P cds (<[uint.Z a := b]> ds) ∧
                                                        P (<[uint.Z a := b]> cds) (<[uint.Z a := b]> ds))
               }}}
  }}}
    Simulate #d #rd #wr @ stk; ⊤
  {{{ RET #(); ∃ cds' ds',
      own_disk cds' ds' ∗
      P cds' ds'
  }}}
  {{{ ∃ cds' ds',
      own_disk cds' ds' ∗
      Pcrash cds'
  }}}.
Proof.
  iIntros (Φ Φc) "H HΦ". iNamed "H".
  iApply wpc_cfupd.
  wpc_call.
  { iIntros "HC". iMod (Pcfupd with "HP HC") as "HP".
    iModIntro. crash_case. iFrame. }
  { iIntros "HC". iMod (Pcfupd with "HP HC") as "HP".
    iModIntro. crash_case. iFrame. }
  iCache with "HΦ Hd HP".
  { iIntros "HC". iMod (Pcfupd with "HP HC") as "HP".
    iModIntro. crash_case. iFrame. }
  wpc_pures.

  iAssert (∃ cds' ds',
    "Hd" ∷ own_disk cds' ds' ∗
    "HP" ∷ P cds' ds' ∗
    "%Hdom'" ∷ ⌜dom ds = dom ds'⌝)%I with "[Hd HP]" as "Hloop".
  { iFrame. done. }

  wpc_apply (wpc_forBreak_cond_2 with "[-]").
  { iNamedAccu. }
  { iNamed 1. iNamed "Hloop".
    iIntros "HC". iMod (Pcfupd with "HP HC") as "HP".
    iModIntro. crash_case. iFrame. }

  iModIntro. iNamed 1.
  iCache with "HΦ Hloop".
  { iNamed "Hloop".
    iIntros "HC". iMod (Pcfupd with "HP HC") as "HP".
    iModIntro. crash_case. iFrame. }

  wpc_pures.
  wpc_frame_seq.
  wp_apply (wp_RandomUint64).
  iIntros (r) "_". iNamed 1.
  wpc_pures.
  wpc_if_destruct.
  {
    wpc_pures.
    iModIntro. iRight. iSplitR; first by done.
    iSplit; last by iFromCache.
    wpc_pures.
    iModIntro. iRight in "HΦ". iApply "HΦ".
    iNamed "Hloop". iFrame.
  }

  wpc_pures.
  wpc_if_destruct.
  {
    wpc_pures.
    wpc_frame_seq.
    wp_apply "Hrd".
    iIntros (a). iNamed 1. iNamed 1. iNamed "Hloop".
    iDestruct (disk_lookup_acc with "[] Hd") as (vcrash v) "(Ha & %Hclookup & %Halookup & Hacc)".
    { rewrite -Hdom'. done. }
    wpc_pures.
    { crash_case.
      iSpecialize ("Hacc" with "Ha").
      iIntros "HC". iMod (Pcfupd with "HP HC") as "HP".
      iModIntro. crash_case. iFrame. }
    wpc_apply (wpc_Read with "Ha").
    iSplit.
    { iIntros "Ha".
      iSpecialize ("Hacc" with "Ha").
      iIntros "HC". iMod (Pcfupd with "HP HC") as "HP".
      iModIntro. crash_case. iFrame. }
    iIntros (s) "!> [Ha Hs]".
    iSpecialize ("Hacc" with "Ha").
    wpc_pures.
    { iIntros "HC". iMod (Pcfupd with "HP HC") as "HP".
      iModIntro. crash_case. iFrame. }
    iModIntro. iLeft. iSplit; first done.
    iFrame. done.
  }

  wpc_pures.
  wpc_if_destruct.
  {
    wpc_pures.
    wpc_frame_seq.
    wp_apply "Hwr".
    iIntros (a s q b). iNamed 1. iNamed 1. iNamed "Hloop".
    iDestruct (disk_insert_acc with "[] Hd") as (vcrash v) "(Ha & %Hclookup & %Halookup & Hacc)".
    { rewrite -Hdom'. done. }
    wpc_pures.
    { iSpecialize ("Hacc" with "Ha"). rewrite ?insert_id //.
      iIntros "HC". iMod (Pcfupd with "HP HC") as "HP".
      iModIntro. crash_case. iFrame. }
    wpc_apply (wpc_Write with "[$Ha $Hb]").
    iSplit.
    { iIntros "Ha". iDestruct "Ha" as "[Ha | [Ha | Ha]]".
      + iSpecialize ("Hacc" with "Ha"). rewrite ?insert_id //.
        iIntros "HC". iMod (Pcfupd with "HP HC") as "HP".
        iModIntro. crash_case. iFrame.
      + iSpecialize ("Hacc" with "Ha"). rewrite insert_id //.
        iIntros "HC". iMod (Pcfupd with "HP HC") as "HP".
        iModIntro. crash_case. iFrame.
      + iSpecialize ("Hacc" with "Ha").
        iIntros "HC". iMod ("Hwr_fupd" with "HP") as "HP". iRight in "HP".
        iMod (Pcfupd with "HP HC") as "HP".
        iModIntro. crash_case. iFrame.
    }
    iModIntro. iIntros "H". iDestruct "H" as (bp) "(Ha & Hb & %Hcrash)".
    iSpecialize ("Hacc" with "Ha").
    iMod ("Hwr_fupd" with "HP") as "HP".
    wpc_pures.
    { destruct Hcrash; subst.
      + iRight in "HP".
        iIntros "HC".
        iMod (Pcfupd with "HP HC") as "HP".
        iModIntro. crash_case. iFrame.
      + rewrite insert_id //.
        iLeft in "HP".
        iIntros "HC".
        iMod (Pcfupd with "HP HC") as "HP".
        iModIntro. crash_case. iFrame.
    }
    iLeft.
    destruct Hcrash; subst.
    + iRight in "HP".
      iModIntro. iSplit; first done. iFrame.
      rewrite dom_insert_L.
      iPureIntro. set_solver.
    + iLeft in "HP". rewrite insert_id //.
      iModIntro. iSplit; first done. iFrame.
      rewrite dom_insert_L.
      iPureIntro. set_solver.
  }

  wpc_pures.
  wpc_if_destruct.
  {
    wpc_pures.
    iNamed "Hloop".
    iDestruct (big_sepM2_alt with "Hd") as "[%Hddom Hdzip]".
    wpc_apply (wpc_Barrier _ _ (map_zip cds' ds') with "Hdzip").
    iSplit.
    { iIntros "Hdzip".
      iIntros "HC". iMod (Pcfupd with "HP HC") as "HP".
      iModIntro. crash_case.
      iExists cds', ds'. iFrame.
      iApply big_sepM2_alt. iFrame. done.
    }
    iIntros "!> [%Hbarrier Hdzip]".
    assert (cds' = ds') as Hdseq.
    { apply map_eq. intro i. specialize (Hbarrier i).
      destruct (cds' !! i) eqn:Hi.
      - assert (i ∈ dom ds') as Hin. { rewrite -Hddom. apply elem_of_dom. eauto. }
        apply elem_of_dom in Hin. destruct Hin as [b' Hin].
        epose proof (map_zip_lookup_some _ _ _ _ _ Hi Hin) as Hz.
        specialize (Hbarrier _ Hz).
        apply map_lookup_zip_Some in Hz. simpl in *; subst. intuition congruence.
      - assert (i ∉ dom ds') as Hin. { rewrite -Hddom. apply not_elem_of_dom. eauto. }
        apply not_elem_of_dom in Hin. rewrite Hi. rewrite Hin. congruence.
    }
    rewrite Hdseq.
    iDestruct (big_sepM2_alt (λ a b c, a d↦[b] c)%I ds' ds' with "[$Hdzip]") as "Hd".
    { eauto. }
    wpc_pures.
    { iIntros "HC". iMod (Pcfupd with "HP HC") as "HP".
      iModIntro. crash_case. iFrame. }
    iModIntro. iLeft. iSplit; first done.
    iFrame. done.
  }

  wpc_pures.
  iModIntro. iLeft. iSplit; first done.
  iFrame.
Qed.

End WRS.

Section WRS_StateMachine.

Parameter State : Type.
Parameter step : State -> State -> Prop.
Parameter abs : disk_state -> State.

(* ... *)

(*
Definition Psm γ :=

*)


(*
      "#Hwr" ∷ {{{ True }}}
                  #wr #() @ stk; ⊤
               {{{ (a:u64) (s:Slice.t) q b, RET (#a, slice_val s);
                   "%Ha" ∷ ⌜uint.Z a ∈ dom ds⌝ ∗
                   "Hb" ∷ is_block s q b ∗
                   "Hwr_fupd" ∷ (∀ cds ds, P cds ds ==∗ P cds (<[uint.Z a := b]> ds) ∧
                                                        P (<[uint.Z a := b]> cds) (<[uint.Z a := b]> ds))
               }}}

  
*)

End WRS_StateMachine.


(*
Theorem wpc_WriteMulti d (a : u64) s q (bslices : list Slice.t) bs (bs0 : list (Block*Block)) stk E1 :
  {{{ own_slice_small s (slice.T byteT) q (slice_val <$> bslices) ∗
      ([∗ list] bslice;b ∈ bslices;bs, own_slice_small bslice byteT q (Block_to_vals b)) ∗
      ([∗ list] i ↦ bp0b0 ∈ bs0, (uint.Z a + i) d↦[fst bp0b0] (snd bp0b0)) ∗
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
    { rewrite length_app length_drop -Hlen -length_drop -length_app take_drop. lia. }
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
        2: { rewrite length_app length_drop -Hlen -length_drop -length_app take_drop. lia. }
        rewrite take_app_le.
        2: { rewrite length_take. lia. }
        rewrite take_idemp.
        rewrite drop_app_ge.
        2: { rewrite length_take. lia. }
        rewrite length_take_le.
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
        2: { rewrite length_app length_drop -Hlen -length_drop -length_app take_drop. lia. }
        rewrite take_app_le.
        2: { rewrite length_take. lia. }
        rewrite take_idemp.
        rewrite drop_app_ge.
        2: { rewrite length_take. lia. }
        rewrite length_take_le.
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
        2: { rewrite length_app length_drop -Hlen -length_drop -length_app take_drop. lia. }
        rewrite take_app_le.
        2: { rewrite length_take. lia. }
        rewrite take_idemp.
        rewrite drop_app_ge.
        2: { rewrite length_take. lia. }
        rewrite length_take_le.
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
*)

(*

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

(* TODO: port to async disk *)
(* TODO: DSL that captures many operations, not just a single WriteMulti *)
(* TODO: instantiate P with a state machine to capture refinement *)

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
