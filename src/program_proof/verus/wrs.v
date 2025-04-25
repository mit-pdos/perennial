From Perennial.program_proof Require Import async_disk_prelude.
From Perennial.program_proof Require Import async_disk_lib std_proof.
From Goose Require github_com.goose_lang.std.

(**
 * This file tries to prove soundness for a write-restricted-storage (PoWER) API,
 * which helps express crash-safety without explicit support for atomic invariants,
 * WPCs, or crash semantics.
 *)

(*
 * The model of an application is captured by the Simulate() function below,
 * implemented in Go.  It issues arbitrary read, write, and barrier operations
 * against a storage device, with arguments chosen by rd() and wr() callbacks,
 * and we later prove that, despite the fact that it issues these arbitrary
 * operations, it still maintains some invariant on the state of the disk at
 * all times, as long as it respects preconditions on the d.Write() calls that
 * mirror the write-restricted-storage (PoWER) API spec.
 *)

(*
 * To translate this Go code -- present below as a comment -- into its Perennial
 * model, run:
 *
 * ~/go/bin/goose ~/wrs
 *)

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

Theorem wpc_Read_disk stk E1 (a: u64) cd d :
  {{{ own_disk cd d ∗
      ⌜uint.Z a ∈ dom d⌝ }}}
    disk.Read #a @ stk; E1
  {{{ s b, RET (slice_val s);
      own_disk cd d ∗
      is_block s (DfracOwn 1) b ∗
      ⌜d !! uint.Z a = Some b⌝ }}}
  {{{ own_disk cd d }}}.
Proof.
  iIntros (Φ Φc) "Hpre HΦ".
  iDestruct "Hpre" as "(Hd & %Hdom)".
  iDestruct (disk_lookup_acc with "[] Hd") as (vcrash v) "(Ha & %Hclookup & %Halookup & Hacc)".
  { eauto. }
  wpc_apply (wpc_Read with "Ha").
  iSplit.
  { iIntros "Ha". iSpecialize ("Hacc" with "Ha"). crash_case. iFrame. }
  iModIntro.
  iIntros (s) "[Ha Hs]".
  iSpecialize ("Hacc" with "Ha").
  iRight in "HΦ". iApply "HΦ". iFrame. iSplit.
  { iDestruct (own_slice_to_small with "Hs") as "Hs". iFrame. }
  done.
Qed.

Theorem wpc_Write_disk stk E1 (a: u64) cd d s q b :
  {{{ own_disk cd d ∗
      ⌜uint.Z a ∈ dom d⌝ ∗
      is_block s q b }}}
    disk.Write #a (slice_val s) @ stk; E1
  {{{ RET #();
      is_block s q b ∗
      ( own_disk cd (<[uint.Z a := b]> d) ∨
        own_disk (<[uint.Z a := b]> cd) (<[uint.Z a := b]> d) ) }}}
  {{{ own_disk cd d ∨
      own_disk cd (<[uint.Z a := b]> d) ∨
      own_disk (<[uint.Z a := b]> cd) (<[uint.Z a := b]> d) }}}.
Proof.
  iIntros (Φ Φc) "Hpre HΦ".
  iDestruct "Hpre" as "(Hd & %Hdom & Hb)".
  iDestruct (disk_insert_acc with "[] Hd") as (vcrash v) "(Ha & %Hclookup & %Halookup & Hacc)".
  { done. }
  wpc_apply (wpc_Write with "[$Ha $Hb]").
  iSplit.
  { iLeft in "HΦ". iIntros "[Ha|[Ha|Ha]]"; iApply "HΦ".
    - iSpecialize ("Hacc" with "Ha"). rewrite insert_id //. rewrite insert_id //. iFrame.
    - iSpecialize ("Hacc" with "Ha"). rewrite insert_id //. iFrame.
    - iSpecialize ("Hacc" with "Ha"). iFrame.
  }
  iRight in "HΦ".
  iIntros "!> (%bp & Ha & Hb & %Hbp)".
  iApply "HΦ". iFrame.
  iSpecialize ("Hacc" with "Ha"). destruct Hbp; subst.
  - iFrame.
  - rewrite insert_id //. iFrame.
Qed.

Theorem wpc_Barrier_disk stk E1 cd d :
  {{{ own_disk cd d }}}
    disk.Barrier #() @ stk; E1
  {{{ RET #(); own_disk cd d ∗ ⌜cd = d⌝ }}}
  {{{ own_disk cd d }}}.
Proof.
  iIntros (Φ Φc) "Hd HΦ".
  iDestruct (big_sepM2_alt with "Hd") as "[%Hddom Hdzip]".
  wpc_apply (wpc_Barrier _ _ (map_zip cd d) with "Hdzip").
  iSplit.
  { iIntros "Hdzip".
    crash_case.
    iApply big_sepM2_alt. iFrame. done.
  }
  iIntros "!> [%Hbarrier Hdzip]".
  assert (cd = d) as Hdseq.
  { apply map_eq. intro i. specialize (Hbarrier i).
    destruct (cd !! i) eqn:Hi.
    - assert (i ∈ dom d) as Hin. { rewrite -Hddom. apply elem_of_dom. eauto. }
      apply elem_of_dom in Hin. destruct Hin as [b' Hin].
      epose proof (map_zip_lookup_some _ _ _ _ _ Hi Hin) as Hz.
      specialize (Hbarrier _ Hz).
      apply map_lookup_zip_Some in Hz. simpl in *; subst. intuition congruence.
    - assert (i ∉ dom d) as Hin. { rewrite -Hddom. apply not_elem_of_dom. eauto. }
      apply not_elem_of_dom in Hin. rewrite Hi. rewrite Hin. congruence.
  }
  rewrite Hdseq.
  iDestruct (big_sepM2_alt (λ a b c, a d↦[b] c)%I d d with "[$Hdzip]") as "Hd".
  { eauto. }
  iRight in "HΦ".
  iApply "HΦ".
  iFrame. done.
Qed.

Section WRS.

(* Roughly equivalent to the opaque check_permission from write-restricted storage *)
Parameter P : disk_state -> disk_state -> iProp Σ.
Parameter Pcrash : disk_state -> iProp Σ.
Parameter Pcfupd : ∀ cds ds, P cds ds -∗ |C={⊤}=> Pcrash cds.

(*
 * This wpc_Simulate theorem states that, if we run Simulate() with an
 * [rd] callback that chooses random in-bounds addresses for reads, and
 * [wr] callback that chooses random in-bounds writes that satisfy the
 * same properties that the PoWER write specification would require,
 * then the crash condition [Pcrash] holds at all times, and [P] holds
 * if Simulate decides to return before crashing.
 *)
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
                   "Hwr_fupd" ∷ ((∀ cds ds, P cds ds ==∗ P cds (<[uint.Z a := b]> ds)) ∧
                                 (∀ cds ds, P cds ds ==∗ P (<[uint.Z a := b]> cds) (<[uint.Z a := b]> ds)))
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
    wpc_pures.
    { crash_case.
      iIntros "HC". iMod (Pcfupd with "HP HC") as "HP".
      iModIntro. crash_case. iFrame. }
    wpc_apply (wpc_Read_disk with "[$Hd]").
    { rewrite -Hdom' //. }
    iSplit.
    { iIntros "Ha".
      iIntros "HC". iMod (Pcfupd with "HP HC") as "HP".
      iModIntro. crash_case. iFrame. }
    iIntros (s b) "!> (Hd & Hb & %Hbv)".
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
    wpc_pures.
    { iIntros "HC". iMod (Pcfupd with "HP HC") as "HP".
      iModIntro. crash_case. iFrame. }
    wpc_apply (wpc_Write_disk with "[$Hd $Hb]").
    { rewrite -Hdom'. done. }
    iSplit.
    { iIntros "Hd". iDestruct "Hd" as "[Hd | [Hd | Hd]]".
      + iIntros "HC".
        iMod (Pcfupd with "HP HC") as "HP".
        iModIntro. crash_case. iFrame.
      + iIntros "HC".
        iLeft in "Hwr_fupd". iMod ("Hwr_fupd" with "HP") as "HP".
        iMod (Pcfupd with "HP HC") as "HP".
        iModIntro. crash_case. iFrame.
      + iIntros "HC".
        iRight in "Hwr_fupd". iMod ("Hwr_fupd" with "HP") as "HP".
        iMod (Pcfupd with "HP HC") as "HP".
        iModIntro. crash_case. iFrame.
    }
    iModIntro. iIntros "[H Hd]".
    iDestruct "Hd" as "[Hd | Hd]".
    + iLeft in "Hwr_fupd".
      iMod ("Hwr_fupd" with "HP") as "HP".
      wpc_pures.
      { iIntros "HC".
        iMod (Pcfupd with "HP HC") as "HP".
        iModIntro. crash_case. iFrame.
      }
      iLeft.
      iModIntro. iSplit; first done. iFrame.
      rewrite dom_insert_L.
      iPureIntro. set_solver.
    + iRight in "Hwr_fupd".
      iMod ("Hwr_fupd" with "HP") as "HP".
      wpc_pures.
      { iIntros "HC".
        iMod (Pcfupd with "HP HC") as "HP".
        iModIntro. crash_case. iFrame.
      }
      iLeft.
      iModIntro. iSplit; first done. iFrame.
      rewrite dom_insert_L.
      iPureIntro. set_solver.
  }

  wpc_pures.
  wpc_if_destruct.
  {
    wpc_pures.
    iNamed "Hloop".
    wpc_apply (wpc_Barrier_disk with "Hd").
    iSplit.
    { iIntros "Hd".
      iIntros "HC". iMod (Pcfupd with "HP HC") as "HP".
      iModIntro. crash_case.
      iExists cds', ds'. iFrame.
    }
    iIntros "!> [Hd %Hbarrier]". subst.
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
Parameter Pabs : State -> iProp Σ.
Parameter Pabs_crash : State -> iProp Σ.

Context `{!ghost_varG Σ State}.

Definition Psm (crash curr : disk_state) : iProp Σ :=
  "Hcrash" ∷ Pabs_crash (abs crash) ∗
  "Hcurr" ∷ Pabs (abs curr).

Definition Psm_crash (crash : disk_state) : iProp Σ :=
  "Hcrash" ∷ Pabs_crash (abs crash).

Theorem Psm_cfupd : ∀ cds ds, Psm cds ds -∗ |C={⊤}=> Psm_crash cds.
Proof.
  iIntros (cds ds) "HP". iNamed "HP".
  iFrame. done.
Qed.

(*
 * This theorem illustrates how to translate thinking about some [wr]
 * ensuring some predicates on the raw state of the disk vs. ensuring
 * some predicates on an abstract state machine state (post-recovery
 * state).
 *)
Theorem wp_wr_sm wr (ds : disk_state) stk :
  {{{ True }}}
    #wr #() @ stk; ⊤
  {{{ (a:u64) (s:Slice.t) q b, RET (#a, slice_val s);
    "%Ha" ∷ ⌜uint.Z a ∈ dom ds⌝ ∗
    "Hb" ∷ is_block s q b ∗
    "Habs_fupd" ∷ (∀ ds, Pabs (abs ds) ==∗ Pabs (abs (<[uint.Z a := b]> ds))) ∗
    "Habs_crash_fupd" ∷ (∀ cds, Pabs_crash (abs cds) ==∗ Pabs_crash (abs (<[uint.Z a := b]> cds)))
  }}}
    -∗
  {{{ True }}}
    #wr #() @ stk; ⊤
  {{{ (a:u64) (s:Slice.t) q b, RET (#a, slice_val s);
    "%Ha" ∷ ⌜uint.Z a ∈ dom ds⌝ ∗
    "Hb" ∷ is_block s q b ∗
    "Hwr_fupd" ∷ ((∀ cds ds, Psm cds ds ==∗ Psm cds (<[uint.Z a := b]> ds)) ∧
                  (∀ cds ds, Psm cds ds ==∗ Psm (<[uint.Z a := b]> cds) (<[uint.Z a := b]> ds)))
  }}}.
Proof.
  iIntros "#Hwp".
  iIntros (Φ) "!> _ HΦ".
  iApply "Hwp"; first by done.
  iModIntro. iIntros (a s q b). iNamed 1. iApply "HΦ".
  iSplit; first by done. iFrame "Hb".
  iSplit.
  - iIntros (cds' ds'). iNamed 1.
    iMod ("Habs_fupd" with "Hcurr") as "Hcurr".
    iModIntro.
    iFrame.
  - iIntros (cds' ds'). iNamed 1.
    iMod ("Habs_fupd" with "Hcurr") as "Hcurr".
    iMod ("Habs_crash_fupd" with "Hcrash") as "Hcrash".
    iModIntro.
    iFrame.
Qed.

End WRS_StateMachine.

End proof.
