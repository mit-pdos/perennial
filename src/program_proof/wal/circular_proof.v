From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
From Goose.github_com.mit_pdos.goose_nfsd Require Import wal.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof Require Import wal.abstraction.
From Perennial.program_proof Require Import marshal_proof.
From Perennial.program_proof Require Import disk_lib.
From Perennial.Helpers Require Import GenHeap.

From Perennial.Helpers Require Import Transitions.
Existing Instance r_mbind.

Definition LogSz := 511.

Module circΣ.
  Record t :=
    mk { upds: list update.t;
         start: u64;
       }.
  Global Instance _eta: Settable _ := settable! mk <upds; start>.
  Definition diskEnd (s:t): Z :=
    int.val s.(start) + Z.of_nat (length s.(upds)).
  Definition empty (s:t): t :=
    mk [] (diskEnd s).
End circΣ.

Notation start := circΣ.start.
Notation upds := circΣ.upds.

Definition circ_read : transition circΣ.t (list update.t * u64) :=
  s ← reads (fun x => (upds x, start x));
  ret s.

Definition assert `(P : T -> Prop) : transition T unit :=
  @suchThat _ unit (fun σ _ => P σ) (fallback_genPred _).

Definition circ_advance (newStart : u64) : transition circΣ.t unit :=
  assert (fun σ => int.val σ.(start) <= int.val newStart <= int.val σ.(start) + length σ.(upds));;
  modify (fun σ => set upds (skipn (Z.to_nat (int.val newStart - int.val σ.(start))%Z)) σ);;
  modify (set start (fun _ => newStart)).

Definition circ_append (l : list update.t) : transition circΣ.t unit :=
  modify (set circΣ.upds (fun u => u ++ l));;
  assert (fun σ => length σ.(upds) <= LogSz).

Section heap.
Context `{!heapG Σ}.

Context (N: namespace).
Context (P: circΣ.t -> iProp Σ).
Context `{!forall σ, Timeless (P σ)}.

Definition is_low_state (startpos endpos : u64) (updarray : list update.t) : iProp Σ :=
  ⌜Z.of_nat (length updarray) = LogSz⌝ ∗
  ∃ hdr1 hdr2 hdr2extra,
    0 d↦ hdr1 ∗
    1 d↦ hdr2 ∗
    ⌜Block_to_vals hdr1 = b2val <$> encode ([EncUInt64 endpos] ++ (map EncUInt64 (map update.addr updarray)))⌝ ∗
    ⌜Block_to_vals hdr2 = b2val <$> encode [EncUInt64 startpos] ++ hdr2extra⌝ ∗
    2 d↦∗ (update.b <$> updarray).

Definition is_circular_state (σ : circΣ.t) : iProp Σ :=
  ∃ updarray,
    is_low_state σ.(circΣ.start) (word.add σ.(circΣ.start) (length σ.(circΣ.upds))) updarray ∗
    [∗ list] i ↦ bupd ∈ σ.(circΣ.upds),
      ⌜updarray !! Z.to_nat ((int.val σ.(circΣ.start) + i) `mod` LogSz)%Z = Some bupd⌝.

Definition is_circular : iProp Σ :=
  inv N (∃ σ, is_circular_state σ ∗ P σ).

Definition is_circular_appender (circ: loc) addrList : iProp Σ :=
  ∃ (diskaddr:loc) s,
    circ ↦[circularAppender.S :: "diskAddrs"] #diskaddr ∗
    diskaddr ↦[slice.T uint64T] (slice_val s) ∗
    is_slice s uint64T 1%Qp addrList.

Opaque encode.

Theorem wp_circular__Advance (Q: iProp Σ) d (newStart : u64) :
  {{{ is_circular ∗
    (∀ σ, P σ -∗
      ( (∃ σ' b, ⌜relation.denote (circ_advance newStart) σ σ' b⌝) ∧
        (∀ σ' b, ⌜relation.denote (circ_advance newStart) σ σ' b⌝ ={⊤ ∖↑ N}=∗ P σ' ∗ Q)))
  }}}
    Advance #d #newStart
  {{{ RET #(); Q }}}.
Proof.
  iIntros (Φ) "[#Hcirc Hfupd] HΦ".
  wp_call.
  wp_call.
  wp_apply wp_new_enc.
  iIntros (enc) "[Henc %]".
  wp_apply (wp_Enc__PutInt with "[$Henc]").
  {
Transparent encode.
    iPureIntro. rewrite /=. rewrite H0. word.
Opaque encode.
  }
  iIntros "Henc".
  wp_apply (wp_Enc__Finish with "Henc").
  iIntros (s extra) "[Hslice %]".
  wp_apply (wp_Write_fupd _ Q with "[Hslice Hfupd]").
  {
    iDestruct (is_slice_small_sz with "Hslice") as %Hslen.
    rewrite fmap_length in Hslen.

    iSplitL "Hslice".
    { iNext.
      rewrite -list_to_block_to_vals; first iFrame.
      rewrite Hslen. rewrite H1. rewrite H0. word.
    }

    iInv N as ">Hcircopen" "Hclose".
    iDestruct "Hcircopen" as (σ) "[Hcs HP]".
    iDestruct "Hcs" as (updarray) "[Hlow Hupds]".
    iDestruct "Hlow" as "[% Hlow]".
    iDestruct "Hlow" as (hdr1 hdr2 hdr2extra) "(Hd0 & Hd1 & % & % & Hd2)".
    iExists _. iFrame.
    iModIntro.
    iIntros "Hd1".

    iDestruct ("Hfupd" with "HP") as "[Hex Hfupd]".
    iDestruct "Hex" as (eσ' eb) "Hex".
    iDestruct "Hex" as %Hex.

    iSpecialize ("Hfupd" $! eσ' eb).
    simpl in Hex. monad_inv.

    iDestruct ("Hfupd" with "[]") as "Hfupd".
    { iPureIntro. repeat econstructor; lia. }

    iMod "Hfupd" as "[HP HQ]". iFrame.
    iApply "Hclose".

    iNext. iExists _. iFrame.
    iExists _. destruct σ. rewrite /=.
    iSplitL "Hd0 Hd1 Hd2".
    { rewrite /is_low_state. iSplitR "Hd0 Hd1 Hd2".
      2: {
        iExists _, _, _. iFrame.
        iPureIntro; intuition idtac; simpl in *.
        {
          rewrite H3.
          f_equal. f_equal. f_equal. f_equal.
          rewrite skipn_length.
          admit.
        }
        {
          rewrite -list_to_block_to_vals; eauto.
          rewrite Hslen. rewrite H1. rewrite H0. word.
        }
      }
      done.
    }
    admit.
  }

  iIntros "[Hslice HQ]".
  wp_pures.
  wp_call.
  iApply "HΦ".
  iFrame.
Admitted.

Theorem wp_circular__Append (Q: iProp Σ) d (newEnd : u64) (bufs : Slice.t) (buflist : list val) (upds : list update.t) c circAppenderList :
  {{{ is_circular ∗
      is_slice_small bufs (struct.t Update.S) 1 buflist ∗
      is_circular_appender c circAppenderList ∗
      (* relate buflist to upds *)
      (* require that [c] and [newEnd] correspond to reality..  newEnd should be σ.end+length(buflist).
        this is probably best handled by passing [circAppenderList] and [newEnd] into
        the [circ_append] transition, and erroring out in that transition if these values don't match. *)
       (∀ σ σ' b,
         ⌜relation.denote (circ_append upds) σ σ' b⌝ -∗
         (P σ ={⊤ ∖↑ N}=∗ P σ' ∗ Q))
  }}}
    circularAppender__Append #c #d #newEnd (slice_val bufs)
  {{{ RET #(); Q }}}.
Proof.
  iIntros (Φ) "(#Hcirc & Hslice & Hfupd) HΦ".
  wp_call.
  wp_call.
Admitted.

End heap.
