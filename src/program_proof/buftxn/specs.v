From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

From Perennial.Helpers Require Import Transitions.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.Helpers Require Import GenHeap.
From Perennial.goose_lang.lib Require Import struct.

From Goose.github_com.mit_pdos.goose_nfsd Require Import addr buftxn.
From Perennial.program_proof Require Import txn.specs.

Section heap.
Context `{!heapG Σ}.
Context `{!lockG Σ}.
Context `{!inG Σ (authR (optionUR (exclR boolO)))}.

Implicit Types s : Slice.t.
Implicit Types (stk:stuckness) (E: coPset).

Definition is_buftxn (buftx : loc) (γT γUnified : gen_heapG addr txnObject Σ) : iProp Σ :=
  (
    ∃ (l : loc) mT bufmap (txid : u64) gBits gInodes gBlocks,
      buftx ↦[BufTxn.S :: "txn"] #l ∗
      buftx ↦[BufTxn.S :: "bufs"] #bufmap ∗
      buftx ↦[BufTxn.S :: "Id"] #txid ∗
      is_txn l gBits gInodes gBlocks ∗
      unify_heaps gBits gInodes gBlocks γUnified ∗
      gen_heap_ctx (hG := γT) mT ∗
      [∗ map] a ↦ v ∈ mT,
        ∃ v0,
          mapsto (hG := γUnified) a 1 v0
  )%I.

Theorem wp_buftxn_Begin l gBits gInodes gBlocks γUnified :
  {{{ is_txn l gBits gInodes gBlocks ∗
      unify_heaps gBits gInodes gBlocks γUnified
  }}}
    Begin #l
  {{{ (buftx : loc) γt, RET #buftx;
      is_buftxn buftx γt γUnified
  }}}.
Proof.
  iIntros (Φ) "(Htxn & Hunified) HΦ".
Admitted.

Theorem wp_BufTxn__ReadBuf__Block buftx γt γUnified a aa v :
  {{{
    is_buftxn buftx γt γUnified ∗
    ⌜ getField_f Addr.S "Sz" a = #(U64 (block_bytes*8)%nat) ⌝ ∗
    ⌜ getField_f Addr.S "Blkno" a = #aa.(addrBlock) ⌝ ∗
    ⌜ getField_f Addr.S "Off" a = #aa.(addrOff) ⌝ ∗
    mapsto (hG := γt) aa 1 (txnBlock v)
  }}}
    BufTxn__ReadBuf #buftx a
  {{{
    (buf : Slice.t), RET (slice_val buf);
    is_slice buf u8T 1%Qp (Block_to_vals v) ∗
    is_buftxn buftx γt γUnified ∗
    mapsto (hG := γt) aa 1 (txnBlock v)
  }}}.
Proof.
  iIntros (Φ) "(Htxn & % & % & % & Ha) HΦ".
  iDestruct "Htxn" as (l mT bufmap txid gBits gInodes gBlocks) "(Hl & Hbufmap & Htxid & Htxn & Hunify & Hγtctx & Hm)".
  wp_call.
  wp_loadField.
Admitted.

Theorem wp_BufTxn__OverWrite__Block buftx γt γUnified a aa v0 v (buf : Slice.t) :
  {{{
    is_buftxn buftx γt γUnified ∗
    ⌜ getField_f Addr.S "Sz" a = #(U64 (block_bytes*8)%nat) ⌝ ∗
    ⌜ getField_f Addr.S "Blkno" a = #aa.(addrBlock) ⌝ ∗
    ⌜ getField_f Addr.S "Off" a = #aa.(addrOff) ⌝ ∗
    mapsto (hG := γt) aa 1 (txnBlock v0) ∗
    is_slice buf u8T 1%Qp (Block_to_vals v)
  }}}
    BufTxn__OverWrite #buftx a (slice_val buf)
  {{{
    RET #();
    is_buftxn buftx γt γUnified ∗
    mapsto (hG := γt) aa 1 (txnBlock v)
  }}}.
Proof.
  iIntros (Φ) "(Htxn & % & % & % & Ha & Hbuf) HΦ".
  iDestruct "Htxn" as (l mT bufmap txid gBits gInodes gBlocks) "(Hl & Hbufmap & Htxid & Htxn & Hunify & Hγtctx & Hm)".
  wp_call.
  wp_loadField.
Admitted.

Theorem BufTxn_lift buftx γt γUnified a v :
  (
    is_buftxn buftx γt γUnified ∗
    mapsto (hG := γUnified) a 1 v
  )
    ==∗
  (
    is_buftxn buftx γt γUnified ∗
    mapsto (hG := γt) a 1 v
  ).
Proof.
  iIntros "[Htxn Ha]".
  iDestruct "Htxn" as (l mT bufmap txid gBits gInodes gBlocks) "(Hl & Hbufmap & Htxid & Htxn & Hunify & Hγtctx & Hm)".
  iAssert (⌜ mT !! a = None ⌝)%I as %Hnone.
  {
    destruct (mT !! a) eqn:He; eauto.
    iDestruct (big_sepM_lookup with "Hm") as (v2) "Ha2"; eauto.
    iDestruct (mapsto_valid_2 with "Ha Ha2") as %Ha.
    exfalso. eauto.
  }

  iMod ((gen_heap_alloc _ _ v) with "Hγtctx") as "[Hγtctx Haa]"; eauto.
  iModIntro.
  iSplitR "Haa"; [|iFrame].

  iExists _, _, _, _, _, _, _.
  iFrame.
  iApply (big_sepM_insert); eauto.
  iFrame.
  iExists _; iFrame.
Qed.

Theorem wp_BufTxn__CommitWait buftx γt γUnified mods :
  {{{
    is_buftxn buftx γt γUnified ∗
    [∗ map] a ↦ v ∈ mods, mapsto (hG := γt) a 1 v
  }}}
    BufTxn__CommitWait #buftx #true
  {{{
    RET #();
    [∗ map] a ↦ v ∈ mods, mapsto (hG := γUnified) a 1 v
  }}}.
Proof.
  iIntros (Φ) "(Htxn & Hmods) HΦ".
  iDestruct "Htxn" as (l mT bufmap txid gBits gInodes gBlocks) "(Hl & Hbufmap & Htxid & Htxn & Hunify & Hγtctx & Hm)".

  wp_call.
  wp_apply util_proof.wp_DPrintf.
  wp_loadField.
  wp_loadField.
Admitted.

End heap.
