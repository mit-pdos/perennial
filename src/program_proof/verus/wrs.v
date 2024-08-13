From Perennial.program_proof Require Import disk_prelude.
From Perennial.program_proof Require Import disk_lib.
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
		d.Write(a + (off * disk.BlockSize), vs[off])
		off = std.SumAssumeNoOverflow(off, 1)
	}
}

*)

Definition WriteMulti: val :=
  rec: "WriteMulti" "d" "a" "vs" :=
    let: "off" := ref (zero_val uint64T) in
    Skip;;
    (for: (λ: <>, (![uint64T] "off") < (slice.len "vs")); (λ: <>, Skip) := λ: <>,
      disk.Write ("a" + ((![uint64T] "off") * disk.BlockSize)) (SliceGet (slice.T byteT) "vs" (![uint64T] "off"));;
      "off" <-[uint64T] (std.SumAssumeNoOverflow (![uint64T] "off") #1);;
      Continue);;
    #().

Section proof.

Context `{!heapGS Σ}.
Context `{!stagedG Σ}.

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
       [∗ list] i↦b ∈ (take (Z.to_nat idx) bs ++ drop (Z.to_nat idx) bs0), (uint.Z a + i) d↦ b)%I with "[Hoff Hb]" as "Hdisk".
  { iExists 0. iFrame. }
  wpc_apply (wpc_forBreak_cond_2 with "[-]").
  { iNamedAccu. }
  { iNamed 1.
    crash_case.
    iDestruct "Hdisk" as (idx) "[Hoff Hdisk]".
    iFrame. }
  iIntros "!# __CTX"; iNamed "__CTX".

  iCache with "HΦ Hdisk".
  { crash_case.
    iDestruct "Hdisk" as (idx) "[Hoff Hdisk]".
    iFrame. }
  wpc_pures.

  (* why is wpc_bind not matching? *)
  wpc_bind (load_ty uint64T (LitV off)).
  wpc_bind (slice.len s).
Admitted.

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
