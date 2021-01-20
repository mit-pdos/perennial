From Perennial.goose_lang Require Import lang notation typing.
From Perennial.goose_lang.lib Require Import map.impl list.impl list_slice.
From Perennial.goose_lang.ffi Require Import jrnl_ffi.
From Perennial.goose_lang.ffi Require Import disk.
From Goose.github_com.mit_pdos.goose_nfsd Require Import twophase.

From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang Require Import ffi.disk_prelude.

From Goose Require github_com.mit_pdos.goose_nfsd.addr.
From Goose Require github_com.mit_pdos.goose_nfsd.buf.
From Goose Require github_com.mit_pdos.goose_nfsd.buftxn.
From Goose Require github_com.mit_pdos.goose_nfsd.common.
From Goose Require github_com.mit_pdos.goose_nfsd.lockmap.
From Goose Require github_com.mit_pdos.goose_nfsd.txn.
From Goose Require github_com.mit_pdos.goose_nfsd.util.

Definition TwoPhase__ReadBuf' : val :=
  λ: "twophase" "addr" "sz", SliceToList byteT (TwoPhase__ReadBuf "twophase" "addr" "sz").

Definition TwoPhase__OverWrite' : val :=
  λ: "twophase" "addr" "data",
  let: "s" := ListToSlice byteT "data" in
  TwoPhase__OverWrite "twophase" "addr" "s" (slice.len "s").
