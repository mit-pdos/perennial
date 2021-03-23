From Perennial.goose_lang Require Import lang notation typing.
From Perennial.goose_lang.lib Require Import map.impl list.impl list_slice.
From Perennial.goose_lang.ffi Require Import jrnl_ffi.
From Perennial.goose_lang.ffi Require Import disk.
From Goose.github_com.mit_pdos.goose_nfsd Require Import txn twophase.

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
  λ: "twophase" "az", SliceToList byteT (TwoPhase__ReadBuf "twophase" (Fst "az") (Snd "az")).

Definition TwoPhase__OverWrite' : val :=
  λ: "twophase" "ad",
  let: "s" := ListToSlice byteT (Snd "ad") in
  TwoPhase__OverWrite "twophase" (Fst "ad") (slice.len "s" * #8) "s".

Definition TwoPhase__ConditionalCommit' : val :=
  λ: "twophase" "v",
  match: "v" with
      NONE => TwoPhase__ReleaseAll "twophase";; "v"
    | SOME "_" =>
    if: TwoPhase__Commit "twophase" then
      "v"
    else
      NONEV
  end.
