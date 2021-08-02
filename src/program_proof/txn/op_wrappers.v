From Perennial.goose_lang Require Import lang notation typing.
From Perennial.goose_lang.lib Require Import map.impl list.impl list_slice.
From Perennial.goose_lang.ffi Require Import jrnl_ffi.
From Perennial.goose_lang.ffi Require Import disk.
From Goose.github_com.mit_pdos.go_journal Require Import obj txn alloc.

From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang Require Import ffi.disk_prelude.

From Goose Require github_com.mit_pdos.go_journal.addr.
From Goose Require github_com.mit_pdos.go_journal.buf.
From Goose Require github_com.mit_pdos.go_journal.jrnl.
From Goose Require github_com.mit_pdos.go_journal.common.
From Goose Require github_com.mit_pdos.go_journal.lockmap.
From Goose Require github_com.mit_pdos.go_journal.obj.
From Goose Require github_com.mit_pdos.go_journal.util.

Definition Txn__ReadBuf' : val :=
  λ: "twophase" "az", SliceToList byteT (Txn__ReadBuf "twophase" (Fst "az") (Snd "az")).

Definition Txn__ReadBufBit' : val :=
  (λ: "twophase" "a", Skip;; Txn__ReadBufBit "twophase" "a").

Definition Txn__OverWrite' : val :=
  λ: "twophase" "ad",
  let: "s" := ListToSlice byteT (Snd "ad") in
  Txn__OverWrite "twophase" (Fst "ad") (slice.len "s" * #8) "s".

Definition Txn__OverWriteBit' : val :=
  λ: "twophase" "ad",
  Txn__OverWriteBit "twophase" (Fst "ad") (Snd "ad").

Definition Txn__ConditionalCommit' : val :=
  λ: "twophase" "v",
  match: "v" with
      NONE => Txn__ReleaseAll "twophase";; "v"
    | SOME "_" =>
    if: Txn__Commit "twophase" then
      "v"
    else
      NONEV
  end.

Definition Alloc__MarkUsed' : val :=
  λ: "ln",
  Alloc__MarkUsed (Fst "ln") (Snd "ln").

Definition Alloc__FreeNum' : val :=
  λ: "ln",
  Alloc__FreeNum (Fst "ln") (Snd "ln").
