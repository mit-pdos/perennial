From Perennial.goose_lang Require Import lang notation typing.
From Perennial.goose_lang.lib Require Import map.impl list.impl list_slice.
From Perennial.goose_lang.ffi Require Import jrnl_ffi.
From Perennial.goose_lang.ffi Require Import disk.
From Goose.github_com.mit_pdos.go_journal Require Import obj twophase alloc.

From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang Require Import ffi.disk_prelude.

From Goose Require github_com.mit_pdos.go_journal.addr.
From Goose Require github_com.mit_pdos.go_journal.buf.
From Goose Require github_com.mit_pdos.go_journal.jrnl.
From Goose Require github_com.mit_pdos.go_journal.common.
From Goose Require github_com.mit_pdos.go_journal.lockmap.
From Goose Require github_com.mit_pdos.go_journal.obj.
From Goose Require github_com.mit_pdos.go_journal.util.

Definition TwoPhase__ReadBuf' : val :=
  λ: "twophase" "az", SliceToList byteT (TwoPhase__ReadBuf "twophase" (Fst "az") (Snd "az")).

Definition TwoPhase__OverWrite' : val :=
  λ: "twophase" "ad",
  let: "s" := ListToSlice byteT (Snd "ad") in
  TwoPhase__OverWrite "twophase" (Fst "ad") (slice.len "s" * #8) "s".

Definition TwoPhase__OverWriteBit' : val :=
  λ: "twophase" "ad",
  TwoPhase__OverWriteBit "twophase" (Fst "ad") (Snd "ad").

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

Definition Alloc__MarkUsed' : val :=
  λ: "ln",
  Alloc__MarkUsed (Fst "ln") (Snd "ln").

Definition Alloc__FreeNum' : val :=
  λ: "ln",
  Alloc__FreeNum (Fst "ln") (Snd "ln").
