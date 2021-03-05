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

(* XXX: replace with the actual Goose generated version later *)
Module TwoPhasePre.
  Definition S := struct.decl [
    "txn" :: struct.ptrT txn.Txn.S;
    "locks" :: struct.ptrT lockmap.LockMap.S
  ].
End TwoPhasePre.

Definition TwoPhase__ReadBuf' : val :=
  λ: "twophase" "az", SliceToList byteT (TwoPhase__ReadBuf "twophase" (Fst "az") (Snd "az")).

Definition TwoPhase__OverWrite' : val :=
  λ: "twophase" "ad",
  let: "s" := ListToSlice byteT (Snd "ad") in
  TwoPhase__OverWrite "twophase" (Fst "ad") "s" (slice.len "s").

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

(* XXX: todo: this should call a wrapped version of MkTxn that also allocates
the lockmap and returns a struct containing both *)
Definition TwoPhase__Init' : val :=
  (λ: "_", MkTxn #()).

(* XXX: todo: this should be a version that takes a struct instead of the two arg version *)
Definition TwoPhase__Begin' : val :=
  (λ: "l", Begin "l").
