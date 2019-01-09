From RecoveryRefinement Require Import Lib.
From RecoveryRefinement Require Import Spec.SumProc.
From RecoveryRefinement Require Import Database.Common.
From RecoveryRefinement Require Import Database.Filesys.

Module Table.
  Module IndexEntry.
    Record t :=
      mk { handle : SliceHandle.t;
           keys: Key * Key; }.
  End IndexEntry.
  Module Tbl.
    Record t :=
      mk { ident : int64;
           fd : Fd;
           index : Array IndexEntry.t; }.
  End Tbl.

  (* TODO: an iterator over Tbl.index (maybe a combination of a Ref int64 and
  the length of the list) *)
  Definition ReadIterator := unit.

  Inductive Op : Type -> Type :=
  | ReadAll : Tbl.t -> Op ReadIterator
  | ReadNext : Tbl.t -> ReadIterator -> Op (option Entry.t)
  | Create : int64 -> Op Tbl.t
  | WriteEntry : Tbl.t -> Entry.t -> Op unit
  .

End Table.
