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

  (* reference to a read-only table *)
  Module Tbl.
    Record t :=
      mk { ident : int32;
           fd : Fd;
           index : Array IndexEntry.t; }.
  End Tbl.

  Module TblWriter.
    Record t :=
      mk {
        (* FIXME: specious-db uses a buffered writer, which was extremely
        important for performance; it avoids issuing a write syscall for every
        entry (110 bytes), batching them into 4096-byte writes *)
        fd : Fd;
        fileOffset : IORef int64;
        (* these are all for the current index entry *)
        indexOffset : IORef int64;
        indexMin : IORef Key;
        indexMax : IORef Key;
        indexNumKeys : IORef int64;
      }.
  End TblWriter.

  (* TODO: an iterator over Tbl.index (maybe a combination of a Ref int64 and
  the length of the list) *)
  Definition ReadIterator := unit.

  Inductive Op : Type -> Type :=
  (* read a table (by iterating over it) *)
  | ReadAll : Tbl.t -> Op ReadIterator
  | ReadNext : Tbl.t -> ReadIterator -> Op (option Entry.t)
  (* create a table by streaming entries *)
  | New : Fd -> Op TblWriter.t
  | PutEntry : TblWriter.t -> Entry.t -> Op unit
  | Create : TblWriter.t -> int32 -> Op Tbl.t
  .

End Table.
