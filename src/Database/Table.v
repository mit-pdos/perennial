From RecoveryRefinement Require Import Lib.
From RecoveryRefinement Require Import Spec.SumProc.
From RecoveryRefinement Require Import Database.Common.
From RecoveryRefinement Require Import Database.BinaryEncoding.
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

  Module ReadIterator.
    Record t :=
      mk { offset : IORef int64;
           buffer : IORef ByteString;
           length : int64; }.
  End ReadIterator.

  Inductive Op : Type -> Type :=
  (* read a table (by iterating over it) *)
  | ReadAll : Tbl.t -> Op ReadIterator.t
  | ReadNext : Tbl.t -> ReadIterator.t -> Op (option Entry.t)
  (* create a table by streaming entries *)
  | New : Fd -> Op TblWriter.t
  | PutEntry : TblWriter.t -> Entry.t -> Op unit
  | Create : TblWriter.t -> int32 -> Op Tbl.t
  .

End Table.

Module TableImpl.
  Import Table.

  Import ProcNotations.
  Local Open Scope proc.

  Definition readAll (t:Tbl.t) : proc (Data.Op ⊕ FS.Op) _ :=
    lift (index <- Call (Data.NewIORef int_val0);
            buf <- Call (Data.NewIORef BS.empty);
            Ret (ReadIterator.mk index buf int_val0)).

  Definition fill (t:Tbl.t) (it:ReadIterator.t) : proc (Data.Op ⊕ FS.Op) _ :=
    offset <- Data.readIORef it.(ReadIterator.offset);
      data <- lift (FS.readAt t.(Tbl.fd) offset int_val4096);
      _ <- Data.modifyIORef it.(ReadIterator.offset) (fun o => intPlus _ o (BS.length data));
      (* technically this is known to be unnecessary if len - offset >= 4096 *)
      let newData := BS.take (intSub (BS.length data) offset) data in
      Data.modifyIORef it.(ReadIterator.buffer) (fun bs => BS.append bs newData).

  Definition readNext (t:Tbl.t) (it:ReadIterator.t) : proc (Data.Op ⊕ FS.Op) _ :=
    data <- Data.readIORef it.(ReadIterator.buffer);
      match decode Entry.t data with
      | Some (e, n) =>
        _ <- Data.writeIORef it.(ReadIterator.buffer) (BS.drop n data);
          Ret (Some e)
      | None => _ <- fill t it;
                 Ret None (* TODO: restart, if filling added any new values *)
      end.

End TableImpl.
