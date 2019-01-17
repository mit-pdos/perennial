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
      mk { ident : uint32;
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
        fileOffset : IORef ty.uint64;
        (* these are all for the current index entry *)
        indexOffset : IORef ty.uint64;
        indexMin : IORef ty.uint64; (* key *)
        indexMax : IORef ty.uint64;
        indexNumKeys : IORef ty.uint64;
        (* these are finished index entries *)
        indexEntries : Array IndexEntry.t;
      }.
  End TblWriter.

  Module ReadIterator.
    Record t :=
      mk { offset : IORef ty.uint64;
           buffer : IORef ty.ByteString;
           length : uint64; }.
  End ReadIterator.

  Import ProcNotations.
  Local Open Scope proc.

  Notation proc := (proc (Data.Op ⊕ FS.Op)).

  Definition readAll (t:Tbl.t) : proc ReadIterator.t :=
    index <- Data.newIORef ty.uint64 int_val0;
      buf <- Data.newIORef ty.ByteString BS.empty;
      Ret (ReadIterator.mk index buf int_val0).

  Definition fill (t:Tbl.t) (it:ReadIterator.t) : proc unit :=
    offset <- Data.readIORef it.(ReadIterator.offset);
      data <- lift (FS.readAt t.(Tbl.fd) offset uint_val4096);
      _ <- Data.modifyIORef it.(ReadIterator.offset) (fun o => intPlus _ o (BS.length data));
      (* technically this is known to be unnecessary if len - offset >= 4096 *)
      let newData := BS.take (intSub (BS.length data) offset) data in
      Data.modifyIORef it.(ReadIterator.buffer) (fun bs => BS.append bs newData).

  Definition readNext (t:Tbl.t) (it:ReadIterator.t) : proc (option Entry.t) :=
    data <- Data.readIORef it.(ReadIterator.buffer);
      match decode Entry.t data with
      | Some (e, n) =>
        _ <- Data.writeIORef it.(ReadIterator.buffer) (BS.drop n data);
          Ret (Some e)
      | None => _ <- fill t it;
                 Ret None (* TODO: restart, if filling added any new values *)
      end.

  Definition new (fh:Fd) : proc TblWriter.t :=
    fileOffset <- Data.newIORef ty.uint64 (int_val0);
      indexOffset <- Data.newIORef ty.uint64 (int_val0);
      indexMin <- Data.newIORef ty.uint64 (int_val0);
      indexMax <- Data.newIORef ty.uint64 (int_val0);
      indexNumKeys <- Data.newIORef ty.uint64 (int_val0);
      indexEntries <- Call (inject (Data.NewArray _));
      Ret {| TblWriter.fd := fh;
             TblWriter.fileOffset := fileOffset;
             TblWriter.indexOffset := indexOffset;
             TblWriter.indexMin := indexMin;
             TblWriter.indexMax := indexMax;
             TblWriter.indexNumKeys := indexNumKeys;
             TblWriter.indexEntries := indexEntries; |}.

  Definition putEntry (t:TblWriter.t) (e: Entry.t) : proc unit :=
    (* TODO: implement *)
    Ret tt.

  (* create the current index entry *)
  Definition flushEntry (t:TblWriter.t) : proc unit :=
    (* TODO: implement *)
    Ret tt.

  (* consumes the table writer and finishes writing out the table *)
  Definition create (t:TblWriter.t) (id:uint32) : proc Tbl.t :=
    _ <- flushEntry t;
      (* TODO: write out index *)
      Ret {| Tbl.fd := TblWriter.fd t;
             Tbl.ident := id;
             Tbl.index := TblWriter.indexEntries t; |}.

End Table.
