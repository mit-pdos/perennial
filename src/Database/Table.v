From RecoveryRefinement Require Import Lib.
From RecoveryRefinement Require Import Spec.SumProc.
From RecoveryRefinement Require Import Database.Common.
From RecoveryRefinement Require Import Database.BinaryEncoding.
From RecoveryRefinement Require Import Database.Filesys.

Module Table.
  Module IndexEntry.
    Definition ty := (ty.uint64 * ty.uint32 * ty.uint64 * ty.uint64)%ty.
    Definition t := ltac:(let x := eval unfold ty, Ty in (Ty ty) in
                              exact x).
    Definition handle (x:t) : SliceHandle.t :=
      let '(off, len, _, _) := x in
      SliceHandle.mk off len.
    Definition keys (x:t) : Key * Key :=
      let '(_, _, min, max) := x in
      (min, max).
  End IndexEntry.

  (* reference to a read-only table *)
  Module Tbl.
    Record t :=
      mk { ident : uint32;
           fd : Fd;
           index : Array IndexEntry.ty; }.
  End Tbl.

  Module ReadIterator.
    Record t :=
      mk { offset : IORef ty.uint64;
           buffer : IORef ty.ByteString;
           length : uint64; }.
  End ReadIterator.

  Import EqualDecNotation.

  Import ProcNotations.
  Local Open Scope proc.

  Notation proc := (proc (Data.Op ⊕ FS.Op)).

  Definition readAll (t:Tbl.t) : proc ReadIterator.t :=
    index <- Data.newIORef ty.uint64 int_val0;
      buf <- Data.newIORef ty.ByteString BS.empty;
      Ret (ReadIterator.mk index buf int_val0).

  (* [fill] attempts to fill the iterator buffer, and returns true if it
  succeeds *)
  Definition fill (t:Tbl.t) (it:ReadIterator.t) : proc bool :=
    offset <- Data.readIORef it.(ReadIterator.offset);
      data <- lift (FS.readAt t.(Tbl.fd) offset uint_val4096);
      if intCmp (BS.length data) int_val0 == Eq then Ret false
      else (_ <- Data.modifyIORef it.(ReadIterator.offset) (fun o => intPlus _ o (BS.length data));
              (* technically this is known to be unnecessary if len - offset >= 4096 *)
              let newData := BS.take (intSub (BS.length data) offset) data in
              _ <- Data.modifyIORef it.(ReadIterator.buffer) (fun bs => BS.append bs newData);
                Ret true).

  Definition readNext (t:Tbl.t) (it:ReadIterator.t) : proc (option Entry.t) :=
    LoopWhileVoid (data <- Data.readIORef it.(ReadIterator.buffer);
                 match decode Entry.t data with
                 | Some (e, n) =>
                   _ <- Data.writeIORef it.(ReadIterator.buffer) (BS.drop n data);
                     LoopRet (Some e)
                 | None => ok <- fill t it;
                            if ok then Continue tt else LoopRet None
                 end).

  Definition readIndexData (fd:Fd) : proc ByteString :=
    (* TODO: read index handle and read its data *)
    Ret BS.empty.

  Definition recover (ident: uint32) (fd:Fd) : proc Tbl.t :=
    index <- Call (inject (Data.NewArray _));
      indexData <- readIndexData fd;
      _ <- Loop (fun indexData =>
              match decode (Ty IndexEntry.ty) indexData with
              | Some (e, n) => _ <- Data.arrayAppend index e;
                                Continue (BS.drop n indexData)
              | None => LoopRet tt
              end) indexData;
      Ret {| Tbl.ident := ident;
             Tbl.fd := fd;
             Tbl.index := index |}.

  Module TblWriter.
    Record t :=
      mk {
        fd : Fd;
        fileOffset : IORef ty.uint64;
        (* these are all for the current index entry *)
        indexOffset : IORef ty.uint64;
        indexMin : IORef ty.uint64; (* key *)
        indexMax : IORef ty.uint64;
        (* this is used to track whether the index is entry;

          for verification purposes the only relevant fact is whether it's 0 (in
          which the other index refs should be ignored) or non-zero, but its
          actual value is also used to determine when entries should be split *)
        indexNumKeys : IORef ty.uint64;
        (* these are finished index entries *)
        indexEntries : Array IndexEntry.ty;
      }.
  End TblWriter.

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

  (* create the current index entry *)
  Definition flushEntry (t:TblWriter.t) : proc unit :=
    numKeys <- Data.readIORef t.(TblWriter.indexNumKeys);
      if intCmp numKeys int_val0 == Eq
      then Ret tt (* need to gracefully handle having no entry to flush, so that
      flushes are a no-op;

      concretely we periodically flush but also need to flush before create,
      which can result in a double-flush *)
      else
        fileOffset <- Data.readIORef t.(TblWriter.fileOffset);
      indexOffset <- Data.readIORef t.(TblWriter.indexOffset);
      let indexLength := uint64_to_uint32 (intSub fileOffset indexOffset) in
      indexMin <- Data.readIORef t.(TblWriter.indexMin);
        indexMax <- Data.readIORef t.(TblWriter.indexMax);
        let e := (indexOffset, indexLength, indexMin, indexMax) in
        _ <- Data.arrayAppend t.(TblWriter.indexEntries) e;
          (* clear current index entry *)
          _ <- Data.writeIORef t.(TblWriter.indexNumKeys) int_val0;
          Ret tt.

  Definition putEntry (t:TblWriter.t) (e: Entry.t) : proc unit :=
    start <- Data.readIORef t.(TblWriter.fileOffset);
      numKeys <- Data.readIORef t.(TblWriter.indexNumKeys);
      _ <- if intCmp numKeys int_val0 == Eq then
            (* initialize a new index entry *)
            _ <- Data.writeIORef t.(TblWriter.indexMin) e.(Entry.key);
              _ <- Data.writeIORef t.(TblWriter.indexOffset) start;
              Ret tt
          else Ret tt;
      let data := encode e in
      _ <- lift (FS.append t.(TblWriter.fd) data);
        _ <- Data.modifyIORef t.(TblWriter.fileOffset) (uint64.(intPlus) (BS.length data));
        _ <- Data.writeIORef t.(TblWriter.indexMax) e.(Entry.key);
        _ <- Data.writeIORef t.(TblWriter.indexNumKeys) (uint64.(intPlus) numKeys int_val1);
        _ <- if intCmp numKeys (uint64.(fromNum) 9) == Gt then
              flushEntry t
            else Ret tt;
        Ret tt.

  (* consumes the table writer and finishes writing out the table *)
  Definition create (t:TblWriter.t) (id:uint32) : proc Tbl.t :=
    _ <- flushEntry t;
      numEntries <- Data.arrayLength t.(TblWriter.indexEntries);
      indexEntries <- Loop (fun '(i, bs) =>
                  if intCmp i numEntries == Eq then LoopRet bs
                  else
                    e <- Data.arrayGet t.(TblWriter.indexEntries) i;
                    let encoded := encode e in
                    Continue (uint64.(intPlus) i int_val1, BS.append bs encoded))
                   (int_val0, BS.empty);
      indexStart <- Data.readIORef t.(TblWriter.fileOffset);
      let indexLength := uint64_to_uint32 (BS.length indexEntries) in
      let indexHandle := encode (indexStart, indexLength) in
      let indexData := BS.append indexEntries indexHandle in
      _ <- lift (FS.append t.(TblWriter.fd) indexData);
      Ret {| Tbl.fd := TblWriter.fd t;
             Tbl.ident := id;
             Tbl.index := TblWriter.indexEntries t; |}.

End Table.
