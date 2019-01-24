From RecoveryRefinement Require Import Database.Base.
From RecoveryRefinement Require Import Database.BinaryEncoding.

Import UIntNotations.

Module Table.
  Module IndexEntry.
    Record t :=
      mk { handle: SliceHandle.t;
           keys: Key * Key; }.

    Instance t_enc : Encodable t.
    Proof.
      refine {| encode := fun e => BS.append (encode e.(handle)) (encode e.(keys));
                decode := decodeBind (decode SliceHandle.t)
                                     (fun h => decodeBind (decode (Key * Key))
                                      (fun ks => decodeRet (mk h ks))); |}.
    Defined.
  End IndexEntry.

  (* reference to a read-only table *)
  Module Tbl.
    (* note that unlike in specious-db, tables do not track an identifer; it's
    only used to compute the table's filename, and that responsibility can
    simply be shifted to the manifest *)
    Record t :=
      mk { fd : Fd;
           index : Array IndexEntry.t; }.
  End Tbl.

  Module ReadIterator.
    Record t :=
      mk { offset : IORef uint64;
           buffer : IORef ByteString;
           length : uint64; }.
  End ReadIterator.

  Import EqualDecNotation.

  Import ProcNotations.
  Local Open Scope proc.

  Definition readAll (t:Tbl.t) : proc ReadIterator.t :=
    index <- Data.newIORef 0%u64;
      buf <- Data.newIORef BS.empty;
      Ret (ReadIterator.mk index buf 0).

  (* [fill] attempts to fill the iterator buffer, and returns true if it
  succeeds *)
  Definition fill (t:Tbl.t) (it:ReadIterator.t) : proc bool :=
    offset <- Data.readIORef it.(ReadIterator.offset);
      data <- lift (FS.readAt t.(Tbl.fd) offset 4096);
      if BS.length data == 0 then Ret false
      else (_ <- Data.modifyIORef it.(ReadIterator.offset) (fun o => o + (BS.length data))%u64;
              (* technically this is known to be unnecessary if len - offset >= 4096 *)
              let newData := BS.take (BS.length data - offset)%u64 data in
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

  Definition keyWithin (k:Key) (bounds: Key * Key) : bool :=
    let (min, max) := bounds in
    match compare min k with
    | Lt => false
    | _ => match compare k max with
          | Gt => false
          | _ => true
          end
    end.

  Definition indexSearch (t:Tbl.t) (k:Key) : proc (option SliceHandle.t) :=
    sz <- Data.arrayLength t.(Tbl.index);
      Loop (fun i =>
              if compare i sz == Eq
              then LoopRet None
              else
                h <- Data.arrayGet t.(Tbl.index) i;
                if keyWithin k h.(IndexEntry.keys)
                then LoopRet (Some h.(IndexEntry.handle))
                else Continue (i + 1))%u64 0.

  Definition readHandle (t:Tbl.t) (h:SliceHandle.t) : proc ByteString :=
    lift (FS.readAt t.(Tbl.fd) h.(SliceHandle.offset) h.(SliceHandle.length)).

  Inductive TableSearchResult :=
  | Missing
  | NotInTable
  | Found (v:Value)
  .

  Definition get (t:Tbl.t) (k:Key) : proc TableSearchResult :=
    mh <- indexSearch t k;
      match mh with
      | Some h =>
        data <- readHandle t h;
          Loop (fun data =>
                  match decode Entry.t data with
                  | Some (e, n) =>
                    if e.(Entry.key) == k
                    then LoopRet (Found e.(Entry.value))
                    else Continue (BS.drop n data)
                  | None => LoopRet Missing
                  end) data
      | None => Ret NotInTable
      end.

  Definition readIndexData (fd:Fd) : proc ByteString :=
    sz <- Call (inject (FS.Size fd));
      let headerLength := fromNum 16 in
      data <- lift (FS.readAt fd (sz - headerLength)%u64 headerLength);
        Ret data.

  Definition recover (fd:Fd) : proc Tbl.t :=
    index <- Call (inject (Data.NewArray _));
      indexData <- readIndexData fd;
      _ <- Loop (fun indexData =>
              match decode IndexEntry.t indexData with
              | Some (e, n) => _ <- Data.arrayAppend index e;
                                Continue (BS.drop n indexData)
              | None => LoopRet tt
              end) indexData;
      Ret {| Tbl.fd := fd;
             Tbl.index := index |}.

  Module TblWriter.
    Record t :=
      mk {
        fd : Fd;
        fileOffset : IORef uint64;
        (* these are all for the current index entry *)
        indexOffset : IORef uint64;
        indexMin : IORef uint64; (* key *)
        indexMax : IORef uint64;
        (* this is used to track whether the index is entry;

          for verification purposes the only relevant fact is whether it's 0 (in
          which the other index refs should be ignored) or non-zero, but its
          actual value is also used to determine when entries should be split *)
        indexNumKeys : IORef uint64;
        (* these are finished index entries *)
        indexEntries : Array IndexEntry.t;
      }.
  End TblWriter.

  Definition new (fh:Fd) : proc TblWriter.t :=
    fileOffset <- Data.newIORef 0%u64;
      indexOffset <- Data.newIORef 0%u64;
      indexMin <- Data.newIORef 0%u64;
      indexMax <- Data.newIORef 0%u64;
      indexNumKeys <- Data.newIORef 0%u64;
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
      if numKeys == 0
      then Ret tt (* need to gracefully handle having no entry to flush, so that
      flushes are a no-op;

      concretely we periodically flush but also need to flush before create,
      which can result in a double-flush *)
      else
        fileOffset <- Data.readIORef t.(TblWriter.fileOffset);
      indexOffset <- Data.readIORef t.(TblWriter.indexOffset);
      let indexLength := (fileOffset - indexOffset)%u64 in
      let indexHandle := {| SliceHandle.offset := indexOffset;
                            SliceHandle.length := indexLength; |} in
      indexMin <- Data.readIORef t.(TblWriter.indexMin);
        indexMax <- Data.readIORef t.(TblWriter.indexMax);
        let e := {| IndexEntry.handle := indexHandle;
                    IndexEntry.keys := (indexMin, indexMax); |} in
        _ <- Data.arrayAppend t.(TblWriter.indexEntries) e;
          (* clear current index entry *)
          _ <- Data.writeIORef t.(TblWriter.indexNumKeys) 0;
          Ret tt.

  Definition putEntry (t:TblWriter.t) (e: Entry.t) : proc unit :=
    start <- Data.readIORef t.(TblWriter.fileOffset);
      numKeys <- Data.readIORef t.(TblWriter.indexNumKeys);
      _ <- if numKeys == 0 then
            (* initialize a new index entry *)
            _ <- Data.writeIORef t.(TblWriter.indexMin) e.(Entry.key);
              _ <- Data.writeIORef t.(TblWriter.indexOffset) start;
              Ret tt
          else Ret tt;
      let data := encode e in
      _ <- lift (FS.append t.(TblWriter.fd) data);
        _ <- Data.modifyIORef t.(TblWriter.fileOffset) (fun o => o + (BS.length data))%u64;
        _ <- Data.writeIORef t.(TblWriter.indexMax) e.(Entry.key);
        _ <- Data.writeIORef t.(TblWriter.indexNumKeys) (numKeys + 1)%u64;
        _ <- if compare numKeys 9 == Gt then
              flushEntry t
            else Ret tt;
        Ret tt.

  (* consumes the table writer and finishes writing out the table *)
  Definition create (t:TblWriter.t) : proc Tbl.t :=
    _ <- flushEntry t;
      numEntries <- Data.arrayLength t.(TblWriter.indexEntries);
      indexEntries <- Loop (fun '(i, bs) =>
                  if i == numEntries then LoopRet bs
                  else
                    e <- Data.arrayGet t.(TblWriter.indexEntries) i;
                    let encoded := encode e in
                    Continue (i + 1, BS.append bs encoded)%u64)
                   (0%u64, BS.empty);
      indexStart <- Data.readIORef t.(TblWriter.fileOffset);
      let indexLength := BS.length indexEntries in
      let indexHandle := encode (indexStart, indexLength) in
      let indexData := BS.append indexEntries indexHandle in
      _ <- lift (FS.append t.(TblWriter.fd) indexData);
      Ret {| Tbl.fd := TblWriter.fd t;
             Tbl.index := TblWriter.indexEntries t; |}.

End Table.
