From RecoveryRefinement Require Import Database.Base.
From RecoveryRefinement Require Import Database.BinaryEncoding.

Module Tbl.
  Record t :=
    mk { index: HashTable uint64; (* key -> offset *)
         file: Fd;
         }.
End Tbl.

Module Db.
  Record t :=
    mk { wbuffer: IORef (HashTable Value); (* key -> value *)
         rbuffer: IORef (HashTable Value);
         bufferL: LockRef;
         table: IORef Tbl.t;
         tableName: IORef Path; (* this is the entire state of the manifest *)
         tableL: LockRef; (* protects both table and tableName *)
         compactionL: LockRef; (* protects constructing shadow tables *)
       }.
End Db.

Import ProcNotations.
Local Open Scope proc.

Import UIntNotations.
Local Open Scope u64.

Import EqualDecNotation.

Implicit Types (t:Tbl.t) (db:Db.t) (index:HashTable uint64).
Implicit Types (k:Key) (v:Value) (p:Path) (fd:Fd).

(* create a new, empty table at p

tables are immutable but for cleanliness of representation we back it with an
 empty, open file anyway *)
Definition createTbl p : proc _ :=
  index <- Data.newHashTable _;
    _ <- (fd <- FS.create p;
           FS.close fd);
    fd <- FS.open p;
    Ret {| Tbl.index := index;
           Tbl.file := fd; |}.

(* fd points to a complete table, which is just a sequence of entries *)
Definition readTableIndex fd index : proc unit :=
  (* loop invariant: file starts with bs at off, and bs is at the beginning of a
  sequence of encoded entires (a suffix of all the entires in fd), and index has
  pointers to everything before bs *)
  Loop (fun '(off,bs) =>
          match decode Entry.t bs with
          | Some (e, n) =>
            (* here we need to compute the offset to the value within the
            encoded entry; we know the key is 8 bytes, so the overall offset to
            the value is always 8+off *)
            let valueOffset := 8+off in
            _ <- Data.hashTableAlter index e.(Entry.key)
                                              (fun _ => Some valueOffset);
              Continue (off+n, BS.drop n bs)
          | None =>
            bs' <- FS.readAt fd (off+BS.length bs) 4096;
              if BS.length bs' == 0
              then LoopRet tt (* no more data; should only happen if bs was
              already empty since the table has a sequence of entries *)
              else Continue (off, BS.append bs bs')
          end)
       (0, BS.empty).

Definition recoverTbl (p:Path) : proc Tbl.t :=
  index <- Data.newHashTable _;
    fd <- FS.open p;
    _ <- readTableIndex fd index;
  Ret {| Tbl.index := index;
         Tbl.file := fd |}.

(* read an array encoded at off efficiently (using a single bulk IO in the
common case) *)
Definition readValue fd off : proc ByteString :=
  bs <- FS.readAt fd off 4096;
    match decode uint64 bs with
    | Some (len, n) =>
      let bs := BS.drop n bs in
      (* bs' should be the remainder of the value at off *)
      bs' <- if compare (BS.length bs) len == Lt then
              FS.readAt fd (off+BS.length bs) (len - BS.length bs)
            else Ret BS.empty;
        Ret (BS.append bs bs')
    | None => Ret BS.empty
    end.

Definition tblRead t k : proc (option ByteString) :=
  moff <- Data.hashTableLookup t.(Tbl.index) k;
    match moff with
    | Some off =>
      bs <- readValue t.(Tbl.file) off;
        Ret (Some bs)
    | None => Ret None
    end.

Module TblW.
  (* NOTE: we can buffer writes here conveniently for efficiency (otherwise
  every entry gets its own write syscall) *)
  Record t :=
    mk { index: HashTable uint64;
         name: Path;
         file: Fd;
         offset: IORef uint64; }.
End TblW.

Definition newTblW p : proc TblW.t :=
  index <- Data.newHashTable _;
    file <- FS.create p;
    offset <- Data.newIORef 0;
    Ret {| TblW.index := index;
           TblW.name := p;
           TblW.file := file;
           TblW.offset := offset; |}.

Definition tblWGetOffset (w:TblW.t) : proc uint64 :=
  Data.readIORef w.(TblW.offset).

Definition tblWAppend (w:TblW.t) (bs:ByteString) : proc _ :=
  _ <- FS.append w.(TblW.file) bs;
  Data.modifyIORef w.(TblW.offset) (fun o => o + BS.length bs).

Definition tblWClose (w:TblW.t) : proc Tbl.t :=
  (* if we're buffering now is the chance to flush *)
  _ <- FS.close w.(TblW.file);
    fd <- FS.open w.(TblW.name);
    Ret {| Tbl.file := fd;
           Tbl.index := w.(TblW.index); |}.

Definition tblPut (w:TblW.t) k v : proc unit :=
  o <- tblWGetOffset w;
    let (kbs, vbs) := (encode k, encode (array64 v)) in
    (* this offset is to the _value_ being written, not the entry *)
    let o' := o + BS.length kbs in
    _ <- Data.hashTableAlter w.(TblW.index) k (fun _ => Some o');
    tblWAppend w (BS.append kbs vbs).

Definition newDb : proc Db.t :=
  wbuffer <- Bind (Data.newHashTable _) Data.newIORef;
  rbuffer <- Bind (Data.newHashTable _) Data.newIORef;
    bufferL <- Data.newLock;
    tableName <- Data.newIORef "table";
    table <- createTbl "table";
    _ <- FS.atomicCreate "manifest" (BS.fromString "table");
    tableRef <- Data.newIORef table;
    tableL <- Data.newLock;
    compactionL <- Data.newLock;
    Ret {| Db.wbuffer := wbuffer;
           Db.rbuffer := rbuffer;
           Db.bufferL := bufferL;
           Db.tableName := tableName;
           Db.table := tableRef;
           Db.tableL := tableL;
           Db.compactionL := compactionL |}.

Definition read db k : proc (option ByteString) :=
  _ <- Data.lockAcquire Reader db.(Db.bufferL);
    mbs <- (b <- Data.readIORef db.(Db.wbuffer);
             Data.hashTableLookup b k);
    match mbs with
    | Some bs => _ <- Data.lockRelease Reader db.(Db.bufferL);
                  Ret (Some bs)
    | None => mbs <- (b <- Data.readIORef db.(Db.rbuffer);
                      Data.hashTableLookup b k);
               match mbs with
               | Some bs => _ <- Data.lockRelease Reader db.(Db.bufferL);
                             Ret (Some bs)
               | None =>
                 _ <- Data.lockAcquire Reader db.(Db.tableL);
                   tbl <- Data.readIORef db.(Db.table);
                   r <- tblRead tbl k;
                   _ <- Data.lockRelease Reader db.(Db.tableL);
                   _ <- Data.lockRelease Reader db.(Db.bufferL);
                   Ret r
               end
    end.

Definition write db k v : proc unit :=
  _ <- Data.lockAcquire Writer db.(Db.bufferL);
    _ <- (b <- Data.readIORef db.(Db.wbuffer);
           Data.hashTableAlter b k (fun _ => Some v));
    _ <- Data.lockRelease Writer db.(Db.bufferL);
    Ret tt.

(* freshTable can be any function, as long as it doesn't return p or "manifest";
ideally it would take table[n] and increment n, in order to get nice
filenames *)
Definition freshTable p : Path :=
  (p ++ "0")%string.

(* put all (key,value) pairs in (read) buffer to w *)
Definition tblPutBuffer (w:TblW.t) (b:HashTable ByteString) : proc _ :=
  a <- Data.hashTableReadAll b;
    sz <- Data.arrayLength a;
    Loop (fun i => if i == sz
                then LoopRet tt
                else kv <- Data.arrayGet a i;
                  let '(k,v) := kv in
                  _ <- tblPut w k v;
                    Continue (i+1)) 0.

(* add all of table t to the table w being created; skip any keys in the (read)
   buffer b since those writes overwrite old ones *)
Definition tblPutOldTable (w:TblW.t) t (b:HashTable ByteString) : proc _ :=
  Loop (fun '(off,bs) =>
          match decode Entry.t bs with
          | Some (e, n) =>
            let 'Entry.mk k v := e in
            m <- Data.hashTableLookup b k;
              _ <- match m with
                  | Some _ =>
                    (* key has an overwrite in the buffer, so the old value is
                    redundant (this is the only compaction going on - otherwise
                    writes are just getting appended to the table) *)
                    Ret tt
                  | None => tblPut w k v
                  end;
              Continue (off+n, BS.drop n bs)
          | None =>
            bs' <- FS.readAt t.(Tbl.file) (off+BS.length bs) 4096;
              if BS.length bs' == 0
              then LoopRet tt (* no more data; should only happen if bs was
              already empty since the table has a sequence of entries *)
              else Continue (off, BS.append bs bs')
          end)
       (0, BS.empty).

(* build a new shadow table that incorporates the current table and the buffer
buf; assumes a compaction lock (for the shadow table), read lock over the table
(though see comment below about this being redundant), and that buf is
read-only *)
Definition constructNewTable db buf :
  proc (Path (* old table name *) *
        Tbl.t (* old table *) *
        Tbl.t (* newly constructed table *)) :=
  oldName <- Data.readIORef db.(Db.tableName);
    let name := freshTable oldName in
    w <- newTblW name;
      oldTable <- Data.readIORef db.(Db.table);
      _ <- tblPutOldTable w oldTable buf;
      _ <- tblPutBuffer w buf;
      t <- tblWClose w;
      Ret (oldName, oldTable, t).

Definition compact db : proc unit :=
  _ <- Data.lockAcquire Writer db.(Db.compactionL);

    (* first, snapshot the buffered writes that will go into this table *)
    _ <- Data.lockAcquire Writer db.(Db.bufferL);
    buf <- Data.readIORef db.(Db.wbuffer);
    _ <- (empty_wbuffer <- Data.newHashTable _;
           Data.writeIORef db.(Db.wbuffer) empty_wbuffer);
    _ <- Data.writeIORef db.(Db.rbuffer) buf;
    _ <- Data.lockRelease Writer db.(Db.bufferL);

    (* next, construct the new table *)
      (* NOTE: it's weird to acquire this table lock:

        - what happens between rrelease(tableL) and wlock(tableL)? a reader
          would be fine since the old table is still valid, and the compaction
          log prevents another writer from suddenly installing a new table

        - given this reasoning, why lock the tableL at all? it feels like the
       compactionL also implicitly acquires a read-lock on the tableL, since it
       guarantees only the compaction itself could be messing with the table,
       which it won't do till later in this function *)
      _ <- Data.lockAcquire Reader db.(Db.tableL);
      oldTable_t <- constructNewTable db buf;
      let '(oldTableName, oldTable, t) := oldTable_t in
      let newTable := freshTable oldTableName in
      _ <- Data.lockRelease Reader db.(Db.tableL);

      (* next, install it (persistently and in-memory) *)
      _ <- Data.lockAcquire Writer db.(Db.tableL);
      _ <- Data.writeIORef db.(Db.table) t;
      _ <- Data.writeIORef db.(Db.tableName) newTable;
      _ <- FS.atomicCreate "manifest" (BS.fromString newTable);
      _ <- FS.close oldTable.(Tbl.file);
      _ <- FS.delete oldTableName;
      (* note that we don't need to remove the rbuffer (it's just a cache for
      the part of the table we just persisted) *)
      _ <- Data.lockRelease Writer db.(Db.tableL);

      _ <- Data.lockRelease Writer db.(Db.compactionL);
      Ret tt.

(* recover manifest recovers the data in the manifest file, which is just the name of the actual table file *)
Definition recoverManifest : proc Path :=
  fd <- FS.open "manifest";
    sz <- FS.size fd;
    bs <- FS.readAt fd 0 sz;
    _ <- FS.close fd;
    Ret (BS.toString bs).

Fixpoint deleteOtherFiles' tableName ps : proc _ :=
  match ps with
  | nil => Ret tt
  | p::ps' =>
    _ <- (if p == tableName
         then Ret tt
         else if p == "manifest" then Ret tt
              else
                (* only tableName and "manifest" are part of the database *)
                FS.delete p);
      deleteOtherFiles' tableName ps'
  end.

Definition deleteOtherFiles tableName : proc _ :=
  ps <- FS.list;
    deleteOtherFiles' tableName ps.

Definition recover : proc Db.t :=
  tableName <- recoverManifest;
    table <- Bind (recoverTbl tableName) Data.newIORef;
    tableNameRef <- Data.newIORef tableName;

    _ <- deleteOtherFiles tableName;

    wbuffer <- Bind (Data.newHashTable _) Data.newIORef;
    rbuffer <- Bind (Data.newHashTable _) Data.newIORef;
    bufferL <- Data.newLock;
    tableL <- Data.newLock;
    compactionL <- Data.newLock;

    Ret {| Db.wbuffer := wbuffer;
           Db.rbuffer := rbuffer;
           Db.bufferL := bufferL;
           Db.tableName := tableNameRef;
           Db.table := table;
           Db.tableL := tableL;
           Db.compactionL := compactionL |}.

(* immediate shutdown; like a crash, but cleanly close all files *)
Definition shutdownDb db : proc unit :=
    _ <- Data.lockAcquire Writer db.(Db.bufferL);
    _ <- Data.lockAcquire Writer db.(Db.compactionL);
    t <- Data.readIORef db.(Db.table);
    _ <- FS.close t.(Tbl.file);
    _ <- Data.lockRelease Writer db.(Db.compactionL);
    _ <- Data.lockRelease Writer db.(Db.bufferL);
    Ret tt.

Definition closeDb db : proc unit :=
  _ <- compact db;
    shutdownDb db.
