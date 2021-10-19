(* autogenerated from github.com/mit-pdos/go-journal/obj *)
From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang Require Import ffi.disk_prelude.

From Goose Require github_com.mit_pdos.go_journal.addr.
From Goose Require github_com.mit_pdos.go_journal.buf.
From Goose Require github_com.mit_pdos.go_journal.common.
From Goose Require github_com.mit_pdos.go_journal.util.
From Goose Require github_com.mit_pdos.go_journal.wal.

(* Package obj atomically installs objects from  modified buffers in their
   corresponding disk blocks and writes the blocks to the write-ahead log.  The
   upper layers are responsible for locking and lock ordering. *)

(* Log mediates access to object loading and installation.

   There is only one Log object. *)
Definition Log := struct.decl [
  "mu" :: lockRefT;
  "log" :: struct.ptrT wal.Walog;
  "pos" :: wal.LogPosition
].

(* MkLog recovers the object logging system
   (or initializes from an all-zero disk). *)
Definition MkLog: val :=
  rec: "MkLog" "d" :=
    let: "log" := struct.new Log [
      "mu" ::= lock.new #();
      "log" ::= wal.MkLog "d";
      "pos" ::= #0
    ] in
    "log".

(* Read a disk object into buf *)
Definition Log__Load: val :=
  rec: "Log__Load" "l" "addr" "sz" :=
    let: "blk" := wal.Walog__Read (struct.loadF Log "log" "l") (struct.get addr.Addr "Blkno" "addr") in
    let: "b" := buf.MkBufLoad "addr" "sz" "blk" in
    "b".

(* Installs bufs into their blocks and returns the blocks.
   A buf may only partially update a disk block and several bufs may
   apply to the same disk block. Assume caller holds commit lock. *)
Definition Log__installBufsMap: val :=
  rec: "Log__installBufsMap" "l" "bufs" :=
    let: "blks" := NewMap (slice.T byteT) #() in
    ForSlice (refT (struct.t buf.Buf)) <> "b" "bufs"
      (if: (struct.loadF buf.Buf "Sz" "b" = common.NBITBLOCK)
      then MapInsert "blks" (struct.get addr.Addr "Blkno" (struct.loadF buf.Buf "Addr" "b")) (struct.loadF buf.Buf "Data" "b")
      else
        let: "blk" := ref (zero_val (slice.T byteT)) in
        let: ("mapblk", "ok") := MapGet "blks" (struct.get addr.Addr "Blkno" (struct.loadF buf.Buf "Addr" "b")) in
        (if: "ok"
        then "blk" <-[slice.T byteT] "mapblk"
        else
          "blk" <-[slice.T byteT] wal.Walog__Read (struct.loadF Log "log" "l") (struct.get addr.Addr "Blkno" (struct.loadF buf.Buf "Addr" "b"));;
          MapInsert "blks" (struct.get addr.Addr "Blkno" (struct.loadF buf.Buf "Addr" "b")) (![slice.T byteT] "blk"));;
        buf.Buf__Install "b" (![slice.T byteT] "blk"));;
    "blks".

Definition Log__installBufs: val :=
  rec: "Log__installBufs" "l" "bufs" :=
    let: "blks" := ref (zero_val (slice.T (struct.t wal.Update))) in
    let: "bufmap" := Log__installBufsMap "l" "bufs" in
    MapIter "bufmap" (λ: "blkno" "data",
      "blks" <-[slice.T (struct.t wal.Update)] SliceAppend (struct.t wal.Update) (![slice.T (struct.t wal.Update)] "blks") (wal.MkBlockData "blkno" "data"));;
    ![slice.T (struct.t wal.Update)] "blks".

(* Acquires the commit log, installs the buffers into their
   blocks, and appends the blocks to the in-memory log. *)
Definition Log__doCommit: val :=
  rec: "Log__doCommit" "l" "bufs" :=
    lock.acquire (struct.loadF Log "mu" "l");;
    let: "blks" := Log__installBufs "l" "bufs" in
    util.DPrintf #3 (#(str"doCommit: %v bufs
    ")) #();;
    let: ("n", "ok") := wal.Walog__MemAppend (struct.loadF Log "log" "l") "blks" in
    struct.storeF Log "pos" "l" "n";;
    lock.release (struct.loadF Log "mu" "l");;
    ("n", "ok").

(* Commit dirty bufs of the transaction into the log, and perhaps wait. *)
Definition Log__CommitWait: val :=
  rec: "Log__CommitWait" "l" "bufs" "wait" :=
    let: "commit" := ref_to boolT #true in
    (if: slice.len "bufs" > #0
    then
      let: ("n", "ok") := Log__doCommit "l" "bufs" in
      (if: ~ "ok"
      then
        util.DPrintf #10 (#(str"memappend failed; log is too small
        ")) #();;
        "commit" <-[boolT] #false
      else
        (if: "wait"
        then wal.Walog__Flush (struct.loadF Log "log" "l") "n"
        else #()))
    else
      util.DPrintf #5 (#(str"commit read-only trans
      ")) #());;
    ![boolT] "commit".

(* NOTE: this is coarse-grained and unattached to the transaction ID *)
Definition Log__Flush: val :=
  rec: "Log__Flush" "l" :=
    lock.acquire (struct.loadF Log "mu" "l");;
    let: "pos" := struct.loadF Log "pos" "l" in
    lock.release (struct.loadF Log "mu" "l");;
    wal.Walog__Flush (struct.loadF Log "log" "l") "pos";;
    #true.

(* LogSz returns 511 (the size of the wal log) *)
Definition Log__LogSz: val :=
  rec: "Log__LogSz" "l" :=
    wal.LOGSZ.

Definition Log__Shutdown: val :=
  rec: "Log__Shutdown" "l" :=
    wal.Walog__Shutdown (struct.loadF Log "log" "l");;
    #().
