(* autogenerated from github.com/mit-pdos/tulip/paxos *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_com.mit_pdos.tulip.params.
From Goose Require github_com.mit_pdos.tulip.quorum.
From Goose Require github_com.mit_pdos.tulip.util.
From Goose Require github_com.tchajed.marshal.

From Perennial.goose_lang Require Import ffi.grove_prelude.

Definition Paxos := struct.decl [
  "nidme" :: uint64T;
  "peers" :: slice.T uint64T;
  "addrm" :: mapT uint64T;
  "sc" :: uint64T;
  "fname" :: stringT;
  "mu" :: ptrT;
  "cv" :: ptrT;
  "hb" :: boolT;
  "termc" :: uint64T;
  "terml" :: uint64T;
  "log" :: slice.T stringT;
  "lsnc" :: uint64T;
  "iscand" :: boolT;
  "isleader" :: boolT;
  "termp" :: uint64T;
  "entsp" :: slice.T stringT;
  "respp" :: mapT boolT;
  "lsnpeers" :: mapT uint64T;
  "conns" :: mapT grove_ffi.Connection
].

Definition MAX_NODES : expr := #16.

Definition Paxos__leading: val :=
  rec: "Paxos__leading" "px" :=
    struct.loadF Paxos "isleader" "px".

Definition CMD_EXTEND : expr := #0.

Definition CMD_APPEND : expr := #1.

Definition CMD_PREPARE : expr := #2.

Definition CMD_ADVANCE : expr := #3.

Definition CMD_ACCEPT : expr := #4.

Definition CMD_EXPAND : expr := #5.

Definition logAppend: val :=
  rec: "logAppend" "fname" "ent" :=
    let: "bs" := NewSliceWithCap byteT #0 #32 in
    let: "bs1" := marshal.WriteInt "bs" CMD_APPEND in
    let: "bs2" := util.EncodeString "bs1" "ent" in
    grove_ffi.FileAppend "fname" "bs2";;
    #().

Definition Paxos__Submit: val :=
  rec: "Paxos__Submit" "px" "v" :=
    Mutex__Lock (struct.loadF Paxos "mu" "px");;
    (if: (~ (Paxos__leading "px"))
    then
      Mutex__Unlock (struct.loadF Paxos "mu" "px");;
      (#0, #0)
    else
      let: "lsn" := slice.len (struct.loadF Paxos "log" "px") in
      struct.storeF Paxos "log" "px" (SliceAppend stringT (struct.loadF Paxos "log" "px") "v");;
      let: "term" := struct.loadF Paxos "termc" "px" in
      logAppend (struct.loadF Paxos "fname" "px") "v";;
      Mutex__Unlock (struct.loadF Paxos "mu" "px");;
      Cond__Broadcast (struct.loadF Paxos "cv" "px");;
      ("lsn", "term")).

Definition Paxos__Lookup: val :=
  rec: "Paxos__Lookup" "px" "lsn" :=
    Mutex__Lock (struct.loadF Paxos "mu" "px");;
    (if: (struct.loadF Paxos "lsnc" "px") ≤ "lsn"
    then
      Mutex__Unlock (struct.loadF Paxos "mu" "px");;
      (#(str""), #false)
    else
      let: "v" := SliceGet stringT (struct.loadF Paxos "log" "px") "lsn" in
      Mutex__Unlock (struct.loadF Paxos "mu" "px");;
      ("v", #true)).

Definition Paxos__gettermc: val :=
  rec: "Paxos__gettermc" "px" :=
    struct.loadF Paxos "termc" "px".

Definition Paxos__getlsnc: val :=
  rec: "Paxos__getlsnc" "px" :=
    struct.loadF Paxos "lsnc" "px".

Definition Paxos__WaitUntilSafe: val :=
  rec: "Paxos__WaitUntilSafe" "px" "lsn" "term" :=
    let: "safe" := ref (zero_val boolT) in
    let: "nretry" := ref (zero_val uint64T) in
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      Mutex__Lock (struct.loadF Paxos "mu" "px");;
      let: "termc" := Paxos__gettermc "px" in
      let: "lsnc" := Paxos__getlsnc "px" in
      Mutex__Unlock (struct.loadF Paxos "mu" "px");;
      (if: "term" ≠ "termc"
      then Break
      else
        (if: "lsn" < "lsnc"
        then
          "safe" <-[boolT] #true;;
          Break
        else
          (if: (![uint64T] "nretry") = params.N_RETRY_REPLICATED
          then Break
          else
            "nretry" <-[uint64T] ((![uint64T] "nretry") + #1);;
            time.Sleep params.NS_REPLICATED_INTERVAL;;
            Continue))));;
    ![boolT] "safe".

Definition logPrepare: val :=
  rec: "logPrepare" "fname" "term" :=
    let: "bs" := NewSliceWithCap byteT #0 #16 in
    let: "bs1" := marshal.WriteInt "bs" CMD_PREPARE in
    let: "bs2" := marshal.WriteInt "bs1" "term" in
    grove_ffi.FileAppend "fname" "bs2";;
    #().

(* Return values:
   1. @term: New term in which this node attempts to be the leader.
   2. @lsn: LSN after which log entries whose committedness is yet known, and
   hence the content need to be resolved through the leader-election phase. *)
Definition Paxos__nominate: val :=
  rec: "Paxos__nominate" "px" :=
    let: "term" := util.NextAligned (struct.loadF Paxos "termc" "px") MAX_NODES (struct.loadF Paxos "nidme" "px") in
    struct.storeF Paxos "termc" "px" "term";;
    struct.storeF Paxos "isleader" "px" #false;;
    let: "lsn" := struct.loadF Paxos "lsnc" "px" in
    let: "ents" := NewSlice stringT ((slice.len (struct.loadF Paxos "log" "px")) - "lsn") in
    SliceCopy stringT "ents" (SliceSkip stringT (struct.loadF Paxos "log" "px") "lsn");;
    struct.storeF Paxos "iscand" "px" #true;;
    struct.storeF Paxos "termp" "px" (struct.loadF Paxos "terml" "px");;
    struct.storeF Paxos "entsp" "px" "ents";;
    struct.storeF Paxos "respp" "px" (NewMap uint64T boolT #());;
    MapInsert (struct.loadF Paxos "respp" "px") (struct.loadF Paxos "nidme" "px") #true;;
    (* fmt.Printf("[paxos %d] Become a candidate in %d.\n", px.nidme, px.termc) *)
    logPrepare (struct.loadF Paxos "fname" "px") "term";;
    ("term", "lsn").

Definition Paxos__stepdown: val :=
  rec: "Paxos__stepdown" "px" "term" :=
    struct.storeF Paxos "iscand" "px" #false;;
    struct.storeF Paxos "isleader" "px" #false;;
    (if: (struct.loadF Paxos "termc" "px") = "term"
    then #()
    else
      struct.storeF Paxos "termc" "px" "term";;
      logPrepare (struct.loadF Paxos "fname" "px") "term";;
      #()).

(* Argument:
   1. @lsn: LSN after which log entries whose committedness is yet known, and
   hence the content need to be resolved through the leader-election phase.

   Return values:
   1. @terml: Log term of this node (which is also the largest accepted term
   before @px.termc).
   2. @ents: All entries after @lsn. *)
Definition Paxos__prepare: val :=
  rec: "Paxos__prepare" "px" "lsn" :=
    (if: (slice.len (struct.loadF Paxos "log" "px")) ≤ "lsn"
    then (struct.loadF Paxos "terml" "px", NewSlice stringT #0)
    else
      let: "ents" := NewSlice stringT ((slice.len (struct.loadF Paxos "log" "px")) - "lsn") in
      SliceCopy stringT "ents" (SliceSkip stringT (struct.loadF Paxos "log" "px") "lsn");;
      (struct.loadF Paxos "terml" "px", "ents")).

Definition Paxos__collect: val :=
  rec: "Paxos__collect" "px" "nid" "term" "ents" :=
    let: (<>, "recved") := MapGet (struct.loadF Paxos "respp" "px") "nid" in
    (if: "recved"
    then #()
    else
      (if: "term" < (struct.loadF Paxos "termp" "px")
      then
        MapInsert (struct.loadF Paxos "respp" "px") "nid" #true;;
        #()
      else
        (if: ("term" = (struct.loadF Paxos "termp" "px")) && ((slice.len "ents") ≤ (slice.len (struct.loadF Paxos "entsp" "px")))
        then
          MapInsert (struct.loadF Paxos "respp" "px") "nid" #true;;
          #()
        else
          struct.storeF Paxos "termp" "px" "term";;
          struct.storeF Paxos "entsp" "px" "ents";;
          MapInsert (struct.loadF Paxos "respp" "px") "nid" #true;;
          #()))).

Definition Paxos__cquorum: val :=
  rec: "Paxos__cquorum" "px" "n" :=
    (quorum.ClassicQuorum (struct.loadF Paxos "sc" "px")) ≤ "n".

(* Note that we could have defined @logAdvance to take @ents only, since @term
   and @lsn can be determined directly from the state for the
   candidate. However, a similar transition also happens on followers, but @term
   and @lsn are passed through function arguments rather than from state. Given
   that advance is used only on failure cases, defining a single interface
   simplify things a bit without hurting too much of the performance. *)
Definition logAdvance: val :=
  rec: "logAdvance" "fname" "term" "lsn" "ents" :=
    let: "bs" := NewSliceWithCap byteT #0 #64 in
    let: "bs1" := marshal.WriteInt "bs" CMD_ADVANCE in
    let: "bs2" := marshal.WriteInt "bs1" "term" in
    let: "bs3" := marshal.WriteInt "bs2" "lsn" in
    let: "bs4" := util.EncodeStrings "bs3" "ents" in
    grove_ffi.FileAppend "fname" "bs4";;
    #().

Definition Paxos__ascend: val :=
  rec: "Paxos__ascend" "px" :=
    (if: (~ (Paxos__cquorum "px" (MapLen (struct.loadF Paxos "respp" "px"))))
    then #()
    else
      struct.storeF Paxos "log" "px" (SliceAppendSlice stringT (SliceTake (struct.loadF Paxos "log" "px") (struct.loadF Paxos "lsnc" "px")) (struct.loadF Paxos "entsp" "px"));;
      struct.storeF Paxos "terml" "px" (struct.loadF Paxos "termc" "px");;
      struct.storeF Paxos "iscand" "px" #false;;
      struct.storeF Paxos "isleader" "px" #true;;
      struct.storeF Paxos "lsnpeers" "px" (NewMap uint64T uint64T #());;
      (* fmt.Printf("[paxos %d] Become a leader in %d.\n", px.nidme, px.termc) *)
      logAdvance (struct.loadF Paxos "fname" "px") (struct.loadF Paxos "termc" "px") (struct.loadF Paxos "lsnc" "px") (struct.loadF Paxos "entsp" "px");;
      #()).

Definition Paxos__obtain: val :=
  rec: "Paxos__obtain" "px" "nid" :=
    let: ("lsne", "ok") := MapGet (struct.loadF Paxos "lsnpeers" "px") "nid" in
    (if: (~ "ok")
    then (slice.len (struct.loadF Paxos "log" "px"), NewSlice stringT #0)
    else
      let: "ents" := NewSlice stringT ((slice.len (struct.loadF Paxos "log" "px")) - "lsne") in
      SliceCopy stringT "ents" (SliceSkip stringT (struct.loadF Paxos "log" "px") "lsne");;
      ("lsne", "ents")).

Definition logAccept: val :=
  rec: "logAccept" "fname" "lsn" "ents" :=
    let: "bs" := NewSliceWithCap byteT #0 #64 in
    let: "bs1" := marshal.WriteInt "bs" CMD_ACCEPT in
    let: "bs2" := marshal.WriteInt "bs1" "lsn" in
    let: "bs3" := util.EncodeStrings "bs2" "ents" in
    grove_ffi.FileAppend "fname" "bs3";;
    #().

(* Arguments:
   1. @lsn: LSN at which @ents start.
   2. @term: Term to which @ents belong.
   3. @ents: Log entries.

   Return values:
   1. @lsna: LSN up to which log consistency at term @term is established. *)
Definition Paxos__accept: val :=
  rec: "Paxos__accept" "px" "lsn" "term" "ents" :=
    (if: "term" ≠ (struct.loadF Paxos "terml" "px")
    then
      (if: (struct.loadF Paxos "lsnc" "px") ≠ "lsn"
      then struct.loadF Paxos "lsnc" "px"
      else
        struct.storeF Paxos "log" "px" (SliceTake (struct.loadF Paxos "log" "px") "lsn");;
        struct.storeF Paxos "log" "px" (SliceAppendSlice stringT (struct.loadF Paxos "log" "px") "ents");;
        struct.storeF Paxos "terml" "px" "term";;
        let: "lsna" := slice.len (struct.loadF Paxos "log" "px") in
        logAdvance (struct.loadF Paxos "fname" "px") "term" "lsn" "ents";;
        "lsna")
    else
      let: "nents" := slice.len (struct.loadF Paxos "log" "px") in
      (if: ("nents" < "lsn") || (("lsn" + (slice.len "ents")) ≤ "nents")
      then "nents"
      else
        struct.storeF Paxos "log" "px" (SliceTake (struct.loadF Paxos "log" "px") "lsn");;
        struct.storeF Paxos "log" "px" (SliceAppendSlice stringT (struct.loadF Paxos "log" "px") "ents");;
        let: "lsna" := slice.len (struct.loadF Paxos "log" "px") in
        logAccept (struct.loadF Paxos "fname" "px") "lsn" "ents";;
        "lsna")).

Definition logExpand: val :=
  rec: "logExpand" "fname" "lsn" :=
    let: "bs" := NewSliceWithCap byteT #0 #16 in
    let: "bs1" := marshal.WriteInt "bs" CMD_EXPAND in
    let: "bs2" := marshal.WriteInt "bs1" "lsn" in
    grove_ffi.FileAppend "fname" "bs2";;
    #().

Definition Paxos__commit: val :=
  rec: "Paxos__commit" "px" "lsn" :=
    (if: "lsn" ≤ (struct.loadF Paxos "lsnc" "px")
    then #()
    else
      (if: (slice.len (struct.loadF Paxos "log" "px")) < "lsn"
      then
        struct.storeF Paxos "lsnc" "px" (slice.len (struct.loadF Paxos "log" "px"));;
        logExpand (struct.loadF Paxos "fname" "px") (struct.loadF Paxos "lsnc" "px");;
        #()
      else
        struct.storeF Paxos "lsnc" "px" "lsn";;
        logExpand (struct.loadF Paxos "fname" "px") "lsn";;
        #())).

(* @learn monotonically increase the commit LSN @px.lsnc in term @term to @lsn. *)
Definition Paxos__learn: val :=
  rec: "Paxos__learn" "px" "lsn" "term" :=
    (if: "term" ≠ (struct.loadF Paxos "terml" "px")
    then #()
    else
      Paxos__commit "px" "lsn";;
      #()).

Definition Paxos__forward: val :=
  rec: "Paxos__forward" "px" "nid" "lsn" :=
    let: ("lsnpeer", "ok") := MapGet (struct.loadF Paxos "lsnpeers" "px") "nid" in
    (if: (~ "ok") || ("lsnpeer" < "lsn")
    then
      MapInsert (struct.loadF Paxos "lsnpeers" "px") "nid" "lsn";;
      #true
    else #false).

Definition Paxos__push: val :=
  rec: "Paxos__push" "px" :=
    (if: (~ (Paxos__cquorum "px" ((MapLen (struct.loadF Paxos "lsnpeers" "px")) + #1)))
    then (#0, #false)
    else
      let: "lsns" := ref_to (slice.T uint64T) (NewSliceWithCap uint64T #0 (struct.loadF Paxos "sc" "px")) in
      MapIter (struct.loadF Paxos "lsnpeers" "px") (λ: <> "lsn",
        "lsns" <-[slice.T uint64T] (SliceAppend uint64T (![slice.T uint64T] "lsns") "lsn"));;
      util.Sort (![slice.T uint64T] "lsns");;
      let: "lsn" := SliceGet uint64T (![slice.T uint64T] "lsns") ((slice.len (![slice.T uint64T] "lsns")) - ((struct.loadF Paxos "sc" "px") `quot` #2)) in
      (if: "lsn" < (struct.loadF Paxos "lsnc" "px")
      then (#0, #false)
      else ("lsn", #true))).

Definition Paxos__gttermc: val :=
  rec: "Paxos__gttermc" "px" "term" :=
    (struct.loadF Paxos "termc" "px") < "term".

Definition Paxos__lttermc: val :=
  rec: "Paxos__lttermc" "px" "term" :=
    "term" < (struct.loadF Paxos "termc" "px").

Definition Paxos__latest: val :=
  rec: "Paxos__latest" "px" :=
    (struct.loadF Paxos "termc" "px") = (struct.loadF Paxos "terml" "px").

Definition Paxos__nominated: val :=
  rec: "Paxos__nominated" "px" :=
    struct.loadF Paxos "iscand" "px".

Definition Paxos__resethb: val :=
  rec: "Paxos__resethb" "px" :=
    struct.storeF Paxos "hb" "px" #false;;
    #().

Definition Paxos__heartbeat: val :=
  rec: "Paxos__heartbeat" "px" :=
    struct.storeF Paxos "hb" "px" #true;;
    #().

Definition Paxos__heartbeated: val :=
  rec: "Paxos__heartbeated" "px" :=
    struct.loadF Paxos "hb" "px".

Definition MSG_PREPARE : expr := #0.

Definition MSG_ACCEPT : expr := #1.

Definition EncodeAcceptRequest: val :=
  rec: "EncodeAcceptRequest" "term" "lsnc" "lsne" "ents" :=
    let: "bs" := NewSliceWithCap byteT #0 #64 in
    let: "bs1" := marshal.WriteInt "bs" MSG_ACCEPT in
    let: "bs2" := marshal.WriteInt "bs1" "term" in
    let: "bs3" := marshal.WriteInt "bs2" "lsnc" in
    let: "bs4" := marshal.WriteInt "bs3" "lsne" in
    let: "data" := util.EncodeStrings "bs4" "ents" in
    "data".

Definition Paxos__GetConnection: val :=
  rec: "Paxos__GetConnection" "px" "nid" :=
    Mutex__Lock (struct.loadF Paxos "mu" "px");;
    let: ("conn", "ok") := MapGet (struct.loadF Paxos "conns" "px") "nid" in
    Mutex__Unlock (struct.loadF Paxos "mu" "px");;
    ("conn", "ok").

Definition Paxos__Connect: val :=
  rec: "Paxos__Connect" "px" "nid" :=
    let: "addr" := Fst (MapGet (struct.loadF Paxos "addrm" "px") "nid") in
    let: "ret" := grove_ffi.Connect "addr" in
    (if: (~ (struct.get grove_ffi.ConnectRet "Err" "ret"))
    then
      Mutex__Lock (struct.loadF Paxos "mu" "px");;
      MapInsert (struct.loadF Paxos "conns" "px") "nid" (struct.get grove_ffi.ConnectRet "Connection" "ret");;
      Mutex__Unlock (struct.loadF Paxos "mu" "px");;
      #true
    else #false).

Definition Paxos__Send: val :=
  rec: "Paxos__Send" "px" "nid" "data" :=
    let: ("conn", "ok") := Paxos__GetConnection "px" "nid" in
    (if: (~ "ok")
    then
      Paxos__Connect "px" "nid";;
      #()
    else
      let: "err" := grove_ffi.Send "conn" "data" in
      (if: "err"
      then
        Paxos__Connect "px" "nid";;
        #()
      else #())).

Definition Paxos__LeaderSession: val :=
  rec: "Paxos__LeaderSession" "px" :=
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      Mutex__Lock (struct.loadF Paxos "mu" "px");;
      Cond__Wait (struct.loadF Paxos "cv" "px");;
      (if: (~ (Paxos__leading "px"))
      then
        Mutex__Unlock (struct.loadF Paxos "mu" "px");;
        Continue
      else
        ForSlice uint64T <> "nidloop" (struct.loadF Paxos "peers" "px")
          (let: "nid" := "nidloop" in
          let: ("lsne", "ents") := Paxos__obtain "px" "nid" in
          let: "termc" := Paxos__gettermc "px" in
          let: "lsnc" := Paxos__getlsnc "px" in
          Fork (let: "data" := EncodeAcceptRequest "termc" "lsnc" "lsne" "ents" in
                Paxos__Send "px" "nid" "data"));;
        Mutex__Unlock (struct.loadF Paxos "mu" "px");;
        Continue));;
    #().

Definition Paxos__HeartbeatSession: val :=
  rec: "Paxos__HeartbeatSession" "px" :=
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      time.Sleep params.NS_HEARTBEAT_INTERVAL;;
      Cond__Broadcast (struct.loadF Paxos "cv" "px");;
      Continue);;
    #().

Definition EncodePrepareRequest: val :=
  rec: "EncodePrepareRequest" "term" "lsnc" :=
    let: "bs" := NewSliceWithCap byteT #0 #24 in
    let: "bs1" := marshal.WriteInt "bs" MSG_PREPARE in
    let: "bs2" := marshal.WriteInt "bs1" "term" in
    let: "data" := marshal.WriteInt "bs2" "lsnc" in
    "data".

Definition Paxos__ElectionSession: val :=
  rec: "Paxos__ElectionSession" "px" :=
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      let: "delta" := (rand.RandomUint64 #()) `rem` params.NS_ELECTION_TIMEOUT_DELTA in
      time.Sleep (params.NS_ELECTION_TIMEOUT_BASE + "delta");;
      Mutex__Lock (struct.loadF Paxos "mu" "px");;
      (if: Paxos__leading "px"
      then
        Mutex__Unlock (struct.loadF Paxos "mu" "px");;
        Continue
      else
        (if: Paxos__heartbeated "px"
        then
          Paxos__resethb "px";;
          Mutex__Unlock (struct.loadF Paxos "mu" "px");;
          Continue
        else
          let: "termc" := ref (zero_val uint64T) in
          let: "lsnc" := ref (zero_val uint64T) in
          (if: Paxos__nominated "px"
          then
            "termc" <-[uint64T] (Paxos__gettermc "px");;
            "lsnc" <-[uint64T] (Paxos__getlsnc "px")
          else
            let: ("0_ret", "1_ret") := Paxos__nominate "px" in
            "termc" <-[uint64T] "0_ret";;
            "lsnc" <-[uint64T] "1_ret");;
          Mutex__Unlock (struct.loadF Paxos "mu" "px");;
          ForSlice uint64T <> "nidloop" (struct.loadF Paxos "peers" "px")
            (let: "nid" := "nidloop" in
            Fork (let: "data" := EncodePrepareRequest (![uint64T] "termc") (![uint64T] "lsnc") in
                  Paxos__Send "px" "nid" "data"));;
          Continue)));;
    #().

Definition Paxos__Receive: val :=
  rec: "Paxos__Receive" "px" "nid" :=
    let: ("conn", "ok") := Paxos__GetConnection "px" "nid" in
    (if: (~ "ok")
    then
      Paxos__Connect "px" "nid";;
      (slice.nil, #false)
    else
      let: "ret" := grove_ffi.Receive "conn" in
      (if: struct.get grove_ffi.ReceiveRet "Err" "ret"
      then
        Paxos__Connect "px" "nid";;
        (slice.nil, #false)
      else (struct.get grove_ffi.ReceiveRet "Data" "ret", #true))).

(* [REQUEST-VOTE, NodeID, Term, EntriesTerm, Entries]
   [APPEND-ENTRIES, NodeID, Term, MatchedLSN] *)
Definition PaxosResponse := struct.decl [
  "Kind" :: uint64T;
  "NodeID" :: uint64T;
  "Term" :: uint64T;
  "EntriesTerm" :: uint64T;
  "Entries" :: slice.T stringT;
  "MatchedLSN" :: uint64T
].

Definition DecodePrepareResponse: val :=
  rec: "DecodePrepareResponse" "bs" :=
    let: ("nid", "bs1") := marshal.ReadInt "bs" in
    let: ("term", "bs2") := marshal.ReadInt "bs1" in
    let: ("terma", "bs3") := marshal.ReadInt "bs2" in
    let: ("ents", <>) := util.DecodeStrings "bs3" in
    struct.mk PaxosResponse [
      "Kind" ::= MSG_PREPARE;
      "NodeID" ::= "nid";
      "Term" ::= "term";
      "EntriesTerm" ::= "terma";
      "Entries" ::= "ents"
    ].

Definition DecodeAcceptResponse: val :=
  rec: "DecodeAcceptResponse" "bs" :=
    let: ("nid", "bs1") := marshal.ReadInt "bs" in
    let: ("term", "bs2") := marshal.ReadInt "bs1" in
    let: ("lsn", <>) := marshal.ReadInt "bs2" in
    struct.mk PaxosResponse [
      "Kind" ::= MSG_ACCEPT;
      "NodeID" ::= "nid";
      "Term" ::= "term";
      "MatchedLSN" ::= "lsn"
    ].

Definition DecodeResponse: val :=
  rec: "DecodeResponse" "bs" :=
    let: ("kind", "data") := marshal.ReadInt "bs" in
    (if: "kind" = MSG_PREPARE
    then
      let: "resp" := DecodePrepareResponse "data" in
      "resp"
    else
      (if: "kind" = MSG_ACCEPT
      then
        let: "resp" := DecodeAcceptResponse "data" in
        "resp"
      else
        struct.mk PaxosResponse [
        ])).

Definition Paxos__ResponseSession: val :=
  rec: "Paxos__ResponseSession" "px" "nid" :=
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      let: ("data", "ok") := Paxos__Receive "px" "nid" in
      (if: (~ "ok")
      then
        time.Sleep params.NS_RECONNECT;;
        Continue
      else
        let: "resp" := DecodeResponse "data" in
        let: "kind" := struct.get PaxosResponse "Kind" "resp" in
        Mutex__Lock (struct.loadF Paxos "mu" "px");;
        (if: Paxos__lttermc "px" (struct.get PaxosResponse "Term" "resp")
        then
          Mutex__Unlock (struct.loadF Paxos "mu" "px");;
          Continue
        else
          (if: Paxos__gttermc "px" (struct.get PaxosResponse "Term" "resp")
          then
            Paxos__stepdown "px" (struct.get PaxosResponse "Term" "resp");;
            Mutex__Unlock (struct.loadF Paxos "mu" "px");;
            Continue
          else
            (if: "kind" = MSG_PREPARE
            then
              (if: (~ (Paxos__nominated "px"))
              then
                Mutex__Unlock (struct.loadF Paxos "mu" "px");;
                Continue
              else
                Paxos__collect "px" (struct.get PaxosResponse "NodeID" "resp") (struct.get PaxosResponse "EntriesTerm" "resp") (struct.get PaxosResponse "Entries" "resp");;
                Paxos__ascend "px";;
                Mutex__Unlock (struct.loadF Paxos "mu" "px");;
                Continue)
            else
              (if: "kind" = MSG_ACCEPT
              then
                (if: (~ (Paxos__leading "px"))
                then
                  Mutex__Unlock (struct.loadF Paxos "mu" "px");;
                  Continue
                else
                  (if: (struct.get PaxosResponse "NodeID" "resp") = (struct.loadF Paxos "nidme" "px")
                  then
                    Mutex__Unlock (struct.loadF Paxos "mu" "px");;
                    Continue
                  else
                    let: "forwarded" := Paxos__forward "px" (struct.get PaxosResponse "NodeID" "resp") (struct.get PaxosResponse "MatchedLSN" "resp") in
                    (if: (~ "forwarded")
                    then
                      Mutex__Unlock (struct.loadF Paxos "mu" "px");;
                      Continue
                    else
                      let: ("lsnc", "pushed") := Paxos__push "px" in
                      (if: (~ "pushed")
                      then
                        Mutex__Unlock (struct.loadF Paxos "mu" "px");;
                        Continue
                      else
                        Paxos__commit "px" "lsnc";;
                        Mutex__Unlock (struct.loadF Paxos "mu" "px");;
                        Continue))))
              else Continue))))));;
    #().

(* [REQUEST-VOTE, Term, CommittedLSN]
   [APPEND-ENTRIES, Term, CommittedLSN, LSNEntries, Entries] *)
Definition PaxosRequest := struct.decl [
  "Kind" :: uint64T;
  "Term" :: uint64T;
  "CommittedLSN" :: uint64T;
  "EntriesLSN" :: uint64T;
  "Entries" :: slice.T stringT
].

Definition DecodePrepareRequest: val :=
  rec: "DecodePrepareRequest" "bs" :=
    let: ("term", "bs1") := marshal.ReadInt "bs" in
    let: ("lsnc", <>) := marshal.ReadInt "bs1" in
    struct.mk PaxosRequest [
      "Kind" ::= MSG_PREPARE;
      "Term" ::= "term";
      "CommittedLSN" ::= "lsnc"
    ].

Definition DecodeAcceptRequest: val :=
  rec: "DecodeAcceptRequest" "bs" :=
    let: ("term", "bs1") := marshal.ReadInt "bs" in
    let: ("lsnc", "bs2") := marshal.ReadInt "bs1" in
    let: ("lsne", "bs3") := marshal.ReadInt "bs2" in
    let: ("ents", <>) := util.DecodeStrings "bs3" in
    struct.mk PaxosRequest [
      "Kind" ::= MSG_ACCEPT;
      "Term" ::= "term";
      "CommittedLSN" ::= "lsnc";
      "EntriesLSN" ::= "lsne";
      "Entries" ::= "ents"
    ].

Definition DecodeRequest: val :=
  rec: "DecodeRequest" "bs" :=
    let: ("kind", "data") := marshal.ReadInt "bs" in
    (if: "kind" = MSG_PREPARE
    then
      let: "req" := DecodePrepareRequest "data" in
      "req"
    else
      (if: "kind" = MSG_ACCEPT
      then
        let: "req" := DecodeAcceptRequest "data" in
        "req"
      else
        struct.mk PaxosRequest [
        ])).

Definition EncodePrepareResponse: val :=
  rec: "EncodePrepareResponse" "nid" "term" "terma" "ents" :=
    let: "bs" := NewSliceWithCap byteT #0 #64 in
    let: "bs1" := marshal.WriteInt "bs" MSG_PREPARE in
    let: "bs2" := marshal.WriteInt "bs1" "nid" in
    let: "bs3" := marshal.WriteInt "bs2" "term" in
    let: "bs4" := marshal.WriteInt "bs3" "terma" in
    let: "data" := util.EncodeStrings "bs4" "ents" in
    "data".

Definition EncodeAcceptResponse: val :=
  rec: "EncodeAcceptResponse" "nid" "term" "lsn" :=
    let: "bs" := NewSliceWithCap byteT #0 #32 in
    let: "bs1" := marshal.WriteInt "bs" MSG_ACCEPT in
    let: "bs2" := marshal.WriteInt "bs1" "nid" in
    let: "bs3" := marshal.WriteInt "bs2" "term" in
    let: "data" := marshal.WriteInt "bs3" "lsn" in
    "data".

Definition Paxos__RequestSession: val :=
  rec: "Paxos__RequestSession" "px" "conn" :=
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      let: "ret" := grove_ffi.Receive "conn" in
      (if: struct.get grove_ffi.ReceiveRet "Err" "ret"
      then Break
      else
        let: "req" := DecodeRequest (struct.get grove_ffi.ReceiveRet "Data" "ret") in
        let: "kind" := struct.get PaxosRequest "Kind" "req" in
        Mutex__Lock (struct.loadF Paxos "mu" "px");;
        (if: Paxos__lttermc "px" (struct.get PaxosRequest "Term" "req")
        then
          Mutex__Unlock (struct.loadF Paxos "mu" "px");;
          Continue
        else
          Paxos__stepdown "px" (struct.get PaxosRequest "Term" "req");;
          Paxos__heartbeat "px";;
          let: "termc" := Paxos__gettermc "px" in
          (if: "kind" = MSG_PREPARE
          then
            (if: Paxos__latest "px"
            then
              Mutex__Unlock (struct.loadF Paxos "mu" "px");;
              Continue
            else
              let: ("terml", "ents") := Paxos__prepare "px" (struct.get PaxosRequest "CommittedLSN" "req") in
              Mutex__Unlock (struct.loadF Paxos "mu" "px");;
              let: "data" := EncodePrepareResponse (struct.loadF Paxos "nidme" "px") "termc" "terml" "ents" in
              grove_ffi.Send "conn" "data";;
              Continue)
          else
            (if: "kind" = MSG_ACCEPT
            then
              let: "lsn" := Paxos__accept "px" (struct.get PaxosRequest "EntriesLSN" "req") (struct.get PaxosRequest "Term" "req") (struct.get PaxosRequest "Entries" "req") in
              Paxos__learn "px" (struct.get PaxosRequest "CommittedLSN" "req") (struct.get PaxosRequest "Term" "req");;
              Mutex__Unlock (struct.loadF Paxos "mu" "px");;
              let: "data" := EncodeAcceptResponse (struct.loadF Paxos "nidme" "px") "termc" "lsn" in
              grove_ffi.Send "conn" "data";;
              Continue
            else Continue)))));;
    #().

Definition Paxos__Serve: val :=
  rec: "Paxos__Serve" "px" :=
    let: "addrme" := Fst (MapGet (struct.loadF Paxos "addrm" "px") (struct.loadF Paxos "nidme" "px")) in
    let: "ls" := grove_ffi.Listen "addrme" in
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      let: "conn" := grove_ffi.Accept "ls" in
      Fork (Paxos__RequestSession "px" "conn");;
      Continue);;
    #().

Definition Paxos__ConnectAll: val :=
  rec: "Paxos__ConnectAll" "px" :=
    ForSlice uint64T <> "nid" (struct.loadF Paxos "peers" "px")
      (Paxos__Connect "px" "nid");;
    #().

Definition Paxos__DumpState: val :=
  rec: "Paxos__DumpState" "px" :=
    Mutex__Lock (struct.loadF Paxos "mu" "px");;
    (* fmt.Printf("Current term: %d\n", px.termc) *)
    (* fmt.Printf("Ledger term: %d\n", px.terml) *)
    (* fmt.Printf("Number of log entries: %d\n", uint64(len(px.log))) *)
    (* fmt.Printf("Committed LSN: %d\n", px.lsnc) *)
    (* fmt.Printf("Is candidate / leader: %t / %t\n", px.iscand, px.isleader) *)
    (if: struct.loadF Paxos "iscand" "px"
    then
      (* fmt.Printf("Candidate state:\n") *)
      (* fmt.Printf("Largest term seen in prepare: %d\n", px.termp) *)
      (* fmt.Printf("Longest log after committed LSN in prepare: %d\n", px.termp) *)
      (* fmt.Printf("Number of votes granted: %d\n", uint64(len(px.respp))) *)
      #()
    else #());;
    (if: struct.loadF Paxos "isleader" "px"
    then
      (* fmt.Printf("Leader state:\n") *)
      (* fmt.Printf("Match LSN for each peer:\n") *)
      MapIter (struct.loadF Paxos "lsnpeers" "px") (λ: "nid" "lsnpeer",
        (* fmt.Printf("Peer %d -> %d\n", nid, lsnpeer) *)
        #())
    else #());;
    Mutex__Unlock (struct.loadF Paxos "mu" "px");;
    #().

Definition Paxos__ForceElection: val :=
  rec: "Paxos__ForceElection" "px" :=
    Mutex__Lock (struct.loadF Paxos "mu" "px");;
    let: ("termc", "lsnc") := Paxos__nominate "px" in
    Mutex__Unlock (struct.loadF Paxos "mu" "px");;
    ForSlice uint64T <> "nidloop" (struct.loadF Paxos "peers" "px")
      (let: "nid" := "nidloop" in
      Fork (let: "data" := EncodePrepareRequest "termc" "lsnc" in
            Paxos__Send "px" "nid" "data"));;
    #().

Definition mkPaxos: val :=
  rec: "mkPaxos" "nidme" "termc" "terml" "lsnc" "log" "addrm" "fname" :=
    let: "sc" := MapLen "addrm" in
    let: "peers" := ref_to (slice.T uint64T) (NewSliceWithCap uint64T #0 ("sc" - #1)) in
    MapIter "addrm" (λ: "nid" <>,
      (if: "nid" ≠ "nidme"
      then "peers" <-[slice.T uint64T] (SliceAppend uint64T (![slice.T uint64T] "peers") "nid")
      else #()));;
    let: "mu" := newMutex #() in
    let: "cv" := NewCond "mu" in
    let: "px" := struct.new Paxos [
      "nidme" ::= "nidme";
      "peers" ::= ![slice.T uint64T] "peers";
      "addrm" ::= "addrm";
      "sc" ::= "sc";
      "fname" ::= "fname";
      "mu" ::= "mu";
      "cv" ::= "cv";
      "hb" ::= #false;
      "termc" ::= "termc";
      "terml" ::= "terml";
      "log" ::= "log";
      "lsnc" ::= "lsnc";
      "iscand" ::= #false;
      "isleader" ::= #false;
      "conns" ::= NewMap uint64T grove_ffi.Connection #()
    ] in
    "px".

(* Read the underlying file and perform recovery to re-construct @termc, @terml,
   @lsnc, and @log. *)
Definition resume: val :=
  rec: "resume" "fname" :=
    let: "termc" := ref (zero_val uint64T) in
    let: "terml" := ref (zero_val uint64T) in
    let: "lsnc" := ref (zero_val uint64T) in
    let: "log" := ref_to (slice.T stringT) (NewSlice stringT #0) in
    let: "data" := ref_to (slice.T byteT) (grove_ffi.FileRead "fname") in
    Skip;;
    (for: (λ: <>, #0 < (slice.len (![slice.T byteT] "data"))); (λ: <>, Skip) := λ: <>,
      let: ("kind", "bs") := marshal.ReadInt (![slice.T byteT] "data") in
      (if: "kind" = CMD_EXTEND
      then
        let: ("ents", "bs1") := util.DecodeStrings "bs" in
        "data" <-[slice.T byteT] "bs1";;
        "log" <-[slice.T stringT] (SliceAppendSlice stringT (![slice.T stringT] "log") "ents");;
        Continue
      else
        (if: "kind" = CMD_APPEND
        then
          let: ("ent", "bs1") := util.DecodeString "bs" in
          "data" <-[slice.T byteT] "bs1";;
          "log" <-[slice.T stringT] (SliceAppend stringT (![slice.T stringT] "log") "ent");;
          Continue
        else
          (if: "kind" = CMD_PREPARE
          then
            let: ("term", "bs1") := marshal.ReadInt "bs" in
            "data" <-[slice.T byteT] "bs1";;
            "termc" <-[uint64T] "term";;
            Continue
          else
            (if: "kind" = CMD_ADVANCE
            then
              let: ("term", "bs1") := marshal.ReadInt "bs" in
              let: ("lsn", "bs2") := marshal.ReadInt "bs1" in
              let: ("ents", "bs3") := util.DecodeStrings "bs2" in
              "data" <-[slice.T byteT] "bs3";;
              "terml" <-[uint64T] "term";;
              "log" <-[slice.T stringT] (SliceTake (![slice.T stringT] "log") "lsn");;
              "log" <-[slice.T stringT] (SliceAppendSlice stringT (![slice.T stringT] "log") "ents");;
              Continue
            else
              (if: "kind" = CMD_ACCEPT
              then
                let: ("lsn", "bs1") := marshal.ReadInt "bs" in
                let: ("ents", "bs2") := util.DecodeStrings "bs1" in
                "data" <-[slice.T byteT] "bs2";;
                "log" <-[slice.T stringT] (SliceTake (![slice.T stringT] "log") "lsn");;
                "log" <-[slice.T stringT] (SliceAppendSlice stringT (![slice.T stringT] "log") "ents");;
                Continue
              else
                (if: "kind" = CMD_EXPAND
                then
                  let: ("lsn", "bs1") := marshal.ReadInt "bs" in
                  "data" <-[slice.T byteT] "bs1";;
                  "lsnc" <-[uint64T] "lsn";;
                  Continue
                else Continue)))))));;
    (![uint64T] "termc", ![uint64T] "terml", ![uint64T] "lsnc", ![slice.T stringT] "log").

Definition Start: val :=
  rec: "Start" "nidme" "addrm" "fname" :=
    control.impl.Assume (#1 < (MapLen "addrm"));;
    let: (<>, "ok") := MapGet "addrm" "nidme" in
    control.impl.Assume "ok";;
    control.impl.Assume ("nidme" < MAX_NODES);;
    let: ((("termc", "terml"), "lsnc"), "log") := resume "fname" in
    let: "px" := mkPaxos "nidme" "termc" "terml" "lsnc" "log" "addrm" "fname" in
    Fork (Paxos__Serve "px");;
    Fork (Paxos__LeaderSession "px");;
    Fork (Paxos__HeartbeatSession "px");;
    Fork (Paxos__ElectionSession "px");;
    ForSlice uint64T <> "nidloop" (struct.loadF Paxos "peers" "px")
      (let: "nid" := "nidloop" in
      Fork (Paxos__ResponseSession "px" "nid"));;
    "px".

Definition logExtend: val :=
  rec: "logExtend" "fname" "ents" :=
    let: "bs" := NewSliceWithCap byteT #0 #64 in
    let: "bs1" := marshal.WriteInt "bs" CMD_EXTEND in
    let: "bs2" := util.EncodeStrings "bs1" "ents" in
    grove_ffi.FileAppend "fname" "bs2";;
    #().
