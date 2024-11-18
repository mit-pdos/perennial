(* autogenerated from github.com/mit-pdos/tulip/gcoord *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_com.mit_pdos.tulip.message.
From Goose Require github_com.mit_pdos.tulip.params.
From Goose Require github_com.mit_pdos.tulip.quorum.
From Goose Require github_com.mit_pdos.tulip.tulip.

From Perennial.goose_lang Require Import ffi.grove_prelude.

(* /
   / Group coordinator.
   /
   / Interface:
   / Read(ts, key) Value
   / Prepare(ts, ptgs, pwrs)
   / Commit(ts, pwrs)
   / Abort(ts)
   / ResultSession(rid uint64) *)
Definition GroupCoordinator := struct.decl [
  "rps" :: mapT uint64T;
  "mu" :: ptrT;
  "cv" :: ptrT;
  "ts" :: uint64T;
  "leader" :: uint64T;
  "grd" :: ptrT;
  "gpp" :: ptrT;
  "tsfinals" :: mapT boolT;
  "conns" :: mapT grove_ffi.Connection
].

(* /
   / Group reader. Used internally by group coordinator.
   / *)
Definition GroupReader := struct.decl [
  "nrps" :: uint64T;
  "rds" :: mapT (struct.t tulip.Value);
  "versm" :: mapT (mapT (struct.t tulip.Version))
].

Definition GroupReader__ready: val :=
  rec: "GroupReader__ready" "grd" "rid" "key" :=
    let: (<>, "final") := MapGet (struct.loadF GroupReader "rds" "grd") "key" in
    (if: "final"
    then #true
    else
      let: "vers" := Fst (MapGet (struct.loadF GroupReader "versm" "grd") "key") in
      let: (<>, "responded") := MapGet "vers" "rid" in
      (if: "responded"
      then #true
      else #false)).

Definition GroupCoordinator__ValueReady: val :=
  rec: "GroupCoordinator__ValueReady" "gcoord" "rid" "key" :=
    Mutex__Lock (struct.loadF GroupCoordinator "mu" "gcoord");;
    let: "done" := GroupReader__ready (struct.loadF GroupCoordinator "grd" "gcoord") "rid" "key" in
    Mutex__Unlock (struct.loadF GroupCoordinator "mu" "gcoord");;
    "done".

Definition GroupCoordinator__GetConnection: val :=
  rec: "GroupCoordinator__GetConnection" "gcoord" "rid" :=
    Mutex__Lock (struct.loadF GroupCoordinator "mu" "gcoord");;
    let: ("conn", "ok") := MapGet (struct.loadF GroupCoordinator "conns" "gcoord") "rid" in
    Mutex__Unlock (struct.loadF GroupCoordinator "mu" "gcoord");;
    ("conn", "ok").

Definition GroupCoordinator__Connect: val :=
  rec: "GroupCoordinator__Connect" "gcoord" "rid" :=
    let: "addr" := Fst (MapGet (struct.loadF GroupCoordinator "rps" "gcoord") "rid") in
    let: "ret" := grove_ffi.Connect "addr" in
    (if: (~ (struct.get grove_ffi.ConnectRet "Err" "ret"))
    then
      Mutex__Lock (struct.loadF GroupCoordinator "mu" "gcoord");;
      MapInsert (struct.loadF GroupCoordinator "conns" "gcoord") "rid" (struct.get grove_ffi.ConnectRet "Connection" "ret");;
      Mutex__Unlock (struct.loadF GroupCoordinator "mu" "gcoord");;
      #true
    else #false).

Definition GroupCoordinator__Send: val :=
  rec: "GroupCoordinator__Send" "gcoord" "rid" "data" :=
    let: ("conn", "ok") := GroupCoordinator__GetConnection "gcoord" "rid" in
    (if: (~ "ok")
    then GroupCoordinator__Connect "gcoord" "rid"
    else #());;
    let: "err" := grove_ffi.Send "conn" "data" in
    (if: "err"
    then
      GroupCoordinator__Connect "gcoord" "rid";;
      #()
    else #()).

Definition GroupCoordinator__SendRead: val :=
  rec: "GroupCoordinator__SendRead" "gcoord" "rid" "ts" "key" :=
    GroupCoordinator__Send "gcoord" "rid" (message.EncodeTxnRead "ts" "key");;
    #().

Definition GroupCoordinator__ReadSession: val :=
  rec: "GroupCoordinator__ReadSession" "gcoord" "rid" "ts" "key" :=
    Skip;;
    (for: (λ: <>, (~ (GroupCoordinator__ValueReady "gcoord" "rid" "key"))); (λ: <>, Skip) := λ: <>,
      GroupCoordinator__SendRead "gcoord" "rid" "ts" "key";;
      time.Sleep params.NS_RESEND_READ;;
      Continue);;
    #().

Definition GroupReader__read: val :=
  rec: "GroupReader__read" "grd" "key" :=
    let: ("v", "ok") := MapGet (struct.loadF GroupReader "rds" "grd") "key" in
    ("v", "ok").

Definition GroupCoordinator__WaitUntilValueReady: val :=
  rec: "GroupCoordinator__WaitUntilValueReady" "gcoord" "key" :=
    Mutex__Lock (struct.loadF GroupCoordinator "mu" "gcoord");;
    let: "value" := ref (zero_val (struct.t tulip.Value)) in
    let: "ok" := ref (zero_val boolT) in
    let: ("0_ret", "1_ret") := GroupReader__read (struct.loadF GroupCoordinator "grd" "gcoord") "key" in
    "value" <-[struct.t tulip.Value] "0_ret";;
    "ok" <-[boolT] "1_ret";;
    Skip;;
    (for: (λ: <>, (~ (![boolT] "ok"))); (λ: <>, Skip) := λ: <>,
      Cond__Wait (struct.loadF GroupCoordinator "cv" "gcoord");;
      let: ("0_ret", "1_ret") := GroupReader__read (struct.loadF GroupCoordinator "grd" "gcoord") "key" in
      "value" <-[struct.t tulip.Value] "0_ret";;
      "ok" <-[boolT] "1_ret";;
      Continue);;
    Mutex__Unlock (struct.loadF GroupCoordinator "mu" "gcoord");;
    ![struct.t tulip.Value] "value".

(* Arguments:
   @ts: Timestamp of the transaction performing this read.
   @key: Key to be read.

   Return value:
   @value: Value of @key.

   @gcoord.Read blocks until the value of @key is determined. *)
Definition GroupCoordinator__Read: val :=
  rec: "GroupCoordinator__Read" "gcoord" "ts" "key" :=
    MapIter (struct.loadF GroupCoordinator "rps" "gcoord") (λ: "ridloop" <>,
      let: "rid" := "ridloop" in
      Fork (GroupCoordinator__ReadSession "gcoord" "rid" "ts" "key"));;
    let: "v" := GroupCoordinator__WaitUntilValueReady "gcoord" "key" in
    "v".

(* /
   / Group preparer. Used internally by group coordinator.
   / *)
Definition GroupPreparer := struct.decl [
  "nrps" :: uint64T;
  "phase" :: uint64T;
  "fresps" :: mapT boolT;
  "sresps" :: mapT boolT
].

Definition GPP_VALIDATING : expr := #0.

Definition GPP_PREPARING : expr := #1.

Definition GPP_UNPREPARING : expr := #2.

Definition GPP_WAITING : expr := #3.

Definition GPP_PREPARED : expr := #4.

Definition GPP_COMMITTED : expr := #5.

Definition GPP_ABORTED : expr := #6.

Definition GPP_FAST_PREPARE : expr := #0.

Definition GPP_VALIDATE : expr := #1.

Definition GPP_PREPARE : expr := #2.

Definition GPP_UNPREPARE : expr := #3.

Definition GPP_QUERY : expr := #4.

Definition GPP_REFRESH : expr := #5.

(* Argument:
   @rid: ID of the replica to which a new action is performed.

   Return value:
   @action: Next action to perform. *)
Definition GroupPreparer__action: val :=
  rec: "GroupPreparer__action" "gpp" "rid" :=
    (if: (struct.loadF GroupPreparer "phase" "gpp") = GPP_VALIDATING
    then
      let: (<>, "fresp") := MapGet (struct.loadF GroupPreparer "fresps" "gpp") "rid" in
      (if: (~ "fresp")
      then GPP_FAST_PREPARE
      else
        let: (<>, "validated") := MapGet (struct.loadF GroupPreparer "sresps" "gpp") "rid" in
        (if: (~ "validated")
        then GPP_VALIDATE
        else GPP_QUERY))
    else
      (if: (struct.loadF GroupPreparer "phase" "gpp") = GPP_PREPARING
      then
        let: (<>, "prepared") := MapGet (struct.loadF GroupPreparer "sresps" "gpp") "rid" in
        (if: (~ "prepared")
        then GPP_PREPARE
        else GPP_QUERY)
      else
        (if: (struct.loadF GroupPreparer "phase" "gpp") = GPP_UNPREPARING
        then
          let: (<>, "unprepared") := MapGet (struct.loadF GroupPreparer "sresps" "gpp") "rid" in
          (if: (~ "unprepared")
          then GPP_UNPREPARE
          else GPP_QUERY)
        else
          (if: (struct.loadF GroupPreparer "phase" "gpp") = GPP_WAITING
          then GPP_QUERY
          else GPP_REFRESH)))).

Definition GroupCoordinator__NextPrepareAction: val :=
  rec: "GroupCoordinator__NextPrepareAction" "gcoord" "rid" :=
    Mutex__Lock (struct.loadF GroupCoordinator "mu" "gcoord");;
    let: "a" := GroupPreparer__action (struct.loadF GroupCoordinator "gpp" "gcoord") "rid" in
    Mutex__Unlock (struct.loadF GroupCoordinator "mu" "gcoord");;
    "a".

Definition GroupCoordinator__AttachedWith: val :=
  rec: "GroupCoordinator__AttachedWith" "gcoord" "ts" :=
    Mutex__Lock (struct.loadF GroupCoordinator "mu" "gcoord");;
    let: "b" := (struct.loadF GroupCoordinator "ts" "gcoord") = "ts" in
    Mutex__Unlock (struct.loadF GroupCoordinator "mu" "gcoord");;
    "b".

Definition GroupCoordinator__SendFastPrepare: val :=
  rec: "GroupCoordinator__SendFastPrepare" "gcoord" "rid" "ts" "pwrs" "ptgs" :=
    GroupCoordinator__Send "gcoord" "rid" (message.EncodeTxnFastPrepare "ts" "pwrs" "ptgs");;
    #().

Definition GroupCoordinator__SendValidate: val :=
  rec: "GroupCoordinator__SendValidate" "gcoord" "rid" "ts" "rank" "pwrs" "ptgs" :=
    #().

Definition GroupCoordinator__SendPrepare: val :=
  rec: "GroupCoordinator__SendPrepare" "gcoord" "rid" "ts" "rank" :=
    #().

Definition GroupCoordinator__SendUnprepare: val :=
  rec: "GroupCoordinator__SendUnprepare" "gcoord" "rid" "ts" "rank" :=
    #().

Definition GroupCoordinator__SendQuery: val :=
  rec: "GroupCoordinator__SendQuery" "gcoord" "rid" "ts" "rank" :=
    #().

Definition GroupCoordinator__SendRefresh: val :=
  rec: "GroupCoordinator__SendRefresh" "gcoord" "rid" "ts" "rank" :=
    #().

Definition GroupCoordinator__PrepareSession: val :=
  rec: "GroupCoordinator__PrepareSession" "gcoord" "rid" "ts" "ptgs" "pwrs" :=
    let: "act" := ref_to uint64T (GroupCoordinator__NextPrepareAction "gcoord" "rid") in
    Skip;;
    (for: (λ: <>, GroupCoordinator__AttachedWith "gcoord" "ts"); (λ: <>, Skip) := λ: <>,
      (if: (![uint64T] "act") = GPP_FAST_PREPARE
      then GroupCoordinator__SendFastPrepare "gcoord" "rid" "ts" "pwrs" "ptgs"
      else
        (if: (![uint64T] "act") = GPP_VALIDATE
        then GroupCoordinator__SendValidate "gcoord" "rid" "ts" #1 "pwrs" "ptgs"
        else
          (if: (![uint64T] "act") = GPP_PREPARE
          then GroupCoordinator__SendPrepare "gcoord" "rid" "ts" #1
          else
            (if: (![uint64T] "act") = GPP_UNPREPARE
            then GroupCoordinator__SendUnprepare "gcoord" "rid" "ts" #1
            else
              (if: (![uint64T] "act") = GPP_QUERY
              then GroupCoordinator__SendQuery "gcoord" "rid" "ts" #1
              else
                (if: (![uint64T] "act") = GPP_REFRESH
                then GroupCoordinator__SendRefresh "gcoord" "rid" "ts" #1
                else #()))))));;
      (if: (![uint64T] "act") = GPP_REFRESH
      then time.Sleep params.NS_SEND_REFRESH
      else time.Sleep params.NS_RESEND_PREPARE);;
      "act" <-[uint64T] (GroupCoordinator__NextPrepareAction "gcoord" "rid");;
      Continue);;
    #().

Definition GroupPreparer__ready: val :=
  rec: "GroupPreparer__ready" "gpp" :=
    GPP_PREPARED ≤ (struct.loadF GroupPreparer "phase" "gpp").

Definition GroupPreparer__getPhase: val :=
  rec: "GroupPreparer__getPhase" "gpp" :=
    struct.loadF GroupPreparer "phase" "gpp".

Definition GroupCoordinator__WaitUntilPrepareDone: val :=
  rec: "GroupCoordinator__WaitUntilPrepareDone" "gcoord" "ts" :=
    Mutex__Lock (struct.loadF GroupCoordinator "mu" "gcoord");;
    (if: (struct.loadF GroupCoordinator "ts" "gcoord") ≠ "ts"
    then
      Mutex__Unlock (struct.loadF GroupCoordinator "mu" "gcoord");;
      (tulip.TXN_PREPARED, #false)
    else
      Skip;;
      (for: (λ: <>, (~ (GroupPreparer__ready (struct.loadF GroupCoordinator "gpp" "gcoord")))); (λ: <>, Skip) := λ: <>,
        Cond__Wait (struct.loadF GroupCoordinator "cv" "gcoord");;
        Continue);;
      let: "phase" := GroupPreparer__getPhase (struct.loadF GroupCoordinator "gpp" "gcoord") in
      Mutex__Unlock (struct.loadF GroupCoordinator "mu" "gcoord");;
      (if: "phase" = GPP_COMMITTED
      then (tulip.TXN_COMMITTED, #true)
      else
        (if: "phase" = GPP_ABORTED
        then (tulip.TXN_ABORTED, #true)
        else (tulip.TXN_PREPARED, #true)))).

(* Arguments:
   @ts: Transaction timestamp.

   Return values:
   @status: Transaction status.
   @valid: If true, the group coordinator is assigned the same timestamp @ts
   throughout the course of @Prepare. @status is meaningful iff @valid is true.

   @Prepare blocks until the prepare decision (one of prepared, committed,
   aborted) is made, or the associated timestamp has changed. *)
Definition GroupCoordinator__Prepare: val :=
  rec: "GroupCoordinator__Prepare" "gcoord" "ts" "ptgs" "pwrs" :=
    MapIter (struct.loadF GroupCoordinator "rps" "gcoord") (λ: "ridloop" <>,
      let: "rid" := "ridloop" in
      Fork (GroupCoordinator__PrepareSession "gcoord" "rid" "ts" "ptgs" "pwrs"));;
    let: ("st", "valid") := GroupCoordinator__WaitUntilPrepareDone "gcoord" "ts" in
    ("st", "valid").

Definition GroupCoordinator__RegisterFinalization: val :=
  rec: "GroupCoordinator__RegisterFinalization" "gcoord" "ts" :=
    Mutex__Lock (struct.loadF GroupCoordinator "mu" "gcoord");;
    MapInsert (struct.loadF GroupCoordinator "tsfinals" "gcoord") "ts" #true;;
    Mutex__Unlock (struct.loadF GroupCoordinator "mu" "gcoord");;
    #().

Definition GroupCoordinator__GetLeader: val :=
  rec: "GroupCoordinator__GetLeader" "gcoord" :=
    Mutex__Lock (struct.loadF GroupCoordinator "mu" "gcoord");;
    let: "leader" := struct.loadF GroupCoordinator "leader" "gcoord" in
    Mutex__Unlock (struct.loadF GroupCoordinator "mu" "gcoord");;
    "leader".

Definition GroupCoordinator__Finalized: val :=
  rec: "GroupCoordinator__Finalized" "gcoord" "ts" :=
    Mutex__Lock (struct.loadF GroupCoordinator "mu" "gcoord");;
    let: (<>, "ok") := MapGet (struct.loadF GroupCoordinator "tsfinals" "gcoord") "ts" in
    Mutex__Unlock (struct.loadF GroupCoordinator "mu" "gcoord");;
    (~ "ok").

Definition GroupCoordinator__SendCommit: val :=
  rec: "GroupCoordinator__SendCommit" "gcoord" "rid" "ts" "pwrs" :=
    #().

Definition GroupCoordinator__ChangeLeader: val :=
  rec: "GroupCoordinator__ChangeLeader" "gcoord" :=
    Mutex__Lock (struct.loadF GroupCoordinator "mu" "gcoord");;
    let: "leader" := ((struct.loadF GroupCoordinator "leader" "gcoord") + #1) `rem` (MapLen (struct.loadF GroupCoordinator "rps" "gcoord")) in
    struct.storeF GroupCoordinator "leader" "gcoord" "leader";;
    Mutex__Unlock (struct.loadF GroupCoordinator "mu" "gcoord");;
    "leader".

Definition GroupCoordinator__Commit: val :=
  rec: "GroupCoordinator__Commit" "gcoord" "ts" "pwrs" :=
    GroupCoordinator__RegisterFinalization "gcoord" "ts";;
    let: "leader" := ref_to uint64T (GroupCoordinator__GetLeader "gcoord") in
    Skip;;
    (for: (λ: <>, (~ (GroupCoordinator__Finalized "gcoord" "ts"))); (λ: <>, Skip) := λ: <>,
      GroupCoordinator__SendCommit "gcoord" (![uint64T] "leader") "ts" "pwrs";;
      time.Sleep params.NS_RESEND_COMMIT;;
      "leader" <-[uint64T] (GroupCoordinator__ChangeLeader "gcoord");;
      Continue);;
    #().

Definition GroupCoordinator__SendAbort: val :=
  rec: "GroupCoordinator__SendAbort" "gcoord" "rid" "ts" :=
    #().

Definition GroupCoordinator__Abort: val :=
  rec: "GroupCoordinator__Abort" "gcoord" "ts" :=
    GroupCoordinator__RegisterFinalization "gcoord" "ts";;
    let: "leader" := ref_to uint64T (GroupCoordinator__GetLeader "gcoord") in
    Skip;;
    (for: (λ: <>, (~ (GroupCoordinator__Finalized "gcoord" "ts"))); (λ: <>, Skip) := λ: <>,
      GroupCoordinator__SendAbort "gcoord" (![uint64T] "leader") "ts";;
      time.Sleep params.NS_RESEND_ABORT;;
      "leader" <-[uint64T] (GroupCoordinator__ChangeLeader "gcoord");;
      Continue);;
    #().

Definition GroupCoordinator__processFinalizationResult: val :=
  rec: "GroupCoordinator__processFinalizationResult" "gcoord" "ts" "res" :=
    (if: "res" = tulip.REPLICA_WRONG_LEADER
    then #()
    else
      MapDelete (struct.loadF GroupCoordinator "tsfinals" "gcoord") "ts";;
      #()).

Definition GroupCoordinator__Receive: val :=
  rec: "GroupCoordinator__Receive" "gcoord" "rid" :=
    let: ("conn", "ok") := GroupCoordinator__GetConnection "gcoord" "rid" in
    (if: (~ "ok")
    then
      GroupCoordinator__Connect "gcoord" "rid";;
      (slice.nil, #false)
    else
      let: "ret" := grove_ffi.Receive "conn" in
      (if: struct.get grove_ffi.ReceiveRet "Err" "ret"
      then
        GroupCoordinator__Connect "gcoord" "rid";;
        (slice.nil, #false)
      else (struct.get grove_ffi.ReceiveRet "Data" "ret", #true))).

Definition GroupReader__cquorum: val :=
  rec: "GroupReader__cquorum" "grd" "n" :=
    (quorum.ClassicQuorum (struct.loadF GroupReader "nrps" "grd")) ≤ "n".

Definition GroupReader__latestVersion: val :=
  rec: "GroupReader__latestVersion" "grd" "key" :=
    let: "latest" := ref (zero_val (struct.t tulip.Version)) in
    let: "vers" := Fst (MapGet (struct.loadF GroupReader "versm" "grd") "key") in
    MapIter "vers" (λ: <> "ver",
      (if: (struct.get tulip.Version "Timestamp" (![struct.t tulip.Version] "latest")) < (struct.get tulip.Version "Timestamp" "ver")
      then "latest" <-[struct.t tulip.Version] "ver"
      else #()));;
    ![struct.t tulip.Version] "latest".

Definition GroupReader__processReadResult: val :=
  rec: "GroupReader__processReadResult" "grd" "rid" "key" "ver" :=
    let: (<>, "final") := MapGet (struct.loadF GroupReader "rds" "grd") "key" in
    (if: "final"
    then #()
    else
      (if: (struct.get tulip.Version "Timestamp" "ver") = #0
      then
        MapInsert (struct.loadF GroupReader "rds" "grd") "key" (struct.get tulip.Version "Value" "ver");;
        MapDelete (struct.loadF GroupReader "versm" "grd") "key";;
        #()
      else
        let: "vers" := Fst (MapGet (struct.loadF GroupReader "versm" "grd") "key") in
        let: (<>, "responded") := MapGet "vers" "rid" in
        (if: "responded"
        then #()
        else
          MapInsert "vers" "rid" "ver";;
          let: "n" := MapLen "vers" in
          (if: (~ (GroupReader__cquorum "grd" "n"))
          then #()
          else
            let: "latest" := GroupReader__latestVersion "grd" "key" in
            MapInsert (struct.loadF GroupReader "rds" "grd") "key" (struct.get tulip.Version "Value" "latest");;
            MapDelete (struct.loadF GroupReader "versm" "grd") "key";;
            #())))).

Definition GroupPreparer__tryResign: val :=
  rec: "GroupPreparer__tryResign" "gpp" "res" :=
    (if: GroupPreparer__ready "gpp"
    then #true
    else
      (if: "res" = tulip.REPLICA_COMMITTED_TXN
      then
        struct.storeF GroupPreparer "phase" "gpp" GPP_COMMITTED;;
        #true
      else
        (if: "res" = tulip.REPLICA_ABORTED_TXN
        then
          struct.storeF GroupPreparer "phase" "gpp" GPP_ABORTED;;
          #true
        else
          (if: "res" = tulip.REPLICA_STALE_COORDINATOR
          then
            struct.storeF GroupPreparer "phase" "gpp" GPP_WAITING;;
            #true
          else #false)))).

Definition countbm: val :=
  rec: "countbm" "m" "b" :=
    let: "n" := ref_to uint64T #0 in
    MapIter "m" (λ: <> "v",
      (if: "v" = "b"
      then "n" <-[uint64T] ((![uint64T] "n") + #1)
      else #()));;
    ![uint64T] "n".

Definition GroupPreparer__fquorum: val :=
  rec: "GroupPreparer__fquorum" "gpp" "n" :=
    (quorum.FastQuorum (struct.loadF GroupPreparer "nrps" "gpp")) ≤ "n".

Definition GroupPreparer__tryBecomeAborted: val :=
  rec: "GroupPreparer__tryBecomeAborted" "gpp" :=
    let: "n" := countbm (struct.loadF GroupPreparer "fresps" "gpp") #false in
    (if: GroupPreparer__fquorum "gpp" "n"
    then
      struct.storeF GroupPreparer "phase" "gpp" GPP_ABORTED;;
      #true
    else #false).

Definition GroupPreparer__tryBecomePrepared: val :=
  rec: "GroupPreparer__tryBecomePrepared" "gpp" :=
    let: "n" := countbm (struct.loadF GroupPreparer "fresps" "gpp") #true in
    (if: GroupPreparer__fquorum "gpp" "n"
    then
      struct.storeF GroupPreparer "phase" "gpp" GPP_PREPARED;;
      #true
    else #false).

Definition GroupPreparer__cquorum: val :=
  rec: "GroupPreparer__cquorum" "gpp" "n" :=
    (quorum.ClassicQuorum (struct.loadF GroupPreparer "nrps" "gpp")) ≤ "n".

Definition GroupPreparer__tryBecomePreparing: val :=
  rec: "GroupPreparer__tryBecomePreparing" "gpp" :=
    let: "n" := MapLen (struct.loadF GroupPreparer "sresps" "gpp") in
    (if: GroupPreparer__cquorum "gpp" "n"
    then
      struct.storeF GroupPreparer "phase" "gpp" GPP_PREPARING;;
      struct.storeF GroupPreparer "sresps" "gpp" (NewMap uint64T boolT #());;
      #()
    else #()).

Definition GroupPreparer__processFastPrepareResult: val :=
  rec: "GroupPreparer__processFastPrepareResult" "gpp" "rid" "res" :=
    (if: GroupPreparer__tryResign "gpp" "res"
    then #()
    else
      (if: "res" = tulip.REPLICA_FAILED_VALIDATION
      then
        MapInsert (struct.loadF GroupPreparer "fresps" "gpp") "rid" #false;;
        GroupPreparer__tryBecomeAborted "gpp";;
        #()
      else
        MapInsert (struct.loadF GroupPreparer "fresps" "gpp") "rid" #true;;
        (if: GroupPreparer__tryBecomePrepared "gpp"
        then #()
        else
          (if: (struct.loadF GroupPreparer "phase" "gpp") ≠ GPP_VALIDATING
          then #()
          else
            MapInsert (struct.loadF GroupPreparer "sresps" "gpp") "rid" #true;;
            GroupPreparer__tryBecomePreparing "gpp";;
            #())))).

Definition GroupPreparer__processValidateResult: val :=
  rec: "GroupPreparer__processValidateResult" "gpp" "rid" "res" :=
    (if: GroupPreparer__tryResign "gpp" "res"
    then #()
    else
      (if: (struct.loadF GroupPreparer "phase" "gpp") ≠ GPP_VALIDATING
      then #()
      else
        (if: "res" = tulip.REPLICA_FAILED_VALIDATION
        then #()
        else
          MapInsert (struct.loadF GroupPreparer "sresps" "gpp") "rid" #true;;
          GroupPreparer__tryBecomePreparing "gpp";;
          #()))).

Definition GroupPreparer__processPrepareResult: val :=
  rec: "GroupPreparer__processPrepareResult" "gpp" "rid" "res" :=
    (if: GroupPreparer__tryResign "gpp" "res"
    then #()
    else
      MapInsert (struct.loadF GroupPreparer "sresps" "gpp") "rid" #true;;
      let: "n" := MapLen (struct.loadF GroupPreparer "sresps" "gpp") in
      (if: GroupPreparer__cquorum "gpp" "n"
      then
        struct.storeF GroupPreparer "phase" "gpp" GPP_PREPARED;;
        #()
      else #())).

Definition GroupPreparer__processUnprepareResult: val :=
  rec: "GroupPreparer__processUnprepareResult" "gpp" "rid" "res" :=
    (if: GroupPreparer__tryResign "gpp" "res"
    then #()
    else
      MapInsert (struct.loadF GroupPreparer "sresps" "gpp") "rid" #true;;
      let: "n" := MapLen (struct.loadF GroupPreparer "sresps" "gpp") in
      (if: GroupPreparer__cquorum "gpp" "n"
      then
        struct.storeF GroupPreparer "phase" "gpp" GPP_ABORTED;;
        #()
      else #())).

Definition GroupPreparer__processQueryResult: val :=
  rec: "GroupPreparer__processQueryResult" "gpp" "rid" "res" :=
    GroupPreparer__tryResign "gpp" "res";;
    #().

Definition GroupCoordinator__ResultSession: val :=
  rec: "GroupCoordinator__ResultSession" "gcoord" "rid" :=
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      let: ("data", "ok") := GroupCoordinator__Receive "gcoord" "rid" in
      (if: (~ "ok")
      then
        time.Sleep params.NS_RECONNECT;;
        Continue
      else
        let: "msg" := message.DecodeTxnResponse "data" in
        let: "kind" := struct.get message.TxnResponse "Kind" "msg" in
        Mutex__Lock (struct.loadF GroupCoordinator "mu" "gcoord");;
        (if: ("kind" = message.MSG_TXN_COMMIT) || ("kind" = message.MSG_TXN_ABORT)
        then
          GroupCoordinator__processFinalizationResult "gcoord" (struct.get message.TxnResponse "Timestamp" "msg") (struct.get message.TxnResponse "Result" "msg");;
          Mutex__Unlock (struct.loadF GroupCoordinator "mu" "gcoord");;
          Continue
        else
          (if: (struct.loadF GroupCoordinator "ts" "gcoord") ≠ (struct.get message.TxnResponse "Timestamp" "msg")
          then
            Mutex__Unlock (struct.loadF GroupCoordinator "mu" "gcoord");;
            Continue
          else
            let: "gpp" := struct.loadF GroupCoordinator "gpp" "gcoord" in
            let: "grd" := struct.loadF GroupCoordinator "grd" "gcoord" in
            (if: "kind" = message.MSG_TXN_READ
            then GroupReader__processReadResult "grd" "rid" (struct.get message.TxnResponse "Key" "msg") (struct.get message.TxnResponse "Version" "msg")
            else
              (if: "kind" = message.MSG_TXN_FAST_PREPARE
              then GroupPreparer__processFastPrepareResult "gpp" "rid" (struct.get message.TxnResponse "Result" "msg")
              else
                (if: "kind" = message.MSG_TXN_VALIDATE
                then GroupPreparer__processValidateResult "gpp" "rid" (struct.get message.TxnResponse "Result" "msg")
                else
                  (if: "kind" = message.MSG_TXN_PREPARE
                  then GroupPreparer__processPrepareResult "gpp" "rid" (struct.get message.TxnResponse "Result" "msg")
                  else
                    (if: "kind" = message.MSG_TXN_UNPREPARE
                    then GroupPreparer__processUnprepareResult "gpp" "rid" (struct.get message.TxnResponse "Result" "msg")
                    else
                      (if: "kind" = message.MSG_TXN_QUERY
                      then GroupPreparer__processQueryResult "gpp" "rid" (struct.get message.TxnResponse "Result" "msg")
                      else
                        (if: "kind" = message.MSG_TXN_REFRESH
                        then #()
                        else #())))))));;
            Cond__Signal (struct.loadF GroupCoordinator "cv" "gcoord");;
            Mutex__Unlock (struct.loadF GroupCoordinator "mu" "gcoord");;
            Continue))));;
    #().
