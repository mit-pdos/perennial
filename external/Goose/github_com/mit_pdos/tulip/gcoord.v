(* autogenerated from github.com/mit-pdos/tulip/gcoord *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_com.mit_pdos.tulip.message.
From Goose Require github_com.mit_pdos.tulip.params.
From Goose Require github_com.mit_pdos.tulip.quorum.
From Goose Require github_com.mit_pdos.tulip.tulip.
From Goose Require github_com.mit_pdos.tulip.util.

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
  "rps" :: slice.T uint64T;
  "addrm" :: mapT uint64T;
  "mu" :: ptrT;
  "cv" :: ptrT;
  "ts" :: uint64T;
  "idxleader" :: uint64T;
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
  "valuem" :: mapT (struct.t tulip.Value);
  "qreadm" :: mapT (mapT (struct.t tulip.Version))
].

Definition GroupReader__responded: val :=
  rec: "GroupReader__responded" "grd" "rid" "key" :=
    let: (<>, "final") := MapGet (struct.loadF GroupReader "valuem" "grd") "key" in
    (if: "final"
    then #true
    else
      let: ("qread", "ok") := MapGet (struct.loadF GroupReader "qreadm" "grd") "key" in
      (if: (~ "ok")
      then #false
      else
        let: (<>, "responded") := MapGet "qread" "rid" in
        (if: "responded"
        then #true
        else #false))).

Definition GroupCoordinator__ValueResponded: val :=
  rec: "GroupCoordinator__ValueResponded" "gcoord" "rid" "key" :=
    Mutex__Lock (struct.loadF GroupCoordinator "mu" "gcoord");;
    let: "done" := GroupReader__responded (struct.loadF GroupCoordinator "grd" "gcoord") "rid" "key" in
    Mutex__Unlock (struct.loadF GroupCoordinator "mu" "gcoord");;
    "done".

Definition GroupCoordinator__attachedWith: val :=
  rec: "GroupCoordinator__attachedWith" "gcoord" "ts" :=
    (struct.loadF GroupCoordinator "ts" "gcoord") = "ts".

Definition GroupCoordinator__AttachedWith: val :=
  rec: "GroupCoordinator__AttachedWith" "gcoord" "ts" :=
    Mutex__Lock (struct.loadF GroupCoordinator "mu" "gcoord");;
    let: "b" := GroupCoordinator__attachedWith "gcoord" "ts" in
    Mutex__Unlock (struct.loadF GroupCoordinator "mu" "gcoord");;
    "b".

Definition GroupCoordinator__GetConnection: val :=
  rec: "GroupCoordinator__GetConnection" "gcoord" "rid" :=
    Mutex__Lock (struct.loadF GroupCoordinator "mu" "gcoord");;
    let: ("conn", "ok") := MapGet (struct.loadF GroupCoordinator "conns" "gcoord") "rid" in
    Mutex__Unlock (struct.loadF GroupCoordinator "mu" "gcoord");;
    ("conn", "ok").

Definition GroupCoordinator__Connect: val :=
  rec: "GroupCoordinator__Connect" "gcoord" "rid" :=
    let: "addr" := Fst (MapGet (struct.loadF GroupCoordinator "addrm" "gcoord") "rid") in
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
    (for: (λ: <>, (~ (GroupCoordinator__ValueResponded "gcoord" "rid" "key")) && (GroupCoordinator__AttachedWith "gcoord" "ts")); (λ: <>, Skip) := λ: <>,
      GroupCoordinator__SendRead "gcoord" "rid" "ts" "key";;
      time.Sleep params.NS_RESEND_READ;;
      Continue);;
    #().

Definition GroupReader__read: val :=
  rec: "GroupReader__read" "grd" "key" :=
    let: ("v", "ok") := MapGet (struct.loadF GroupReader "valuem" "grd") "key" in
    ("v", "ok").

Definition GroupCoordinator__WaitUntilValueReady: val :=
  rec: "GroupCoordinator__WaitUntilValueReady" "gcoord" "ts" "key" :=
    let: "value" := ref (zero_val (struct.t tulip.Value)) in
    let: "valid" := ref (zero_val boolT) in
    Mutex__Lock (struct.loadF GroupCoordinator "mu" "gcoord");;
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      (if: (~ (GroupCoordinator__attachedWith "gcoord" "ts"))
      then
        "valid" <-[boolT] #false;;
        Break
      else
        let: ("v", "ok") := GroupReader__read (struct.loadF GroupCoordinator "grd" "gcoord") "key" in
        (if: "ok"
        then
          "value" <-[struct.t tulip.Value] "v";;
          "valid" <-[boolT] #true;;
          Break
        else
          Cond__Wait (struct.loadF GroupCoordinator "cv" "gcoord");;
          Continue)));;
    Mutex__Unlock (struct.loadF GroupCoordinator "mu" "gcoord");;
    (![struct.t tulip.Value] "value", ![boolT] "valid").

(* Arguments:
   @ts: Timestamp of the transaction performing this read.
   @key: Key to be read.

   Return value:
   @value: Value of @key.

   @gcoord.Read blocks until the value of @key is determined. *)
Definition GroupCoordinator__Read: val :=
  rec: "GroupCoordinator__Read" "gcoord" "ts" "key" :=
    MapIter (struct.loadF GroupCoordinator "addrm" "gcoord") (λ: "ridloop" <>,
      let: "rid" := "ridloop" in
      Fork (GroupCoordinator__ReadSession "gcoord" "rid" "ts" "key"));;
    let: ("v", "ok") := GroupCoordinator__WaitUntilValueReady "gcoord" "ts" "key" in
    ("v", "ok").

(* /
   / Group preparer. Used internally by group coordinator.
   / *)
Definition GroupPreparer := struct.decl [
  "nrps" :: uint64T;
  "phase" :: uint64T;
  "frespm" :: mapT boolT;
  "vdm" :: mapT boolT;
  "srespm" :: mapT boolT
].

Definition GroupPreparer__in: val :=
  rec: "GroupPreparer__in" "gpp" "phase" :=
    (struct.loadF GroupPreparer "phase" "gpp") = "phase".

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
    (if: GroupPreparer__in "gpp" GPP_VALIDATING
    then
      let: (<>, "fresp") := MapGet (struct.loadF GroupPreparer "frespm" "gpp") "rid" in
      (if: (~ "fresp")
      then GPP_FAST_PREPARE
      else
        let: (<>, "validated") := MapGet (struct.loadF GroupPreparer "vdm" "gpp") "rid" in
        (if: (~ "validated")
        then GPP_VALIDATE
        else GPP_QUERY))
    else
      (if: GroupPreparer__in "gpp" GPP_PREPARING
      then
        let: (<>, "prepared") := MapGet (struct.loadF GroupPreparer "srespm" "gpp") "rid" in
        (if: (~ "prepared")
        then GPP_PREPARE
        else GPP_QUERY)
      else
        (if: GroupPreparer__in "gpp" GPP_UNPREPARING
        then
          let: (<>, "unprepared") := MapGet (struct.loadF GroupPreparer "srespm" "gpp") "rid" in
          (if: (~ "unprepared")
          then GPP_UNPREPARE
          else GPP_QUERY)
        else
          (if: GroupPreparer__in "gpp" GPP_WAITING
          then GPP_QUERY
          else GPP_REFRESH)))).

Definition GroupCoordinator__NextPrepareAction: val :=
  rec: "GroupCoordinator__NextPrepareAction" "gcoord" "rid" "ts" :=
    Mutex__Lock (struct.loadF GroupCoordinator "mu" "gcoord");;
    (if: (~ (GroupCoordinator__attachedWith "gcoord" "ts"))
    then
      Mutex__Unlock (struct.loadF GroupCoordinator "mu" "gcoord");;
      (#0, #false)
    else
      let: "action" := GroupPreparer__action (struct.loadF GroupCoordinator "gpp" "gcoord") "rid" in
      Mutex__Unlock (struct.loadF GroupCoordinator "mu" "gcoord");;
      ("action", #true)).

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
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      let: ("act", "attached") := GroupCoordinator__NextPrepareAction "gcoord" "rid" "ts" in
      (if: (~ "attached")
      then Break
      else
        (if: "act" = GPP_FAST_PREPARE
        then GroupCoordinator__SendFastPrepare "gcoord" "rid" "ts" "pwrs" "ptgs"
        else
          (if: "act" = GPP_VALIDATE
          then GroupCoordinator__SendValidate "gcoord" "rid" "ts" #1 "pwrs" "ptgs"
          else
            (if: "act" = GPP_PREPARE
            then GroupCoordinator__SendPrepare "gcoord" "rid" "ts" #1
            else
              (if: "act" = GPP_UNPREPARE
              then GroupCoordinator__SendUnprepare "gcoord" "rid" "ts" #1
              else
                (if: "act" = GPP_QUERY
                then GroupCoordinator__SendQuery "gcoord" "rid" "ts" #1
                else
                  (if: "act" = GPP_REFRESH
                  then GroupCoordinator__SendRefresh "gcoord" "rid" "ts" #1
                  else #()))))));;
        (if: "act" = GPP_REFRESH
        then
          time.Sleep params.NS_SEND_REFRESH;;
          Continue
        else
          time.Sleep params.NS_RESEND_PREPARE;;
          Continue)));;
    #().

Definition GroupPreparer__ready: val :=
  rec: "GroupPreparer__ready" "gpp" :=
    GPP_PREPARED ≤ (struct.loadF GroupPreparer "phase" "gpp").

Definition GroupPreparer__getPhase: val :=
  rec: "GroupPreparer__getPhase" "gpp" :=
    struct.loadF GroupPreparer "phase" "gpp".

Definition GroupCoordinator__WaitUntilPrepareDone: val :=
  rec: "GroupCoordinator__WaitUntilPrepareDone" "gcoord" "ts" :=
    let: "phase" := ref (zero_val uint64T) in
    let: "valid" := ref (zero_val boolT) in
    Mutex__Lock (struct.loadF GroupCoordinator "mu" "gcoord");;
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      (if: (~ (GroupCoordinator__attachedWith "gcoord" "ts"))
      then
        "valid" <-[boolT] #false;;
        Break
      else
        let: "ready" := GroupPreparer__ready (struct.loadF GroupCoordinator "gpp" "gcoord") in
        (if: "ready"
        then
          "phase" <-[uint64T] (GroupPreparer__getPhase (struct.loadF GroupCoordinator "gpp" "gcoord"));;
          "valid" <-[boolT] #true;;
          Break
        else
          Cond__Wait (struct.loadF GroupCoordinator "cv" "gcoord");;
          Continue)));;
    Mutex__Unlock (struct.loadF GroupCoordinator "mu" "gcoord");;
    (if: (~ (![boolT] "valid"))
    then (tulip.TXN_PREPARED, #false)
    else
      (if: (![uint64T] "phase") = GPP_COMMITTED
      then (tulip.TXN_COMMITTED, #true)
      else
        (if: (![uint64T] "phase") = GPP_ABORTED
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
    MapIter (struct.loadF GroupCoordinator "addrm" "gcoord") (λ: "ridloop" <>,
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
    let: "idxleader" := struct.loadF GroupCoordinator "idxleader" "gcoord" in
    Mutex__Unlock (struct.loadF GroupCoordinator "mu" "gcoord");;
    SliceGet uint64T (struct.loadF GroupCoordinator "rps" "gcoord") "idxleader".

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
    let: "idxleader" := ((struct.loadF GroupCoordinator "idxleader" "gcoord") + #1) `rem` (slice.len (struct.loadF GroupCoordinator "rps" "gcoord")) in
    struct.storeF GroupCoordinator "idxleader" "gcoord" "idxleader";;
    Mutex__Unlock (struct.loadF GroupCoordinator "mu" "gcoord");;
    SliceGet uint64T (struct.loadF GroupCoordinator "rps" "gcoord") "idxleader".

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

Definition GroupReader__pickLatestValue: val :=
  rec: "GroupReader__pickLatestValue" "grd" "key" :=
    let: "lts" := ref (zero_val uint64T) in
    let: "value" := ref (zero_val (struct.t tulip.Value)) in
    let: "verm" := Fst (MapGet (struct.loadF GroupReader "qreadm" "grd") "key") in
    MapIter "verm" (λ: <> "ver",
      (if: (![uint64T] "lts") ≤ (struct.get tulip.Version "Timestamp" "ver")
      then
        "value" <-[struct.t tulip.Value] (struct.get tulip.Version "Value" "ver");;
        "lts" <-[uint64T] (struct.get tulip.Version "Timestamp" "ver")
      else #()));;
    ![struct.t tulip.Value] "value".

Definition GroupReader__clearVersions: val :=
  rec: "GroupReader__clearVersions" "grd" "key" :=
    MapDelete (struct.loadF GroupReader "qreadm" "grd") "key";;
    #().

Definition GroupReader__processReadResult: val :=
  rec: "GroupReader__processReadResult" "grd" "rid" "key" "ver" :=
    let: (<>, "final") := MapGet (struct.loadF GroupReader "valuem" "grd") "key" in
    (if: "final"
    then #()
    else
      (if: (struct.get tulip.Version "Timestamp" "ver") = #0
      then
        MapInsert (struct.loadF GroupReader "valuem" "grd") "key" (struct.get tulip.Version "Value" "ver");;
        MapDelete (struct.loadF GroupReader "qreadm" "grd") "key";;
        #()
      else
        let: ("qread", "ok") := MapGet (struct.loadF GroupReader "qreadm" "grd") "key" in
        (if: (~ "ok")
        then
          let: "verm" := NewMap uint64T (struct.t tulip.Version) #() in
          MapInsert "verm" "rid" "ver";;
          MapInsert (struct.loadF GroupReader "qreadm" "grd") "key" "verm";;
          #()
        else
          let: (<>, "responded") := MapGet "qread" "rid" in
          (if: "responded"
          then #()
          else
            MapInsert "qread" "rid" "ver";;
            MapInsert (struct.loadF GroupReader "qreadm" "grd") "key" "qread";;
            let: "n" := MapLen "qread" in
            (if: (~ (GroupReader__cquorum "grd" "n"))
            then #()
            else
              let: "latest" := GroupReader__pickLatestValue "grd" "key" in
              MapInsert (struct.loadF GroupReader "valuem" "grd") "key" "latest";;
              GroupReader__clearVersions "grd" "key";;
              #()))))).

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
          then #true
          else #false)))).

Definition GroupPreparer__collectFastDecision: val :=
  rec: "GroupPreparer__collectFastDecision" "gpp" "rid" "b" :=
    MapInsert (struct.loadF GroupPreparer "frespm" "gpp") "rid" "b";;
    #().

Definition GroupPreparer__fquorum: val :=
  rec: "GroupPreparer__fquorum" "gpp" "n" :=
    (quorum.FastQuorum (struct.loadF GroupPreparer "nrps" "gpp")) ≤ "n".

Definition GroupPreparer__tryFastAbort: val :=
  rec: "GroupPreparer__tryFastAbort" "gpp" :=
    let: "n" := util.CountBoolMap (struct.loadF GroupPreparer "frespm" "gpp") #false in
    (if: GroupPreparer__fquorum "gpp" "n"
    then
      struct.storeF GroupPreparer "phase" "gpp" GPP_ABORTED;;
      #true
    else #false).

Definition GroupPreparer__cquorum: val :=
  rec: "GroupPreparer__cquorum" "gpp" "n" :=
    (quorum.ClassicQuorum (struct.loadF GroupPreparer "nrps" "gpp")) ≤ "n".

Definition GroupPreparer__hcquorum: val :=
  rec: "GroupPreparer__hcquorum" "gpp" "n" :=
    (quorum.Half (quorum.ClassicQuorum (struct.loadF GroupPreparer "nrps" "gpp"))) ≤ "n".

Definition GroupPreparer__tryBecomeUnpreparing: val :=
  rec: "GroupPreparer__tryBecomeUnpreparing" "gpp" :=
    let: "nresp" := MapLen (struct.loadF GroupPreparer "frespm" "gpp") in
    (if: (~ (GroupPreparer__cquorum "gpp" "nresp"))
    then #()
    else
      let: "nfu" := util.CountBoolMap (struct.loadF GroupPreparer "frespm" "gpp") #false in
      (if: (~ (GroupPreparer__hcquorum "gpp" "nfu"))
      then #()
      else
        struct.storeF GroupPreparer "srespm" "gpp" (NewMap uint64T boolT #());;
        struct.storeF GroupPreparer "phase" "gpp" GPP_UNPREPARING;;
        #())).

Definition GroupPreparer__tryFastPrepare: val :=
  rec: "GroupPreparer__tryFastPrepare" "gpp" :=
    let: "n" := util.CountBoolMap (struct.loadF GroupPreparer "frespm" "gpp") #true in
    (if: GroupPreparer__fquorum "gpp" "n"
    then
      struct.storeF GroupPreparer "phase" "gpp" GPP_PREPARED;;
      #true
    else #false).

Definition GroupPreparer__collectValidation: val :=
  rec: "GroupPreparer__collectValidation" "gpp" "rid" :=
    MapInsert (struct.loadF GroupPreparer "vdm" "gpp") "rid" #true;;
    #().

Definition GroupPreparer__tryBecomePreparing: val :=
  rec: "GroupPreparer__tryBecomePreparing" "gpp" :=
    let: "nvd" := MapLen (struct.loadF GroupPreparer "vdm" "gpp") in
    (if: (~ (GroupPreparer__cquorum "gpp" "nvd"))
    then #()
    else
      let: "nresp" := MapLen (struct.loadF GroupPreparer "frespm" "gpp") in
      (if: (~ (GroupPreparer__cquorum "gpp" "nresp"))
      then #()
      else
        let: "nfp" := util.CountBoolMap (struct.loadF GroupPreparer "frespm" "gpp") #true in
        (if: (~ (GroupPreparer__hcquorum "gpp" "nfp"))
        then #()
        else
          struct.storeF GroupPreparer "srespm" "gpp" (NewMap uint64T boolT #());;
          struct.storeF GroupPreparer "phase" "gpp" GPP_PREPARING;;
          #()))).

Definition GroupPreparer__processFastPrepareResult: val :=
  rec: "GroupPreparer__processFastPrepareResult" "gpp" "rid" "res" :=
    (if: GroupPreparer__tryResign "gpp" "res"
    then #()
    else
      (if: "res" = tulip.REPLICA_FAILED_VALIDATION
      then
        GroupPreparer__collectFastDecision "gpp" "rid" #false;;
        let: "aborted" := GroupPreparer__tryFastAbort "gpp" in
        (if: "aborted"
        then #()
        else
          (if: (~ (GroupPreparer__in "gpp" GPP_VALIDATING))
          then #()
          else
            GroupPreparer__tryBecomeUnpreparing "gpp";;
            #()))
      else
        GroupPreparer__collectFastDecision "gpp" "rid" #true;;
        (if: GroupPreparer__tryFastPrepare "gpp"
        then #()
        else
          (if: (~ (GroupPreparer__in "gpp" GPP_VALIDATING))
          then #()
          else
            GroupPreparer__collectValidation "gpp" "rid";;
            GroupPreparer__tryBecomePreparing "gpp";;
            #())))).

Definition GroupPreparer__processValidateResult: val :=
  rec: "GroupPreparer__processValidateResult" "gpp" "rid" "res" :=
    (if: GroupPreparer__tryResign "gpp" "res"
    then #()
    else
      (if: "res" = tulip.REPLICA_FAILED_VALIDATION
      then #()
      else
        (if: (~ (GroupPreparer__in "gpp" GPP_VALIDATING))
        then #()
        else
          GroupPreparer__collectValidation "gpp" "rid";;
          GroupPreparer__tryBecomePreparing "gpp";;
          #()))).

Definition GroupPreparer__processPrepareResult: val :=
  rec: "GroupPreparer__processPrepareResult" "gpp" "rid" "res" :=
    (if: GroupPreparer__tryResign "gpp" "res"
    then #()
    else
      (if: (~ (GroupPreparer__in "gpp" GPP_PREPARING))
      then #()
      else
        MapInsert (struct.loadF GroupPreparer "srespm" "gpp") "rid" #true;;
        let: "n" := MapLen (struct.loadF GroupPreparer "srespm" "gpp") in
        (if: GroupPreparer__cquorum "gpp" "n"
        then
          struct.storeF GroupPreparer "phase" "gpp" GPP_PREPARED;;
          #()
        else #()))).

Definition GroupPreparer__processUnprepareResult: val :=
  rec: "GroupPreparer__processUnprepareResult" "gpp" "rid" "res" :=
    (if: GroupPreparer__tryResign "gpp" "res"
    then #()
    else
      (if: (~ (GroupPreparer__in "gpp" GPP_UNPREPARING))
      then #()
      else
        MapInsert (struct.loadF GroupPreparer "srespm" "gpp") "rid" #true;;
        let: "n" := MapLen (struct.loadF GroupPreparer "srespm" "gpp") in
        (if: GroupPreparer__cquorum "gpp" "n"
        then
          struct.storeF GroupPreparer "phase" "gpp" GPP_ABORTED;;
          #()
        else #()))).

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
          (if: (~ (GroupCoordinator__attachedWith "gcoord" (struct.get message.TxnResponse "Timestamp" "msg")))
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
            Cond__Broadcast (struct.loadF GroupCoordinator "cv" "gcoord");;
            Mutex__Unlock (struct.loadF GroupCoordinator "mu" "gcoord");;
            Continue))));;
    #().
