(* autogenerated from github.com/mit-pdos/tulip/txn *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_com.goose_lang.std.
From Goose Require github_com.mit_pdos.tulip.gcoord.
From Goose Require github_com.mit_pdos.tulip.params.
From Goose Require github_com.mit_pdos.tulip.tulip.
From Perennial.goose_lang.trusted Require Import github_com.mit_pdos.tulip.trusted_proph.
From Perennial.goose_lang.trusted Require Import github_com.mit_pdos.tulip.trusted_time.

From Perennial.goose_lang Require Import ffi.grove_prelude.

Definition Txn := struct.decl [
  "sid" :: uint64T;
  "ts" :: uint64T;
  "wrs" :: mapT (mapT (struct.t tulip.Value));
  "wrsp" :: mapT (struct.t tulip.Value);
  "ptgs" :: slice.T uint64T;
  "gcoords" :: mapT ptrT;
  "proph" :: ProphIdT
].

Definition mkTxn: val :=
  rec: "mkTxn" "sid" "gaddrm" "proph" :=
    let: "txn" := struct.new Txn [
      "sid" ::= "sid";
      "proph" ::= "proph"
    ] in
    let: "wrs" := NewMap uint64T (mapT (struct.t tulip.Value)) #() in
    MapIter "gaddrm" (λ: "gid" <>,
      MapInsert "wrs" "gid" (NewMap stringT (struct.t tulip.Value) #()));;
    struct.storeF Txn "wrs" "txn" "wrs";;
    struct.storeF Txn "wrsp" "txn" (NewMap stringT (struct.t tulip.Value) #());;
    let: "gcoords" := NewMap uint64T ptrT #() in
    MapIter "gaddrm" (λ: "gid" "addrm",
      MapInsert "gcoords" "gid" (gcoord.Start "addrm"));;
    struct.storeF Txn "gcoords" "txn" "gcoords";;
    "txn".

Definition MkTxn: val :=
  rec: "MkTxn" "sid" "gaddrm" :=
    mkTxn "sid" "gaddrm" (NewProph #()).

Definition getTimestamp: val :=
  rec: "getTimestamp" "sid" :=
    let: "ts" := trusted_time.GetTime #() in
    let: "n" := params.N_TXN_SITES in
    let: "tid" := (((std.SumAssumeNoOverflow "ts" "n") `quot` "n") * "n") + "sid" in
    Skip;;
    (for: (λ: <>, (trusted_time.GetTime #()) ≤ "tid"); (λ: <>, Skip) := λ: <>,
      Continue);;
    "tid".

Definition Txn__begin: val :=
  rec: "Txn__begin" "txn" :=
    struct.storeF Txn "ts" "txn" (getTimestamp (struct.loadF Txn "sid" "txn"));;
    #().

Definition Txn__attach: val :=
  rec: "Txn__attach" "txn" :=
    MapIter (struct.loadF Txn "gcoords" "txn") (λ: <> "gcoord",
      gcoord.GroupCoordinator__Attach "gcoord" (struct.loadF Txn "ts" "txn"));;
    #().

Definition Txn__resetwrs: val :=
  rec: "Txn__resetwrs" "txn" :=
    let: "wrs" := NewMap uint64T (mapT (struct.t tulip.Value)) #() in
    MapIter (struct.loadF Txn "wrs" "txn") (λ: "gid" <>,
      MapInsert "wrs" "gid" (NewMap stringT (struct.t tulip.Value) #()));;
    struct.storeF Txn "wrs" "txn" "wrs";;
    struct.storeF Txn "wrsp" "txn" (NewMap stringT (struct.t tulip.Value) #());;
    #().

Definition Txn__keyToGroup: val :=
  rec: "Txn__keyToGroup" "txn" "key" :=
    (StringLength "key") `rem` (MapLen (struct.loadF Txn "wrs" "txn")).

Definition Txn__setwrs: val :=
  rec: "Txn__setwrs" "txn" "key" "value" :=
    let: "gid" := Txn__keyToGroup "txn" "key" in
    let: "pwrs" := Fst (MapGet (struct.loadF Txn "wrs" "txn") "gid") in
    MapInsert "pwrs" "key" "value";;
    MapInsert (struct.loadF Txn "wrsp" "txn") "key" "value";;
    #().

Definition Txn__getwrs: val :=
  rec: "Txn__getwrs" "txn" "key" :=
    let: "gid" := Txn__keyToGroup "txn" "key" in
    let: "pwrs" := Fst (MapGet (struct.loadF Txn "wrs" "txn") "gid") in
    let: ("v", "ok") := MapGet "pwrs" "key" in
    ("v", "ok").

Definition Txn__setptgs: val :=
  rec: "Txn__setptgs" "txn" :=
    let: "ptgs" := ref_to (slice.T uint64T) (NewSliceWithCap uint64T #0 #1) in
    MapIter (struct.loadF Txn "wrs" "txn") (λ: "gid" "pwrs",
      (if: (MapLen "pwrs") ≠ #0
      then "ptgs" <-[slice.T uint64T] (SliceAppend uint64T (![slice.T uint64T] "ptgs") "gid")
      else #()));;
    struct.storeF Txn "ptgs" "txn" (![slice.T uint64T] "ptgs");;
    #().

Definition Txn__reset: val :=
  rec: "Txn__reset" "txn" :=
    Txn__resetwrs "txn";;
    #().

Definition Txn__prepare: val :=
  rec: "Txn__prepare" "txn" :=
    Txn__setptgs "txn";;
    let: "ts" := struct.loadF Txn "ts" "txn" in
    let: "ptgs" := struct.loadF Txn "ptgs" "txn" in
    let: "mu" := newMutex #() in
    let: "cv" := NewCond "mu" in
    let: "np" := ref_to uint64T #0 in
    let: "st" := ref_to uint64T tulip.TXN_PREPARED in
    let: "wrs" := struct.loadF Txn "wrs" "txn" in
    ForSlice uint64T <> "gid" "ptgs"
      (let: "gcoord" := Fst (MapGet (struct.loadF Txn "gcoords" "txn") "gid") in
      let: "pwrs" := Fst (MapGet "wrs" "gid") in
      Fork (let: ("stg", "ok") := gcoord.GroupCoordinator__Prepare "gcoord" "ts" "ptgs" "pwrs" in
            (if: "ok"
            then
              Mutex__Lock "mu";;
              (if: "stg" = tulip.TXN_PREPARED
              then "np" <-[uint64T] ((![uint64T] "np") + #1)
              else "st" <-[uint64T] "stg");;
              Mutex__Unlock "mu";;
              Cond__Signal "cv"
            else #())));;
    Mutex__Lock "mu";;
    Skip;;
    (for: (λ: <>, ((![uint64T] "st") = tulip.TXN_PREPARED) && ((![uint64T] "np") ≠ (slice.len "ptgs"))); (λ: <>, Skip) := λ: <>,
      Cond__Wait "cv";;
      Continue);;
    let: "status" := ![uint64T] "st" in
    Mutex__Unlock "mu";;
    "status".

Definition Txn__commit: val :=
  rec: "Txn__commit" "txn" :=
    trusted_proph.ResolveCommit (struct.loadF Txn "proph" "txn") (struct.loadF Txn "ts" "txn") (struct.loadF Txn "wrsp" "txn");;
    let: "ts" := struct.loadF Txn "ts" "txn" in
    let: "wrs" := struct.loadF Txn "wrs" "txn" in
    ForSlice uint64T <> "gid" (struct.loadF Txn "ptgs" "txn")
      (let: "gcoord" := Fst (MapGet (struct.loadF Txn "gcoords" "txn") "gid") in
      let: "pwrs" := Fst (MapGet "wrs" "gid") in
      Fork (gcoord.GroupCoordinator__Commit "gcoord" "ts" "pwrs"));;
    Txn__reset "txn";;
    #().

Definition Txn__abort: val :=
  rec: "Txn__abort" "txn" :=
    trusted_proph.ResolveAbort (struct.loadF Txn "proph" "txn") (struct.loadF Txn "ts" "txn");;
    let: "ts" := struct.loadF Txn "ts" "txn" in
    ForSlice uint64T <> "gid" (struct.loadF Txn "ptgs" "txn")
      (let: "gcoord" := Fst (MapGet (struct.loadF Txn "gcoords" "txn") "gid") in
      Fork (gcoord.GroupCoordinator__Abort "gcoord" "ts"));;
    Txn__reset "txn";;
    #().

Definition Txn__cancel: val :=
  rec: "Txn__cancel" "txn" :=
    trusted_proph.ResolveAbort (struct.loadF Txn "proph" "txn") (struct.loadF Txn "ts" "txn");;
    Txn__reset "txn";;
    #().

Definition Txn__Read: val :=
  rec: "Txn__Read" "txn" "key" :=
    let: ("vlocal", "hit") := Txn__getwrs "txn" "key" in
    (if: "hit"
    then ("vlocal", #true)
    else
      let: "gid" := Txn__keyToGroup "txn" "key" in
      let: "gcoord" := Fst (MapGet (struct.loadF Txn "gcoords" "txn") "gid") in
      let: ("v", "ok") := gcoord.GroupCoordinator__Read "gcoord" (struct.loadF Txn "ts" "txn") "key" in
      (if: (~ "ok")
      then
        (struct.mk tulip.Value [
         ], #false)
      else
        trusted_proph.ResolveRead (struct.loadF Txn "proph" "txn") (struct.loadF Txn "ts" "txn") "key";;
        ("v", #true))).

Definition Txn__Write: val :=
  rec: "Txn__Write" "txn" "key" "value" :=
    let: "v" := struct.mk tulip.Value [
      "Present" ::= #true;
      "Content" ::= "value"
    ] in
    Txn__setwrs "txn" "key" "v";;
    #().

Definition Txn__Delete: val :=
  rec: "Txn__Delete" "txn" "key" :=
    let: "v" := struct.mk tulip.Value [
      "Present" ::= #false
    ] in
    Txn__setwrs "txn" "key" "v";;
    #().

Definition Txn__Run: val :=
  rec: "Txn__Run" "txn" "body" :=
    Txn__begin "txn";;
    Txn__attach "txn";;
    let: "cmt" := "body" "txn" in
    (if: (~ "cmt")
    then
      Txn__cancel "txn";;
      #false
    else
      let: "status" := Txn__prepare "txn" in
      (if: "status" = tulip.TXN_COMMITTED
      then
        Txn__reset "txn";;
        #true
      else
        (if: "status" = tulip.TXN_ABORTED
        then
          Txn__abort "txn";;
          #false
        else
          Txn__commit "txn";;
          #true))).
