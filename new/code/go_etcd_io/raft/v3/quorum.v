(* autogenerated from go.etcd.io/raft/v3/quorum *)
From New.golang Require Import defn.
Require Export New.code.fmt.
Require Export New.code.go_etcd_io.raft.v3.quorum.slices64.
Require Export New.code.math.
Require Export New.code.sort.
Require Export New.code.strconv.
Require Export New.code.strings.

Module quorum.
Section code.
Context `{ffi_syntax}.


Definition MajorityConfig : go_type := mapT uint64T (structT [
]).

Definition JointConfig : go_type := arrayT 2 MajorityConfig.

Definition pkg_name' : go_string := "go.etcd.io/raft/v3/quorum".

(* go: joint.go:21:22 *)
Definition JointConfig__String : val :=
  rec: "JointConfig__String" "c" <> :=
    exception_do (let: "c" := (ref_ty JointConfig "c") in
    (if: int_gt (let: "$a0" := (![MajorityConfig] (array.elem_ref MajorityConfig (![JointConfig] "c") #(W64 1))) in
    map.len "$a0") #(W64 0)
    then return: ((((method_call #pkg_name' #"MajorityConfig" #"String" (![MajorityConfig] (array.elem_ref MajorityConfig (![JointConfig] "c") #(W64 0)))) #()) + #"&&"%go) + ((method_call #pkg_name' #"MajorityConfig" #"String" (![MajorityConfig] (array.elem_ref MajorityConfig (![JointConfig] "c") #(W64 1)))) #()))
    else do:  #());;;
    return: ((method_call #pkg_name' #"MajorityConfig" #"String" (![MajorityConfig] (array.elem_ref MajorityConfig (![JointConfig] "c") #(W64 0)))) #())).

Definition unit : go_type := structT [
].

(* IDs returns a newly initialized map representing the set of voters present
   in the joint configuration.

   go: joint.go:32:22 *)
Definition JointConfig__IDs : val :=
  rec: "JointConfig__IDs" "c" <> :=
    exception_do (let: "c" := (ref_ty JointConfig "c") in
    let: "m" := (ref_ty (mapT uint64T (structT [
    ])) (zero_val (mapT uint64T (structT [
    ])))) in
    let: "$r0" := (map.make uint64T (structT [
    ]) #()) in
    do:  ("m" <-[mapT uint64T (structT [
    ])] "$r0");;;
    (let: "id" := (ref_ty uint64T (zero_val uint64T)) in
    let: "$range" := (![MajorityConfig] (array.elem_ref MajorityConfig (![JointConfig] "c") #(W64 0))) in
    map.for_range "$range" (λ: "$key" "value",
      do:  ("id" <-[uint64T] "$key");;;
      let: "$r0" := (struct.make (structT [
      ]) [{
      }]) in
      do:  (map.insert (![mapT uint64T (structT [
      ])] "m") (![uint64T] "id") "$r0")));;;
    (let: "id" := (ref_ty uint64T (zero_val uint64T)) in
    let: "$range" := (![MajorityConfig] (array.elem_ref MajorityConfig (![JointConfig] "c") #(W64 1))) in
    map.for_range "$range" (λ: "$key" "value",
      do:  ("id" <-[uint64T] "$key");;;
      let: "$r0" := (struct.make (structT [
      ]) [{
      }]) in
      do:  (map.insert (![mapT uint64T (structT [
      ])] "m") (![uint64T] "id") "$r0")));;;
    return: (![mapT uint64T (structT [
     ])] "m")).

Definition AckedIndexer : go_type := interfaceT.

(* Describe returns a (multi-line) representation of the commit indexes for the
   given lookuper.

   go: joint.go:45:22 *)
Definition JointConfig__Describe : val :=
  rec: "JointConfig__Describe" "c" "l" :=
    exception_do (let: "c" := (ref_ty JointConfig "c") in
    let: "l" := (ref_ty AckedIndexer "l") in
    return: (let: "$a0" := (![AckedIndexer] "l") in
     (method_call #pkg_name' #"MajorityConfig" #"Describe" ((method_call #pkg_name' #"JointConfig" #"IDs" (![JointConfig] "c")) #())) "$a0")).

Definition Index : go_type := uint64T.

(* CommittedIndex returns the largest committed index for the given joint
   quorum. An index is jointly committed if it is committed in both constituent
   majorities.

   go: joint.go:52:22 *)
Definition JointConfig__CommittedIndex : val :=
  rec: "JointConfig__CommittedIndex" "c" "l" :=
    exception_do (let: "c" := (ref_ty JointConfig "c") in
    let: "l" := (ref_ty AckedIndexer "l") in
    let: "idx0" := (ref_ty Index (zero_val Index)) in
    let: "$r0" := (let: "$a0" := (![AckedIndexer] "l") in
    (method_call #pkg_name' #"MajorityConfig" #"CommittedIndex" (![MajorityConfig] (array.elem_ref MajorityConfig (![JointConfig] "c") #(W64 0)))) "$a0") in
    do:  ("idx0" <-[Index] "$r0");;;
    let: "idx1" := (ref_ty Index (zero_val Index)) in
    let: "$r0" := (let: "$a0" := (![AckedIndexer] "l") in
    (method_call #pkg_name' #"MajorityConfig" #"CommittedIndex" (![MajorityConfig] (array.elem_ref MajorityConfig (![JointConfig] "c") #(W64 1)))) "$a0") in
    do:  ("idx1" <-[Index] "$r0");;;
    (if: (![Index] "idx0") < (![Index] "idx1")
    then return: (![Index] "idx0")
    else do:  #());;;
    return: (![Index] "idx1")).

Definition VotePending : expr := #(W8 (1 + 0)).

Definition VoteResult : go_type := uint8T.

Definition VoteLost : expr := #(W8 2).

(* VoteResult takes a mapping of voters to yes/no (true/false) votes and returns
   a result indicating whether the vote is pending, lost, or won. A joint quorum
   requires both majority quorums to vote in favor.

   go: joint.go:64:22 *)
Definition JointConfig__VoteResult : val :=
  rec: "JointConfig__VoteResult" "c" "votes" :=
    exception_do (let: "c" := (ref_ty JointConfig "c") in
    let: "votes" := (ref_ty (mapT uint64T boolT) "votes") in
    let: "r1" := (ref_ty VoteResult (zero_val VoteResult)) in
    let: "$r0" := (let: "$a0" := (![mapT uint64T boolT] "votes") in
    (method_call #pkg_name' #"MajorityConfig" #"VoteResult" (![MajorityConfig] (array.elem_ref MajorityConfig (![JointConfig] "c") #(W64 0)))) "$a0") in
    do:  ("r1" <-[VoteResult] "$r0");;;
    let: "r2" := (ref_ty VoteResult (zero_val VoteResult)) in
    let: "$r0" := (let: "$a0" := (![mapT uint64T boolT] "votes") in
    (method_call #pkg_name' #"MajorityConfig" #"VoteResult" (![MajorityConfig] (array.elem_ref MajorityConfig (![JointConfig] "c") #(W64 1)))) "$a0") in
    do:  ("r2" <-[VoteResult] "$r0");;;
    (if: (![VoteResult] "r1") = (![VoteResult] "r2")
    then return: (![VoteResult] "r1")
    else do:  #());;;
    (if: ((![VoteResult] "r1") = VoteLost) || ((![VoteResult] "r2") = VoteLost)
    then return: (VoteLost)
    else do:  #());;;
    return: (VotePending)).

(* go: majority.go:28:25 *)
Definition MajorityConfig__String : val :=
  rec: "MajorityConfig__String" "c" <> :=
    exception_do (let: "c" := (ref_ty MajorityConfig "c") in
    let: "sl" := (ref_ty sliceT (zero_val sliceT)) in
    let: "$r0" := (slice.make3 uint64T #(W64 0) (let: "$a0" := (![MajorityConfig] "c") in
    map.len "$a0")) in
    do:  ("sl" <-[sliceT] "$r0");;;
    (let: "id" := (ref_ty uint64T (zero_val uint64T)) in
    let: "$range" := (![MajorityConfig] "c") in
    map.for_range "$range" (λ: "$key" "value",
      do:  ("id" <-[uint64T] "$key");;;
      let: "$r0" := (let: "$a0" := (![sliceT] "sl") in
      let: "$a1" := ((let: "$sl0" := (![uint64T] "id") in
      slice.literal uint64T ["$sl0"])) in
      (slice.append sliceT) "$a0" "$a1") in
      do:  ("sl" <-[sliceT] "$r0")));;;
    do:  (let: "$a0" := (interface.make #"slice'"%go (![sliceT] "sl")) in
    let: "$a1" := (λ: "i" "j",
      exception_do (let: "j" := (ref_ty intT "j") in
      let: "i" := (ref_ty intT "i") in
      return: ((![uint64T] (slice.elem_ref uint64T (![sliceT] "sl") (![intT] "i"))) < (![uint64T] (slice.elem_ref uint64T (![sliceT] "sl") (![intT] "j")))))
      ) in
    (func_call #sort.pkg_name' #"Slice"%go) "$a0" "$a1");;;
    let: "buf" := (ref_ty strings.Builder (zero_val strings.Builder)) in
    do:  (let: "$a0" := #(W8 40) in
    (method_call #strings.pkg_name' #"Builder'ptr" #"WriteByte" "buf") "$a0");;;
    (let: "i" := (ref_ty intT (zero_val intT)) in
    let: "$range" := (![sliceT] "sl") in
    slice.for_range uint64T "$range" (λ: "$key" "$value",
      do:  ("i" <-[intT] "$key");;;
      (if: int_gt (![intT] "i") #(W64 0)
      then
        do:  (let: "$a0" := #(W8 32) in
        (method_call #strings.pkg_name' #"Builder'ptr" #"WriteByte" "buf") "$a0")
      else do:  #());;;
      do:  (let: "$a0" := (interface.make #strings.pkg_name' #"Builder'ptr" "buf") in
      let: "$a1" := ((let: "$sl0" := (interface.make #""%go #"uint64"%go (![uint64T] (slice.elem_ref uint64T (![sliceT] "sl") (![intT] "i")))) in
      slice.literal interfaceT ["$sl0"])) in
      (func_call #fmt.pkg_name' #"Fprint"%go) "$a0" "$a1")));;;
    do:  (let: "$a0" := #(W8 41) in
    (method_call #strings.pkg_name' #"Builder'ptr" #"WriteByte" "buf") "$a0");;;
    return: ((method_call #strings.pkg_name' #"Builder'ptr" #"String" "buf") #())).

Definition tup : go_type := structT [
  "id" :: uint64T;
  "idx" :: Index;
  "ok" :: boolT;
  "bar" :: intT
].

(* Describe returns a (multi-line) representation of the commit indexes for the
   given lookuper.

   go: majority.go:55:25 *)
Definition MajorityConfig__Describe : val :=
  rec: "MajorityConfig__Describe" "c" "l" :=
    exception_do (let: "c" := (ref_ty MajorityConfig "c") in
    let: "l" := (ref_ty AckedIndexer "l") in
    (if: (let: "$a0" := (![MajorityConfig] "c") in
    map.len "$a0") = #(W64 0)
    then return: (#"<empty majority quorum>"%go)
    else do:  #());;;
    let: "n" := (ref_ty intT (zero_val intT)) in
    let: "$r0" := (let: "$a0" := (![MajorityConfig] "c") in
    map.len "$a0") in
    do:  ("n" <-[intT] "$r0");;;
    let: "info" := (ref_ty sliceT (zero_val sliceT)) in
    let: "$r0" := (slice.make3 tup #(W64 0) (![intT] "n")) in
    do:  ("info" <-[sliceT] "$r0");;;
    (let: "id" := (ref_ty uint64T (zero_val uint64T)) in
    let: "$range" := (![MajorityConfig] "c") in
    map.for_range "$range" (λ: "$key" "value",
      do:  ("id" <-[uint64T] "$key");;;
      let: "ok" := (ref_ty boolT (zero_val boolT)) in
      let: "idx" := (ref_ty Index (zero_val Index)) in
      let: ("$ret0", "$ret1") := (let: "$a0" := (![uint64T] "id") in
      (interface.get "AckedIndex" (![AckedIndexer] "l")) "$a0") in
      let: "$r0" := "$ret0" in
      let: "$r1" := "$ret1" in
      do:  ("idx" <-[Index] "$r0");;;
      do:  ("ok" <-[boolT] "$r1");;;
      let: "$r0" := (let: "$a0" := (![sliceT] "info") in
      let: "$a1" := ((let: "$sl0" := (let: "$id" := (![uint64T] "id") in
      let: "$idx" := (![Index] "idx") in
      let: "$ok" := (![boolT] "ok") in
      struct.make tup [{
        "id" ::= "$id";
        "idx" ::= "$idx";
        "ok" ::= "$ok";
        "bar" ::= zero_val intT
      }]) in
      slice.literal tup ["$sl0"])) in
      (slice.append sliceT) "$a0" "$a1") in
      do:  ("info" <-[sliceT] "$r0")));;;
    do:  (let: "$a0" := (interface.make #"slice'"%go (![sliceT] "info")) in
    let: "$a1" := (λ: "i" "j",
      exception_do (let: "j" := (ref_ty intT "j") in
      let: "i" := (ref_ty intT "i") in
      (if: (![Index] (struct.field_ref tup "idx" (slice.elem_ref tup (![sliceT] "info") (![intT] "i")))) = (![Index] (struct.field_ref tup "idx" (slice.elem_ref tup (![sliceT] "info") (![intT] "j"))))
      then return: ((![uint64T] (struct.field_ref tup "id" (slice.elem_ref tup (![sliceT] "info") (![intT] "i")))) < (![uint64T] (struct.field_ref tup "id" (slice.elem_ref tup (![sliceT] "info") (![intT] "j")))))
      else do:  #());;;
      return: ((![Index] (struct.field_ref tup "idx" (slice.elem_ref tup (![sliceT] "info") (![intT] "i")))) < (![Index] (struct.field_ref tup "idx" (slice.elem_ref tup (![sliceT] "info") (![intT] "j"))))))
      ) in
    (func_call #sort.pkg_name' #"Slice"%go) "$a0" "$a1");;;
    (let: "i" := (ref_ty intT (zero_val intT)) in
    let: "$range" := (![sliceT] "info") in
    slice.for_range tup "$range" (λ: "$key" "$value",
      do:  ("i" <-[intT] "$key");;;
      (if: (int_gt (![intT] "i") #(W64 0)) && ((![Index] (struct.field_ref tup "idx" (slice.elem_ref tup (![sliceT] "info") ((![intT] "i") - #(W64 1))))) < (![Index] (struct.field_ref tup "idx" (slice.elem_ref tup (![sliceT] "info") (![intT] "i")))))
      then
        let: "$r0" := (![intT] "i") in
        do:  ((struct.field_ref tup "bar" (slice.elem_ref tup (![sliceT] "info") (![intT] "i"))) <-[intT] "$r0")
      else do:  #())));;;
    do:  (let: "$a0" := (interface.make #"slice'"%go (![sliceT] "info")) in
    let: "$a1" := (λ: "i" "j",
      exception_do (let: "j" := (ref_ty intT "j") in
      let: "i" := (ref_ty intT "i") in
      return: ((![uint64T] (struct.field_ref tup "id" (slice.elem_ref tup (![sliceT] "info") (![intT] "i")))) < (![uint64T] (struct.field_ref tup "id" (slice.elem_ref tup (![sliceT] "info") (![intT] "j"))))))
      ) in
    (func_call #sort.pkg_name' #"Slice"%go) "$a0" "$a1");;;
    let: "buf" := (ref_ty strings.Builder (zero_val strings.Builder)) in
    do:  (let: "$a0" := (interface.make #strings.pkg_name' #"Builder'ptr" "buf") in
    let: "$a1" := ((let: "$sl0" := (interface.make #""%go #"string"%go ((let: "$a0" := #" "%go in
    let: "$a1" := (![intT] "n") in
    (func_call #strings.pkg_name' #"Repeat"%go) "$a0" "$a1") + #"    idx
    "%go)) in
    slice.literal interfaceT ["$sl0"])) in
    (func_call #fmt.pkg_name' #"Fprint"%go) "$a0" "$a1");;;
    (let: "i" := (ref_ty intT (zero_val intT)) in
    let: "$range" := (![sliceT] "info") in
    slice.for_range tup "$range" (λ: "$key" "$value",
      do:  ("i" <-[intT] "$key");;;
      let: "bar" := (ref_ty intT (zero_val intT)) in
      let: "$r0" := (![intT] (struct.field_ref tup "bar" (slice.elem_ref tup (![sliceT] "info") (![intT] "i")))) in
      do:  ("bar" <-[intT] "$r0");;;
      (if: (~ (![boolT] (struct.field_ref tup "ok" (slice.elem_ref tup (![sliceT] "info") (![intT] "i")))))
      then
        do:  (let: "$a0" := (interface.make #strings.pkg_name' #"Builder'ptr" "buf") in
        let: "$a1" := ((let: "$sl0" := (interface.make #""%go #"string"%go (#"?"%go + (let: "$a0" := #" "%go in
        let: "$a1" := (![intT] "n") in
        (func_call #strings.pkg_name' #"Repeat"%go) "$a0" "$a1"))) in
        slice.literal interfaceT ["$sl0"])) in
        (func_call #fmt.pkg_name' #"Fprint"%go) "$a0" "$a1")
      else
        do:  (let: "$a0" := (interface.make #strings.pkg_name' #"Builder'ptr" "buf") in
        let: "$a1" := ((let: "$sl0" := (interface.make #""%go #"string"%go (((let: "$a0" := #"x"%go in
        let: "$a1" := (![intT] "bar") in
        (func_call #strings.pkg_name' #"Repeat"%go) "$a0" "$a1") + #">"%go) + (let: "$a0" := #" "%go in
        let: "$a1" := ((![intT] "n") - (![intT] "bar")) in
        (func_call #strings.pkg_name' #"Repeat"%go) "$a0" "$a1"))) in
        slice.literal interfaceT ["$sl0"])) in
        (func_call #fmt.pkg_name' #"Fprint"%go) "$a0" "$a1"));;;
      do:  (let: "$a0" := (interface.make #strings.pkg_name' #"Builder'ptr" "buf") in
      let: "$a1" := #" %5d    (id=%d)
      "%go in
      let: "$a2" := ((let: "$sl0" := (interface.make #pkg_name' #"Index" (![Index] (struct.field_ref tup "idx" (slice.elem_ref tup (![sliceT] "info") (![intT] "i"))))) in
      let: "$sl1" := (interface.make #""%go #"uint64"%go (![uint64T] (struct.field_ref tup "id" (slice.elem_ref tup (![sliceT] "info") (![intT] "i"))))) in
      slice.literal interfaceT ["$sl0"; "$sl1"])) in
      (func_call #fmt.pkg_name' #"Fprintf"%go) "$a0" "$a1" "$a2")));;;
    return: ((method_call #strings.pkg_name' #"Builder'ptr" #"String" "buf") #())).

(* Slice returns the MajorityConfig as a sorted slice.

   go: majority.go:108:25 *)
Definition MajorityConfig__Slice : val :=
  rec: "MajorityConfig__Slice" "c" <> :=
    exception_do (let: "c" := (ref_ty MajorityConfig "c") in
    let: "sl" := (ref_ty sliceT (zero_val sliceT)) in
    (let: "id" := (ref_ty uint64T (zero_val uint64T)) in
    let: "$range" := (![MajorityConfig] "c") in
    map.for_range "$range" (λ: "$key" "value",
      do:  ("id" <-[uint64T] "$key");;;
      let: "$r0" := (let: "$a0" := (![sliceT] "sl") in
      let: "$a1" := ((let: "$sl0" := (![uint64T] "id") in
      slice.literal uint64T ["$sl0"])) in
      (slice.append sliceT) "$a0" "$a1") in
      do:  ("sl" <-[sliceT] "$r0")));;;
    do:  (let: "$a0" := (interface.make #"slice'"%go (![sliceT] "sl")) in
    let: "$a1" := (λ: "i" "j",
      exception_do (let: "j" := (ref_ty intT "j") in
      let: "i" := (ref_ty intT "i") in
      return: ((![uint64T] (slice.elem_ref uint64T (![sliceT] "sl") (![intT] "i"))) < (![uint64T] (slice.elem_ref uint64T (![sliceT] "sl") (![intT] "j")))))
      ) in
    (func_call #sort.pkg_name' #"Slice"%go) "$a0" "$a1");;;
    return: (![sliceT] "sl")).

(* CommittedIndex computes the committed index from those supplied via the
   provided AckedIndexer (for the active config).

   go: majority.go:119:25 *)
Definition MajorityConfig__CommittedIndex : val :=
  rec: "MajorityConfig__CommittedIndex" "c" "l" :=
    exception_do (let: "c" := (ref_ty MajorityConfig "c") in
    let: "l" := (ref_ty AckedIndexer "l") in
    let: "n" := (ref_ty intT (zero_val intT)) in
    let: "$r0" := (let: "$a0" := (![MajorityConfig] "c") in
    map.len "$a0") in
    do:  ("n" <-[intT] "$r0");;;
    (if: (![intT] "n") = #(W64 0)
    then return: (#(W64 math.MaxUint64))
    else do:  #());;;
    let: "stk" := (ref_ty (arrayT 7 uint64T) (zero_val (arrayT 7 uint64T))) in
    let: "srt" := (ref_ty sliceT (zero_val sliceT)) in
    (if: int_geq (array.len (arrayT 7 uint64T)) (![intT] "n")
    then
      let: "$r0" := (let: "$a" := "stk" in
      array.slice "$a" #(W64 0) (![intT] "n")) in
      do:  ("srt" <-[sliceT] "$r0")
    else
      let: "$r0" := (slice.make2 uint64T (![intT] "n")) in
      do:  ("srt" <-[sliceT] "$r0"));;;
    let: "i" := (ref_ty intT (zero_val intT)) in
    let: "$r0" := ((![intT] "n") - #(W64 1)) in
    do:  ("i" <-[intT] "$r0");;;
    (let: "id" := (ref_ty uint64T (zero_val uint64T)) in
    let: "$range" := (![MajorityConfig] "c") in
    map.for_range "$range" (λ: "$key" "value",
      do:  ("id" <-[uint64T] "$key");;;
      (let: "ok" := (ref_ty boolT (zero_val boolT)) in
      let: "idx" := (ref_ty Index (zero_val Index)) in
      let: ("$ret0", "$ret1") := (let: "$a0" := (![uint64T] "id") in
      (interface.get "AckedIndex" (![AckedIndexer] "l")) "$a0") in
      let: "$r0" := "$ret0" in
      let: "$r1" := "$ret1" in
      do:  ("idx" <-[Index] "$r0");;;
      do:  ("ok" <-[boolT] "$r1");;;
      (if: ![boolT] "ok"
      then
        let: "$r0" := (![Index] "idx") in
        do:  ((slice.elem_ref uint64T (![sliceT] "srt") (![intT] "i")) <-[uint64T] "$r0");;;
        do:  ("i" <-[intT] ((![intT] "i") - #(W64 1)))
      else do:  #()))));;;
    do:  (let: "$a0" := (![sliceT] "srt") in
    (func_call #slices64.pkg_name' #"Sort"%go) "$a0");;;
    let: "pos" := (ref_ty intT (zero_val intT)) in
    let: "$r0" := ((![intT] "n") - ((int_quot (![intT] "n") #(W64 2)) + #(W64 1))) in
    do:  ("pos" <-[intT] "$r0");;;
    return: (![uint64T] (slice.elem_ref uint64T (![sliceT] "srt") (![intT] "pos")))).

Definition VoteWon : expr := #(W8 3).

(* VoteResult takes a mapping of voters to yes/no (true/false) votes and returns
   a result indicating whether the vote is pending (i.e. neither a quorum of
   yes/no has been reached), won (a quorum of yes has been reached), or lost (a
   quorum of no has been reached).

   go: majority.go:168:25 *)
Definition MajorityConfig__VoteResult : val :=
  rec: "MajorityConfig__VoteResult" "c" "votes" :=
    exception_do (let: "c" := (ref_ty MajorityConfig "c") in
    let: "votes" := (ref_ty (mapT uint64T boolT) "votes") in
    (if: (let: "$a0" := (![MajorityConfig] "c") in
    map.len "$a0") = #(W64 0)
    then return: (VoteWon)
    else do:  #());;;
    let: "votedCnt" := (ref_ty intT (zero_val intT)) in
    let: "missing" := (ref_ty intT (zero_val intT)) in
    (let: "id" := (ref_ty uint64T (zero_val uint64T)) in
    let: "$range" := (![MajorityConfig] "c") in
    map.for_range "$range" (λ: "$key" "value",
      do:  ("id" <-[uint64T] "$key");;;
      let: "ok" := (ref_ty boolT (zero_val boolT)) in
      let: "v" := (ref_ty boolT (zero_val boolT)) in
      let: ("$ret0", "$ret1") := (map.get (![mapT uint64T boolT] "votes") (![uint64T] "id")) in
      let: "$r0" := "$ret0" in
      let: "$r1" := "$ret1" in
      do:  ("v" <-[boolT] "$r0");;;
      do:  ("ok" <-[boolT] "$r1");;;
      (if: (~ (![boolT] "ok"))
      then
        do:  ("missing" <-[intT] ((![intT] "missing") + #(W64 1)));;;
        continue: #()
      else do:  #());;;
      (if: ![boolT] "v"
      then do:  ("votedCnt" <-[intT] ((![intT] "votedCnt") + #(W64 1)))
      else do:  #())));;;
    let: "q" := (ref_ty intT (zero_val intT)) in
    let: "$r0" := ((int_quot (let: "$a0" := (![MajorityConfig] "c") in
    map.len "$a0") #(W64 2)) + #(W64 1)) in
    do:  ("q" <-[intT] "$r0");;;
    (if: int_geq (![intT] "votedCnt") (![intT] "q")
    then return: (VoteWon)
    else do:  #());;;
    (if: int_geq ((![intT] "votedCnt") + (![intT] "missing")) (![intT] "q")
    then return: (VotePending)
    else do:  #());;;
    return: (VoteLost)).

(* go: quorum.go:25:16 *)
Definition Index__String : val :=
  rec: "Index__String" "i" <> :=
    exception_do (let: "i" := (ref_ty Index "i") in
    (if: (![Index] "i") = #(W64 math.MaxUint64)
    then return: (#"∞"%go)
    else do:  #());;;
    return: (let: "$a0" := (![Index] "i") in
     let: "$a1" := #(W64 10) in
     (func_call #strconv.pkg_name' #"FormatUint"%go) "$a0" "$a1")).

Definition mapAckIndexer : go_type := mapT uint64T Index.

(* go: quorum.go:40:24 *)
Definition mapAckIndexer__AckedIndex : val :=
  rec: "mapAckIndexer__AckedIndex" "m" "id" :=
    exception_do (let: "m" := (ref_ty mapAckIndexer "m") in
    let: "id" := (ref_ty uint64T "id") in
    let: "ok" := (ref_ty boolT (zero_val boolT)) in
    let: "idx" := (ref_ty Index (zero_val Index)) in
    let: ("$ret0", "$ret1") := (map.get (![mapAckIndexer] "m") (![uint64T] "id")) in
    let: "$r0" := "$ret0" in
    let: "$r1" := "$ret1" in
    do:  ("idx" <-[Index] "$r0");;;
    do:  ("ok" <-[boolT] "$r1");;;
    return: (![Index] "idx", ![boolT] "ok")).

(* go: voteresult_string.go:7:6 *)
Definition _unused : val :=
  rec: "_unused" <> :=
    exception_do (let: "x" := (ref_ty (arrayT 1 (structT [
    ])) (zero_val (arrayT 1 (structT [
    ])))) in
    let: "$r0" := (![structT [
    ]] (array.elem_ref (structT [
    ]) (![arrayT 1 (structT [
    ])] "x") (VotePending - #(W8 1)))) in
    do:  "$r0";;;
    let: "$r0" := (![structT [
    ]] (array.elem_ref (structT [
    ]) (![arrayT 1 (structT [
    ])] "x") (VoteLost - #(W8 2)))) in
    do:  "$r0";;;
    let: "$r0" := (![structT [
    ]] (array.elem_ref (structT [
    ]) (![arrayT 1 (structT [
    ])] "x") (VoteWon - #(W8 3)))) in
    do:  "$r0").

Definition _VoteResult_name : go_string := "VotePendingVoteLostVoteWon"%go.

Definition vars' : list (go_string * go_type) := [("_VoteResult_index"%go, arrayT 4 uint8T)].

Definition functions' : list (go_string * val) := [("_unused"%go, _unused)].

Definition msets' : list (go_string * (list (go_string * val))) := [("JointConfig"%go, [("CommittedIndex"%go, JointConfig__CommittedIndex); ("Describe"%go, JointConfig__Describe); ("IDs"%go, JointConfig__IDs); ("String"%go, JointConfig__String); ("VoteResult"%go, JointConfig__VoteResult)]); ("JointConfig'ptr"%go, [("CommittedIndex"%go, (λ: "$recvAddr",
                 method_call #pkg_name' #"JointConfig" #"CommittedIndex" (![JointConfig] "$recvAddr")
                 )%V); ("Describe"%go, (λ: "$recvAddr",
                 method_call #pkg_name' #"JointConfig" #"Describe" (![JointConfig] "$recvAddr")
                 )%V); ("IDs"%go, (λ: "$recvAddr",
                 method_call #pkg_name' #"JointConfig" #"IDs" (![JointConfig] "$recvAddr")
                 )%V); ("String"%go, (λ: "$recvAddr",
                 method_call #pkg_name' #"JointConfig" #"String" (![JointConfig] "$recvAddr")
                 )%V); ("VoteResult"%go, (λ: "$recvAddr",
                 method_call #pkg_name' #"JointConfig" #"VoteResult" (![JointConfig] "$recvAddr")
                 )%V)]); ("MajorityConfig"%go, [("CommittedIndex"%go, MajorityConfig__CommittedIndex); ("Describe"%go, MajorityConfig__Describe); ("Slice"%go, MajorityConfig__Slice); ("String"%go, MajorityConfig__String); ("VoteResult"%go, MajorityConfig__VoteResult)]); ("MajorityConfig'ptr"%go, [("CommittedIndex"%go, (λ: "$recvAddr",
                 method_call #pkg_name' #"MajorityConfig" #"CommittedIndex" (![MajorityConfig] "$recvAddr")
                 )%V); ("Describe"%go, (λ: "$recvAddr",
                 method_call #pkg_name' #"MajorityConfig" #"Describe" (![MajorityConfig] "$recvAddr")
                 )%V); ("Slice"%go, (λ: "$recvAddr",
                 method_call #pkg_name' #"MajorityConfig" #"Slice" (![MajorityConfig] "$recvAddr")
                 )%V); ("String"%go, (λ: "$recvAddr",
                 method_call #pkg_name' #"MajorityConfig" #"String" (![MajorityConfig] "$recvAddr")
                 )%V); ("VoteResult"%go, (λ: "$recvAddr",
                 method_call #pkg_name' #"MajorityConfig" #"VoteResult" (![MajorityConfig] "$recvAddr")
                 )%V)]); ("tup"%go, []); ("tup'ptr"%go, []); ("Index"%go, [("String"%go, Index__String)]); ("Index'ptr"%go, [("String"%go, (λ: "$recvAddr",
                 method_call #pkg_name' #"Index" #"String" (![Index] "$recvAddr")
                 )%V)]); ("mapAckIndexer"%go, [("AckedIndex"%go, mapAckIndexer__AckedIndex)]); ("mapAckIndexer'ptr"%go, [("AckedIndex"%go, (λ: "$recvAddr",
                 method_call #pkg_name' #"mapAckIndexer" #"AckedIndex" (![mapAckIndexer] "$recvAddr")
                 )%V)]); ("VoteResult"%go, []); ("VoteResult'ptr"%go, [])].

Definition initialize' : val :=
  rec: "initialize'" <> :=
    globals.package_init pkg_name' vars' functions' msets' (λ: <>,
      exception_do (do:  strconv.initialize';;;
      do:  strings.initialize';;;
      do:  sort.initialize';;;
      do:  slices64.initialize';;;
      do:  math.initialize';;;
      do:  fmt.initialize';;;
      let: "$r0" := ((let: "$ar0" := #(W8 0) in
      let: "$ar1" := #(W8 11) in
      let: "$ar2" := #(W8 19) in
      let: "$ar3" := #(W8 26) in
      array.literal ["$ar0"; "$ar1"; "$ar2"; "$ar3"])) in
      do:  ((globals.get #pkg_name' #"_VoteResult_index"%go) <-[arrayT 4 uint8T] "$r0"))
      ).

End code.
End quorum.
