(* autogenerated from github.com/mit-pdos/go-journal/lockmap *)
From New.golang Require Import defn.
Require Export New.code.sync.

Definition lockmap : go_string := "github.com/mit-pdos/go-journal/lockmap".

Module lockmap.
Section code.
Context `{ffi_syntax}.


Definition lockState : go_type := structT [
  "held" :: boolT;
  "cond" :: ptrT;
  "waiters" :: uint64T
].

Definition lockShard : go_type := structT [
  "mu" :: ptrT;
  "state" :: mapT uint64T ptrT
].

(* go: lock.go:30:6 *)
Definition mkLockShard : val :=
  rec: "mkLockShard" <> :=
    exception_do (let: "state" := (mem.alloc (type.zero_val (type.mapT #uint64T #ptrT))) in
    let: "$r0" := (map.make #uint64T #ptrT) in
    do:  ("state" <-[type.mapT #uint64T #ptrT] "$r0");;;
    let: "mu" := (mem.alloc (type.zero_val #ptrT)) in
    let: "$r0" := (mem.alloc (type.zero_val #sync.Mutex)) in
    do:  ("mu" <-[#ptrT] "$r0");;;
    let: "a" := (mem.alloc (type.zero_val #ptrT)) in
    let: "$r0" := (mem.alloc (let: "$mu" := (![#ptrT] "mu") in
    let: "$state" := (![type.mapT #uint64T #ptrT] "state") in
    struct.make #lockShard [{
      "mu" ::= "$mu";
      "state" ::= "$state"
    }])) in
    do:  ("a" <-[#ptrT] "$r0");;;
    return: (![#ptrT] "a")).

(* go: lock.go:40:24 *)
Definition lockShard__acquire : val :=
  rec: "lockShard__acquire" "lmap" "addr" :=
    exception_do (let: "lmap" := (mem.alloc "lmap") in
    let: "addr" := (mem.alloc "addr") in
    do:  ((method_call #sync #"Mutex'ptr" #"Lock" (![#ptrT] (struct.field_ref #lockShard #"mu"%go (![#ptrT] "lmap")))) #());;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      let: "state" := (mem.alloc (type.zero_val #ptrT)) in
      let: "ok1" := (mem.alloc (type.zero_val #boolT)) in
      let: "state1" := (mem.alloc (type.zero_val #ptrT)) in
      let: ("$ret0", "$ret1") := (map.get (![type.mapT #uint64T #ptrT] (struct.field_ref #lockShard #"state"%go (![#ptrT] "lmap"))) (![#uint64T] "addr")) in
      let: "$r0" := "$ret0" in
      let: "$r1" := "$ret1" in
      do:  ("state1" <-[#ptrT] "$r0");;;
      do:  ("ok1" <-[#boolT] "$r1");;;
      (if: ![#boolT] "ok1"
      then
        let: "$r0" := (![#ptrT] "state1") in
        do:  ("state" <-[#ptrT] "$r0")
      else
        let: "$r0" := (mem.alloc (let: "$held" := #false in
        let: "$cond" := (let: "$a0" := (interface.make (#sync, #"Mutex'ptr") (![#ptrT] (struct.field_ref #lockShard #"mu"%go (![#ptrT] "lmap")))) in
        (func_call #sync.sync #"NewCond"%go) "$a0") in
        let: "$waiters" := #(W64 0) in
        struct.make #lockState [{
          "held" ::= "$held";
          "cond" ::= "$cond";
          "waiters" ::= "$waiters"
        }])) in
        do:  ("state" <-[#ptrT] "$r0");;;
        let: "$r0" := (![#ptrT] "state") in
        do:  (map.insert (![type.mapT #uint64T #ptrT] (struct.field_ref #lockShard #"state"%go (![#ptrT] "lmap"))) (![#uint64T] "addr") "$r0"));;;
      let: "acquired" := (mem.alloc (type.zero_val #boolT)) in
      (if: (~ (![#boolT] (struct.field_ref #lockState #"held"%go (![#ptrT] "state"))))
      then
        let: "$r0" := #true in
        do:  ((struct.field_ref #lockState #"held"%go (![#ptrT] "state")) <-[#boolT] "$r0");;;
        let: "$r0" := #true in
        do:  ("acquired" <-[#boolT] "$r0")
      else
        do:  ((struct.field_ref #lockState #"waiters"%go (![#ptrT] "state")) <-[#uint64T] ((![#uint64T] (struct.field_ref #lockState #"waiters"%go (![#ptrT] "state"))) + #(W64 1)));;;
        do:  ((method_call #sync #"Cond'ptr" #"Wait" (![#ptrT] (struct.field_ref #lockState #"cond"%go (![#ptrT] "state")))) #());;;
        let: "ok2" := (mem.alloc (type.zero_val #boolT)) in
        let: "state2" := (mem.alloc (type.zero_val #ptrT)) in
        let: ("$ret0", "$ret1") := (map.get (![type.mapT #uint64T #ptrT] (struct.field_ref #lockShard #"state"%go (![#ptrT] "lmap"))) (![#uint64T] "addr")) in
        let: "$r0" := "$ret0" in
        let: "$r1" := "$ret1" in
        do:  ("state2" <-[#ptrT] "$r0");;;
        do:  ("ok2" <-[#boolT] "$r1");;;
        (if: ![#boolT] "ok2"
        then do:  ((struct.field_ref #lockState #"waiters"%go (![#ptrT] "state2")) <-[#uint64T] ((![#uint64T] (struct.field_ref #lockState #"waiters"%go (![#ptrT] "state2"))) - #(W64 1)))
        else do:  #()));;;
      (if: ![#boolT] "acquired"
      then break: #()
      else do:  #());;;
      continue: #());;;
    do:  ((method_call #sync #"Mutex'ptr" #"Unlock" (![#ptrT] (struct.field_ref #lockShard #"mu"%go (![#ptrT] "lmap")))) #());;;
    return: #()).

(* go: lock.go:81:24 *)
Definition lockShard__release : val :=
  rec: "lockShard__release" "lmap" "addr" :=
    exception_do (let: "lmap" := (mem.alloc "lmap") in
    let: "addr" := (mem.alloc "addr") in
    do:  ((method_call #sync #"Mutex'ptr" #"Lock" (![#ptrT] (struct.field_ref #lockShard #"mu"%go (![#ptrT] "lmap")))) #());;;
    let: "state" := (mem.alloc (type.zero_val #ptrT)) in
    let: "$r0" := (Fst (map.get (![type.mapT #uint64T #ptrT] (struct.field_ref #lockShard #"state"%go (![#ptrT] "lmap"))) (![#uint64T] "addr"))) in
    do:  ("state" <-[#ptrT] "$r0");;;
    let: "$r0" := #false in
    do:  ((struct.field_ref #lockState #"held"%go (![#ptrT] "state")) <-[#boolT] "$r0");;;
    (if: (![#uint64T] (struct.field_ref #lockState #"waiters"%go (![#ptrT] "state"))) > #(W64 0)
    then do:  ((method_call #sync #"Cond'ptr" #"Signal" (![#ptrT] (struct.field_ref #lockState #"cond"%go (![#ptrT] "state")))) #())
    else
      do:  (let: "$a0" := (![type.mapT #uint64T #ptrT] (struct.field_ref #lockShard #"state"%go (![#ptrT] "lmap"))) in
      let: "$a1" := (![#uint64T] "addr") in
      map.delete "$a0" "$a1"));;;
    do:  ((method_call #sync #"Mutex'ptr" #"Unlock" (![#ptrT] (struct.field_ref #lockShard #"mu"%go (![#ptrT] "lmap")))) #());;;
    return: #()).

Definition NSHARD : expr := #(W64 65537).

Definition LockMap : go_type := structT [
  "shards" :: sliceT
].

(* go: lock.go:99:6 *)
Definition MkLockMap : val :=
  rec: "MkLockMap" <> :=
    exception_do (let: "shards" := (mem.alloc (type.zero_val #sliceT)) in
    (let: "i" := (mem.alloc (type.zero_val #uint64T)) in
    let: "$r0" := #(W64 0) in
    do:  ("i" <-[#uint64T] "$r0");;;
    (for: (λ: <>, (![#uint64T] "i") < NSHARD); (λ: <>, do:  ("i" <-[#uint64T] ((![#uint64T] "i") + #(W64 1)))) := λ: <>,
      let: "$r0" := (let: "$a0" := (![#sliceT] "shards") in
      let: "$a1" := ((let: "$sl0" := ((func_call #lockmap.lockmap #"mkLockShard"%go) #()) in
      slice.literal #ptrT ["$sl0"])) in
      (slice.append #ptrT) "$a0" "$a1") in
      do:  ("shards" <-[#sliceT] "$r0")));;;
    let: "a" := (mem.alloc (type.zero_val #ptrT)) in
    let: "$r0" := (mem.alloc (let: "$shards" := (![#sliceT] "shards") in
    struct.make #LockMap [{
      "shards" ::= "$shards"
    }])) in
    do:  ("a" <-[#ptrT] "$r0");;;
    return: (![#ptrT] "a")).

(* go: lock.go:110:22 *)
Definition LockMap__Acquire : val :=
  rec: "LockMap__Acquire" "lmap" "flataddr" :=
    exception_do (let: "lmap" := (mem.alloc "lmap") in
    let: "flataddr" := (mem.alloc "flataddr") in
    let: "shard" := (mem.alloc (type.zero_val #ptrT)) in
    let: "$r0" := (![#ptrT] (slice.elem_ref #ptrT (![#sliceT] (struct.field_ref #LockMap #"shards"%go (![#ptrT] "lmap"))) ((![#uint64T] "flataddr") `rem` NSHARD))) in
    do:  ("shard" <-[#ptrT] "$r0");;;
    do:  (let: "$a0" := (![#uint64T] "flataddr") in
    (method_call #lockmap.lockmap #"lockShard'ptr" #"acquire" (![#ptrT] "shard")) "$a0");;;
    return: #()).

(* go: lock.go:115:22 *)
Definition LockMap__Release : val :=
  rec: "LockMap__Release" "lmap" "flataddr" :=
    exception_do (let: "lmap" := (mem.alloc "lmap") in
    let: "flataddr" := (mem.alloc "flataddr") in
    let: "shard" := (mem.alloc (type.zero_val #ptrT)) in
    let: "$r0" := (![#ptrT] (slice.elem_ref #ptrT (![#sliceT] (struct.field_ref #LockMap #"shards"%go (![#ptrT] "lmap"))) ((![#uint64T] "flataddr") `rem` NSHARD))) in
    do:  ("shard" <-[#ptrT] "$r0");;;
    do:  (let: "$a0" := (![#uint64T] "flataddr") in
    (method_call #lockmap.lockmap #"lockShard'ptr" #"release" (![#ptrT] "shard")) "$a0");;;
    return: #()).

Definition vars' : list (go_string * go_type) := [].

Definition functions' : list (go_string * val) := [("mkLockShard"%go, mkLockShard); ("MkLockMap"%go, MkLockMap)].

Definition msets' : list (go_string * (list (go_string * val))) := [("lockState"%go, []); ("lockState'ptr"%go, []); ("lockShard"%go, []); ("lockShard'ptr"%go, [("acquire"%go, lockShard__acquire); ("release"%go, lockShard__release)]); ("LockMap"%go, []); ("LockMap'ptr"%go, [("Acquire"%go, LockMap__Acquire); ("Release"%go, LockMap__Release)])].

#[global] Instance info' : PkgInfo lockmap.lockmap :=
  {|
    pkg_vars := vars';
    pkg_functions := functions';
    pkg_msets := msets';
    pkg_imported_pkgs := [sync.sync];
  |}.

Definition initialize' : val :=
  rec: "initialize'" <> :=
    globals.package_init lockmap.lockmap (λ: <>,
      exception_do (do:  sync.initialize')
      ).

End code.
End lockmap.
