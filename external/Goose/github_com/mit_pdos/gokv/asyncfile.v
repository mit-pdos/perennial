(* autogenerated from github.com/mit-pdos/gokv/asyncfile *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_com.goose_lang.std.

From Perennial.goose_lang Require Import ffi.grove_prelude.

Definition AsyncFile := struct.decl [
  "mu" :: ptrT;
  "data" :: slice.T byteT;
  "filename" :: stringT;
  "index" :: uint64T;
  "indexCond" :: ptrT;
  "durableIndex" :: uint64T;
  "durableIndexCond" :: ptrT;
  "closeRequested" :: boolT;
  "closed" :: boolT;
  "closedCond" :: ptrT
].

Definition AsyncFile__wait: val :=
  rec: "AsyncFile__wait" "s" "index" :=
    Mutex__Lock (struct.loadF AsyncFile "mu" "s");;
    Skip;;
    (for: (λ: <>, (struct.loadF AsyncFile "durableIndex" "s") < "index"); (λ: <>, Skip) := λ: <>,
      Cond__Wait (struct.loadF AsyncFile "durableIndexCond" "s");;
      Continue);;
    Mutex__Unlock (struct.loadF AsyncFile "mu" "s");;
    #().

Definition AsyncFile__Write: val :=
  rec: "AsyncFile__Write" "s" "data" :=
    Mutex__Lock (struct.loadF AsyncFile "mu" "s");;
    struct.storeF AsyncFile "data" "s" "data";;
    struct.storeF AsyncFile "index" "s" (std.SumAssumeNoOverflow (struct.loadF AsyncFile "index" "s") #1);;
    let: "index" := struct.loadF AsyncFile "index" "s" in
    Cond__Signal (struct.loadF AsyncFile "indexCond" "s");;
    Mutex__Unlock (struct.loadF AsyncFile "mu" "s");;
    (λ: <>,
      AsyncFile__wait "s" "index";;
      #()
      ).

Definition AsyncFile__flushThread: val :=
  rec: "AsyncFile__flushThread" "s" :=
    Mutex__Lock (struct.loadF AsyncFile "mu" "s");;
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      (if: struct.loadF AsyncFile "closeRequested" "s"
      then
        grove_ffi.FileWrite (struct.loadF AsyncFile "filename" "s") (struct.loadF AsyncFile "data" "s");;
        struct.storeF AsyncFile "durableIndex" "s" (struct.loadF AsyncFile "index" "s");;
        Cond__Broadcast (struct.loadF AsyncFile "durableIndexCond" "s");;
        struct.storeF AsyncFile "closed" "s" #true;;
        Mutex__Unlock (struct.loadF AsyncFile "mu" "s");;
        Cond__Signal (struct.loadF AsyncFile "closedCond" "s");;
        Break
      else
        (if: (struct.loadF AsyncFile "durableIndex" "s") ≥ (struct.loadF AsyncFile "index" "s")
        then
          Cond__Wait (struct.loadF AsyncFile "indexCond" "s");;
          Continue
        else
          let: "index" := struct.loadF AsyncFile "index" "s" in
          let: "data" := struct.loadF AsyncFile "data" "s" in
          Mutex__Unlock (struct.loadF AsyncFile "mu" "s");;
          grove_ffi.FileWrite (struct.loadF AsyncFile "filename" "s") "data";;
          Mutex__Lock (struct.loadF AsyncFile "mu" "s");;
          struct.storeF AsyncFile "durableIndex" "s" "index";;
          Cond__Broadcast (struct.loadF AsyncFile "durableIndexCond" "s");;
          Continue)));;
    #().

Definition AsyncFile__Close: val :=
  rec: "AsyncFile__Close" "s" :=
    Mutex__Lock (struct.loadF AsyncFile "mu" "s");;
    struct.storeF AsyncFile "closeRequested" "s" #true;;
    Cond__Signal (struct.loadF AsyncFile "indexCond" "s");;
    Skip;;
    (for: (λ: <>, (~ (struct.loadF AsyncFile "closed" "s"))); (λ: <>, Skip) := λ: <>,
      Cond__Wait (struct.loadF AsyncFile "closedCond" "s");;
      Continue);;
    Mutex__Unlock (struct.loadF AsyncFile "mu" "s");;
    #().

(* returns the state, then the File object *)
Definition MakeAsyncFile: val :=
  rec: "MakeAsyncFile" "filename" :=
    let: "s" := struct.alloc AsyncFile (zero_val (struct.t AsyncFile)) in
    struct.storeF AsyncFile "mu" "s" (newMutex #());;
    struct.storeF AsyncFile "indexCond" "s" (NewCond (struct.loadF AsyncFile "mu" "s"));;
    struct.storeF AsyncFile "durableIndexCond" "s" (NewCond (struct.loadF AsyncFile "mu" "s"));;
    struct.storeF AsyncFile "closedCond" "s" (NewCond (struct.loadF AsyncFile "mu" "s"));;
    struct.storeF AsyncFile "filename" "s" "filename";;
    struct.storeF AsyncFile "data" "s" (grove_ffi.FileRead "filename");;
    struct.storeF AsyncFile "index" "s" #0;;
    struct.storeF AsyncFile "durableIndex" "s" #0;;
    struct.storeF AsyncFile "closed" "s" #false;;
    struct.storeF AsyncFile "closeRequested" "s" #false;;
    let: "data" := struct.loadF AsyncFile "data" "s" in
    Fork (AsyncFile__flushThread "s");;
    ("data", "s").
