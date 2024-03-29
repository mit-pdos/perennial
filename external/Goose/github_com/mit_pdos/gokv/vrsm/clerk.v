(* autogenerated from github.com/mit-pdos/gokv/vrsm/clerk *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_com.mit_pdos.gokv.vrsm.configservice.
From Goose Require github_com.mit_pdos.gokv.vrsm.e.
From Goose Require github_com.mit_pdos.gokv.vrsm.replica.
From Perennial.goose_lang.trusted Require Import github_com.mit_pdos.gokv.trusted_proph.

From Perennial.goose_lang Require Import ffi.grove_prelude.

(* 1 second *)
Definition PreferenceRefreshTime : expr := #1000000000.

Definition Clerk := struct.decl [
  "confCk" :: ptrT;
  "replicaClerks" :: slice.T ptrT;
  "preferredReplica" :: uint64T;
  "lastPreferenceRefresh" :: uint64T
].

Definition makeClerks: val :=
  rec: "makeClerks" "servers" :=
    let: "clerks" := NewSlice ptrT (slice.len "servers") in
    let: "i" := ref_to uint64T #0 in
    Skip;;
    (for: (λ: <>, (![uint64T] "i") < (slice.len "clerks")); (λ: <>, Skip) := λ: <>,
      SliceSet ptrT "clerks" (![uint64T] "i") (replica.MakeClerk (SliceGet uint64T "servers" (![uint64T] "i")));;
      "i" <-[uint64T] ((![uint64T] "i") + #1);;
      Continue);;
    "clerks".

Definition Make: val :=
  rec: "Make" "confHosts" :=
    let: "ck" := struct.alloc Clerk (zero_val (struct.t Clerk)) in
    struct.storeF Clerk "confCk" "ck" (configservice.MakeClerk "confHosts");;
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      let: "config" := configservice.Clerk__GetConfig (struct.loadF Clerk "confCk" "ck") in
      (if: (slice.len "config") = #0
      then Continue
      else
        struct.storeF Clerk "replicaClerks" "ck" (makeClerks "config");;
        Break));;
    struct.storeF Clerk "preferredReplica" "ck" ((rand.RandomUint64 #()) `rem` (slice.len (struct.loadF Clerk "replicaClerks" "ck")));;
    let: ("0_ret", "1_ret") := grove_ffi.GetTimeRange #() in
    struct.storeF Clerk "lastPreferenceRefresh" "ck" "0_ret";;
    "1_ret";;
    "ck".

(* will retry forever *)
Definition Clerk__Apply: val :=
  rec: "Clerk__Apply" "ck" "op" :=
    let: "ret" := ref (zero_val (slice.T byteT)) in
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      let: "err" := ref (zero_val uint64T) in
      let: ("0_ret", "1_ret") := replica.Clerk__Apply (SliceGet ptrT (struct.loadF Clerk "replicaClerks" "ck") #0) "op" in
      "err" <-[uint64T] "0_ret";;
      "ret" <-[slice.T byteT] "1_ret";;
      (if: (![uint64T] "err") = e.None
      then Break
      else
        time.Sleep (#100 * #1000000);;
        let: "config" := configservice.Clerk__GetConfig (struct.loadF Clerk "confCk" "ck") in
        (if: (slice.len "config") > #0
        then struct.storeF Clerk "replicaClerks" "ck" (makeClerks "config")
        else #());;
        Continue));;
    ![slice.T byteT] "ret".

Definition Clerk__maybeRefreshPreference: val :=
  rec: "Clerk__maybeRefreshPreference" "ck" :=
    let: ("now", <>) := grove_ffi.GetTimeRange #() in
    (if: "now" > ((struct.loadF Clerk "lastPreferenceRefresh" "ck") + PreferenceRefreshTime)
    then
      struct.storeF Clerk "preferredReplica" "ck" ((rand.RandomUint64 #()) `rem` (slice.len (struct.loadF Clerk "replicaClerks" "ck")));;
      let: ("0_ret", "1_ret") := grove_ffi.GetTimeRange #() in
      struct.storeF Clerk "lastPreferenceRefresh" "ck" "0_ret";;
      "1_ret";;
      #()
    else #()).

Definition Clerk__ApplyRo2: val :=
  rec: "Clerk__ApplyRo2" "ck" "op" :=
    let: "ret" := ref (zero_val (slice.T byteT)) in
    Clerk__maybeRefreshPreference "ck";;
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      let: "offset" := struct.loadF Clerk "preferredReplica" "ck" in
      let: "err" := ref (zero_val uint64T) in
      let: "i" := ref (zero_val uint64T) in
      Skip;;
      (for: (λ: <>, (![uint64T] "i") < (slice.len (struct.loadF Clerk "replicaClerks" "ck"))); (λ: <>, Skip) := λ: <>,
        let: "k" := ((![uint64T] "i") + "offset") `rem` (slice.len (struct.loadF Clerk "replicaClerks" "ck")) in
        let: ("0_ret", "1_ret") := replica.Clerk__ApplyRo (SliceGet ptrT (struct.loadF Clerk "replicaClerks" "ck") "k") "op" in
        "err" <-[uint64T] "0_ret";;
        "ret" <-[slice.T byteT] "1_ret";;
        (if: (![uint64T] "err") = e.None
        then
          struct.storeF Clerk "preferredReplica" "ck" "k";;
          Break
        else
          "i" <-[uint64T] ((![uint64T] "i") + #1);;
          let: ("0_ret", "1_ret") := grove_ffi.GetTimeRange #() in
          struct.storeF Clerk "lastPreferenceRefresh" "ck" "0_ret";;
          "1_ret";;
          Continue));;
      (if: (![uint64T] "err") = e.None
      then Break
      else
        let: "timeToSleep" := #5 + ((rand.RandomUint64 #()) `rem` #10) in
        time.Sleep ("timeToSleep" * #1000000);;
        let: "config" := configservice.Clerk__GetConfig (struct.loadF Clerk "confCk" "ck") in
        (if: (slice.len "config") > #0
        then
          struct.storeF Clerk "replicaClerks" "ck" (makeClerks "config");;
          let: ("0_ret", "1_ret") := grove_ffi.GetTimeRange #() in
          struct.storeF Clerk "lastPreferenceRefresh" "ck" "0_ret";;
          "1_ret";;
          struct.storeF Clerk "preferredReplica" "ck" ((rand.RandomUint64 #()) `rem` (slice.len (struct.loadF Clerk "replicaClerks" "ck")))
        else #());;
        Continue));;
    ![slice.T byteT] "ret".

Definition Clerk__ApplyRo: val :=
  rec: "Clerk__ApplyRo" "ck" "op" :=
    let: "p" := trusted_proph.NewProph #() in
    let: "v" := Clerk__ApplyRo2 "ck" "op" in
    trusted_proph.ResolveBytes "p" "v";;
    "v".
