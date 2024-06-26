(* autogenerated from github.com/mit-pdos/gokv/etcd/election *)
From Perennial.goose_lang Require Import prelude.

Section code.
Context `{ext_ty: ext_types}.
Local Coercion Var' s: expr := Var s.

Definition Election := struct.decl [
  "lease" :: stringT;
  "keyPrefix" :: stringT;
  "leaderLease" :: stringT;
  "leaderKey" :: stringT;
  "leaderRev" :: uint64T
].

Notation Error := uint64T.

Definition ErrNone : expr := #0.

Definition ErrElectionNotLeader : expr := #1.

Definition Txn := struct.decl [
].

Definition Op := struct.decl [
].

Definition OpGet: val :=
  rec: "OpGet" "key" :=
    Panic "axiom";;
    #().

Definition OpPutWithLease: val :=
  rec: "OpPutWithLease" "key" "val" "lease" :=
    Panic "axiom";;
    #().

Definition OpDelete: val :=
  rec: "OpDelete" "key" :=
    Panic "axiom";;
    #().

Definition StartTxn: val :=
  rec: "StartTxn" <> :=
    Panic "axiom";;
    #().

Definition Txn__IfCreateRevisionEq: val :=
  rec: "Txn__IfCreateRevisionEq" "txn" "k" "ver" :=
    Panic "axiom";;
    #().

Definition Txn__Then: val :=
  rec: "Txn__Then" "txn" "" :=
    Panic "axiom";;
    #().

Definition Txn__Else: val :=
  rec: "Txn__Else" "txn" "" :=
    Panic "axiom";;
    #().

Definition ResponseHeader := struct.decl [
  "Revision" :: uint64T
].

Definition KeyValue := struct.decl [
  "Key" :: stringT;
  "Value" :: stringT;
  "CreateRevision" :: uint64T
].

Definition RangeResponse := struct.decl [
  "Kvs" :: slice.T ptrT
].

Notation ResponseOp := (struct.t RangeResponse).

Definition TxnResponse := struct.decl [
  "Succeeded" :: boolT;
  "Header" :: ptrT;
  "Responses" :: slice.T ptrT
].

Definition Txn__Commit: val :=
  rec: "Txn__Commit" "txn" :=
    Panic "axiom";;
    #().

Definition waitDeletes: val :=
  rec: "waitDeletes" "pfx" "rev" :=
    Panic "axiom";;
    #().

(* Proclaim lets the leader announce a new value without another election. *)
Definition Election__Proclaim: val :=
  rec: "Election__Proclaim" "e" "val" :=
    (if: (struct.loadF Election "leaderLease" "e") = #(str"")
    then ErrElectionNotLeader
    else
      let: "txn" := ref_to ptrT (Txn__IfCreateRevisionEq (StartTxn #()) (struct.loadF Election "leaderKey" "e") (struct.loadF Election "leaderRev" "e")) in
      "txn" <-[ptrT] (Txn__Then (![ptrT] "txn") (OpPutWithLease (struct.loadF Election "leaderKey" "e") "val" (struct.loadF Election "leaderLease" "e")));;
      let: ("tresp", "terr") := Txn__Commit (![ptrT] "txn") in
      (if: "terr" ≠ ErrNone
      then "terr"
      else
        (if: (~ (struct.loadF TxnResponse "Succeeded" "tresp"))
        then
          struct.storeF Election "leaderKey" "e" #(str"");;
          ErrElectionNotLeader
        else ErrNone))).

(* Resign lets a leader start a new election. *)
Definition Election__Resign: val :=
  rec: "Election__Resign" "e" :=
    (if: (struct.loadF Election "leaderLease" "e") = #(str"")
    then ErrNone
    else
      let: (<>, "err") := Txn__Commit (Txn__Then (Txn__IfCreateRevisionEq (StartTxn #()) (struct.loadF Election "leaderKey" "e") (struct.loadF Election "leaderRev" "e")) (OpDelete (struct.loadF Election "leaderKey" "e"))) in
      struct.storeF Election "leaderKey" "e" #(str"");;
      struct.storeF Election "leaderLease" "e" #(str"");;
      "err").

Definition Election__Campaign: val :=
  rec: "Election__Campaign" "e" "val" :=
    let: "l" := struct.loadF Election "lease" "e" in
    let: "k" := (struct.loadF Election "keyPrefix" "e") + "l" in
    let: "txn" := ref_to ptrT (Txn__IfCreateRevisionEq (StartTxn #()) "k" #0) in
    "txn" <-[ptrT] (Txn__Then (![ptrT] "txn") (OpPutWithLease "k" "val" (struct.loadF Election "lease" "e")));;
    "txn" <-[ptrT] (Txn__Else (![ptrT] "txn") (OpGet "k"));;
    let: "resp" := ref (zero_val ptrT) in
    let: "err" := ref (zero_val uint64T) in
    let: ("0_ret", "1_ret") := Txn__Commit (![ptrT] "txn") in
    "resp" <-[ptrT] "0_ret";;
    "err" <-[uint64T] "1_ret";;
    (if: (![uint64T] "err") ≠ ErrNone
    then ![uint64T] "err"
    else
      struct.storeF Election "leaderKey" "e" "k";;
      struct.storeF Election "leaderRev" "e" (struct.loadF ResponseHeader "Revision" (struct.loadF TxnResponse "Header" (![ptrT] "resp")));;
      struct.storeF Election "leaderLease" "e" "l";;
      let: "done" := ref_to boolT #false in
      (if: (~ (struct.loadF TxnResponse "Succeeded" (![ptrT] "resp")))
      then
        let: "kv" := SliceGet ptrT (struct.loadF RangeResponse "Kvs" (SliceGet ptrT (struct.loadF TxnResponse "Responses" (![ptrT] "resp")) #0)) #0 in
        struct.storeF Election "leaderRev" "e" (struct.loadF KeyValue "CreateRevision" "kv");;
        (if: (struct.loadF KeyValue "Value" "kv") ≠ "val"
        then
          "err" <-[uint64T] (Election__Proclaim "e" "val");;
          (if: (![uint64T] "err") ≠ ErrNone
          then
            Election__Resign "e";;
            "done" <-[boolT] #true
          else #())
        else #())
      else #());;
      (if: ![boolT] "done"
      then ![uint64T] "err"
      else
        "err" <-[uint64T] (waitDeletes (struct.loadF Election "keyPrefix" "e") ((struct.loadF Election "leaderRev" "e") - #1));;
        (if: (![uint64T] "err") ≠ ErrNone
        then #()
        else #());;
        ErrNone)).

End code.
