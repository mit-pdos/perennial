(* autogenerated from github.com/mit-pdos/rsm/spaxos *)
From Perennial.goose_lang Require Import prelude.

Section code.
Context `{ext_ty: ext_types}.
Local Coercion Var' s: expr := Var s.

Definition Paxos := struct.decl [
  "mu" :: ptrT;
  "termc" :: uint64T;
  "termp" :: uint64T;
  "decree" :: stringT;
  "learned" :: boolT;
  "peers" :: slice.T ptrT
].

Definition Paxos__proceedToNewTerm: val :=
  rec: "Paxos__proceedToNewTerm" "px" :=
    #0.

(* {{{ is_paxos(px, id) }}} *)
Definition Paxos__prepare: val :=
  rec: "Paxos__prepare" "px" "term" :=
    (#0, #(str""), #false).

Definition Paxos__major: val :=
  rec: "Paxos__major" "px" "n" :=
    "n" > ((slice.len (struct.loadF Paxos "peers" "px")) `quot` #2).

Definition Paxos__prepareAll: val :=
  rec: "Paxos__prepareAll" "px" "term" :=
    let: "termLargest" := ref (zero_val uint64T) in
    let: "decreeLargest" := ref (zero_val stringT) in
    let: "nPrepared" := ref (zero_val uint64T) in
    ForSlice ptrT <> "peer" (struct.loadF Paxos "peers" "px")
      (let: (("termPeer", "decreePeer"), "ok") := Paxos__prepare "peer" "term" in
      (if: "ok"
      then
        "nPrepared" <-[uint64T] ((![uint64T] "nPrepared") + #1);;
        (if: "termPeer" > (![uint64T] "termLargest")
        then
          "termLargest" <-[uint64T] "termPeer";;
          "decreeLargest" <-[stringT] "decreePeer"
        else #())
      else #()));;
    (if: (~ (Paxos__major "px" (![uint64T] "nPrepared")))
    then (#0, #(str""), #false)
    else (![uint64T] "termLargest", ![stringT] "decreeLargest", #true)).

(* {{{ is_paxos(px, id) \ast
       \E Q. [\ast set] id \in Q. \E ledger. own_ledger_lb(id, ledger) /\ length(ledger) >= term
   TODO: the `decree` we're proposing here is the one with largest-term accepted by the quorum;
   if no such proposal, then we get to use our value (i.e., the parameter of @Propose).
   }}}
   (Ignoring the case where every node in the quorum has not accepted a
   proposal, in which case the proposer can choose any value.) *)
Definition Paxos__accept: val :=
  rec: "Paxos__accept" "px" "term" "decree" :=
    #false.

Definition Paxos__acceptAll: val :=
  rec: "Paxos__acceptAll" "px" "term" "decree" :=
    let: "nAccepted" := ref_to uint64T #0 in
    ForSlice ptrT <> "peer" (struct.loadF Paxos "peers" "px")
      (let: "ok" := Paxos__accept "peer" "term" "decree" in
      (if: "ok"
      then "nAccepted" <-[uint64T] ((![uint64T] "nAccepted") + #1)
      else #()));;
    Paxos__major "px" (![uint64T] "nAccepted").

(* TODO: We probably don't need @term, but the inv might look simpler.
   {{{ is_paxos(px, id) \ast \E n. own_oneshot(shot(n)) }}} *)
Definition Paxos__learn: val :=
  rec: "Paxos__learn" "px" "term" "decree" :=
    lock.acquire (struct.loadF Paxos "mu" "px");;
    struct.storeF Paxos "termp" "px" "term";;
    struct.storeF Paxos "decree" "px" "decree";;
    struct.storeF Paxos "learned" "px" #true;;
    lock.release (struct.loadF Paxos "mu" "px");;
    #().

Definition Paxos__learnAll: val :=
  rec: "Paxos__learnAll" "px" "term" "decree" :=
    ForSlice ptrT <> "peer" (struct.loadF Paxos "peers" "px")
      (Paxos__learn "peer" "term" "decree");;
    #().

(* Note that @Propose returning true doesn't mean that @v is chosen, but only
   that @v is successfully proposed. Call @Outcome to know the actual chosen
   value.

   We could prove a stronger spec that says:
   (Case chosen) @v is successfully chosen.
   (Case proposed) @v is successfully proposed.
   (Case not proposed) @v is not proposed.
   For now it's unclear this stronger spec is useful, so we're proving a spec
   where the successful case essentially merge the first two cases above. *)
Definition Paxos__Propose: val :=
  rec: "Paxos__Propose" "px" "v" :=
    lock.acquire (struct.loadF Paxos "mu" "px");;
    let: "term" := Paxos__proceedToNewTerm "px" in
    let: (("termLargest", "decreeLargest"), "prepared") := Paxos__prepareAll "px" "term" in
    (if: (~ "prepared")
    then
      lock.release (struct.loadF Paxos "mu" "px");;
      #false
    else
      let: "decree" := ref (zero_val stringT) in
      let: "helping" := ref (zero_val boolT) in
      (if: "termLargest" = #0
      then
        "decree" <-[stringT] "v";;
        "helping" <-[boolT] #false
      else
        "decree" <-[stringT] "decreeLargest";;
        "helping" <-[boolT] #true);;
      let: "accepted" := Paxos__acceptAll "px" "term" (![stringT] "decree") in
      (if: (~ "accepted")
      then
        lock.release (struct.loadF Paxos "mu" "px");;
        #false
      else
        Paxos__learnAll "px" "term" (![stringT] "decree");;
        lock.release (struct.loadF Paxos "mu" "px");;
        (if: ![boolT] "helping"
        then #false
        else #true))).

Definition Paxos__isLearned: val :=
  rec: "Paxos__isLearned" "px" :=
    lock.acquire (struct.loadF Paxos "mu" "px");;
    let: "learned" := struct.loadF Paxos "learned" "px" in
    lock.release (struct.loadF Paxos "mu" "px");;
    "learned".

Definition Paxos__getDecree: val :=
  rec: "Paxos__getDecree" "px" :=
    lock.acquire (struct.loadF Paxos "mu" "px");;
    let: "decree" := struct.loadF Paxos "decree" "px" in
    lock.release (struct.loadF Paxos "mu" "px");;
    "decree".

Definition Paxos__Outcome: val :=
  rec: "Paxos__Outcome" "px" :=
    lock.acquire (struct.loadF Paxos "mu" "px");;
    (if: Paxos__isLearned "px"
    then
      lock.release (struct.loadF Paxos "mu" "px");;
      (Paxos__getDecree "px", #true)
    else
      lock.release (struct.loadF Paxos "mu" "px");;
      (#(str""), #false)).

Definition Paxos__isProposalAtTerm: val :=
  rec: "Paxos__isProposalAtTerm" "px" "term" :=
    lock.acquire (struct.loadF Paxos "mu" "px");;
    let: "ok" := (struct.loadF Paxos "termp" "px") = "term" in
    lock.release (struct.loadF Paxos "mu" "px");;
    "ok".

End code.