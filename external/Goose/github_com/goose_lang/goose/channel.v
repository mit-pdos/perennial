(* autogenerated from github.com/goose-lang/goose/channel *)
From Perennial.goose_lang Require Import base_prelude.

Section code.
Context `{ext_ty: ext_types}.

Definition ChannelState: ty := uint64T.

Definition start : expr := #0.

Definition receiver_ready : expr := #1.

Definition sender_ready : expr := #2.

Definition receiver_done : expr := #3.

Definition sender_done : expr := #4.

Definition closed : expr := #5.

Definition Channel (T: ty) : descriptor := struct.decl [
  "lock" :: ptrT;
  "state" :: ChannelState;
  "buffer" :: slice.T T;
  "first" :: uint64T;
  "count" :: uint64T;
  "v" :: T
].

(* buffer_size = 0 is an unbuffered channel *)
Definition NewChannel (T:ty): val :=
  rec: "NewChannel" "buffer_size" :=
    struct.mk (Channel T) [
      "buffer" ::= NewSlice T "buffer_size";
      "lock" ::= newMutex #();
      "first" ::= #0;
      "count" ::= #0;
      "state" ::= start
    ].

(* buffer_size = 0 is an unbuffered channel *)
Definition NewChannelRef (T:ty): val :=
  rec: "NewChannelRef" "buffer_size" :=
    struct.new (Channel T) [
      "buffer" ::= NewSlice T "buffer_size";
      "lock" ::= newMutex #();
      "first" ::= #0;
      "count" ::= #0;
      "state" ::= start
    ].

(* c.Send(val)

   is equivalent to:

   c <- val *)
Definition Channel__Send (T:ty): val :=
  rec: "Channel__Send" "c" "val" :=
    (if: "c" = #null
    then
      Skip;;
      (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
        Continue)
    else #());;
    let: "buffer_size" := ref_to uint64T (slice.len (struct.loadF (Channel T) "buffer" "c")) in
    (if: (![uint64T] "buffer_size") ≠ #0
    then
      Skip;;
      (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
        Mutex__Lock (struct.loadF (Channel T) "lock" "c");;
        (if: (struct.loadF (Channel T) "state" "c") = closed
        then Panic "send on closed channel"
        else #());;
        (if: (struct.loadF (Channel T) "count" "c") ≥ (![uint64T] "buffer_size")
        then
          Mutex__Unlock (struct.loadF (Channel T) "lock" "c");;
          Continue
        else
          let: "last" := ref_to uint64T (((struct.loadF (Channel T) "first" "c") + (struct.loadF (Channel T) "count" "c")) `rem` (![uint64T] "buffer_size")) in
          SliceSet T (struct.loadF (Channel T) "buffer" "c") (![uint64T] "last") "val";;
          struct.storeF (Channel T) "count" "c" ((struct.loadF (Channel T) "count" "c") + #1);;
          Mutex__Unlock (struct.loadF (Channel T) "lock" "c");;
          Break));;
      #()
    else
      let: "return_early" := ref_to boolT #false in
      Skip;;
      (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
        Mutex__Lock (struct.loadF (Channel T) "lock" "c");;
        (if: (struct.loadF (Channel T) "state" "c") = closed
        then Panic "send on closed channel"
        else #());;
        (if: (struct.loadF (Channel T) "state" "c") = receiver_ready
        then
          struct.storeF (Channel T) "state" "c" sender_done;;
          struct.storeF (Channel T) "v" "c" "val";;
          Mutex__Unlock (struct.loadF (Channel T) "lock" "c");;
          "return_early" <-[boolT] #true;;
          Break
        else
          (if: (struct.loadF (Channel T) "state" "c") = start
          then
            struct.storeF (Channel T) "v" "c" "val";;
            struct.storeF (Channel T) "state" "c" sender_ready;;
            Mutex__Unlock (struct.loadF (Channel T) "lock" "c");;
            Break
          else
            Mutex__Unlock (struct.loadF (Channel T) "lock" "c");;
            Continue)));;
      (if: ![boolT] "return_early"
      then
        Skip;;
        (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
          Mutex__Lock (struct.loadF (Channel T) "lock" "c");;
          (if: (~ ((struct.loadF (Channel T) "state" "c") = sender_done))
          then
            Mutex__Unlock (struct.loadF (Channel T) "lock" "c");;
            Break
          else
            Mutex__Unlock (struct.loadF (Channel T) "lock" "c");;
            Continue));;
        #()
      else
        Skip;;
        (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
          Mutex__Lock (struct.loadF (Channel T) "lock" "c");;
          (if: (struct.loadF (Channel T) "state" "c") = closed
          then Panic "send on closed channel"
          else #());;
          (if: (struct.loadF (Channel T) "state" "c") = receiver_done
          then
            struct.storeF (Channel T) "state" "c" start;;
            Mutex__Unlock (struct.loadF (Channel T) "lock" "c");;
            Break
          else
            Mutex__Unlock (struct.loadF (Channel T) "lock" "c");;
            Continue));;
        #())).

(* Equivalent to:
   value, ok := <-c
   Notably, this requires the user to consume the ok bool which is not actually required with Go
   channels. This should be able to be solved by adding an overload wrapper that discards the ok
   bool. *)
Definition Channel__Receive (T:ty): val :=
  rec: "Channel__Receive" "c" :=
    (if: "c" = #null
    then
      Skip;;
      (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
        Continue)
    else #());;
    let: "ret_val" := ref (zero_val T) in
    let: "buffer_size" := ref_to uint64T (slice.len (struct.loadF (Channel T) "buffer" "c")) in
    let: "closed_local" := ref_to boolT #false in
    (if: (![uint64T] "buffer_size") ≠ #0
    then
      Skip;;
      (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
        Mutex__Lock (struct.loadF (Channel T) "lock" "c");;
        (if: ((struct.loadF (Channel T) "state" "c") = closed) && ((struct.loadF (Channel T) "count" "c") = #0)
        then
          Mutex__Unlock (struct.loadF (Channel T) "lock" "c");;
          "closed_local" <-[boolT] #true;;
          Break
        else
          (if: (struct.loadF (Channel T) "count" "c") = #0
          then
            Mutex__Unlock (struct.loadF (Channel T) "lock" "c");;
            Continue
          else
            "ret_val" <-[T] (SliceGet T (struct.loadF (Channel T) "buffer" "c") (struct.loadF (Channel T) "first" "c"));;
            struct.storeF (Channel T) "first" "c" (((struct.loadF (Channel T) "first" "c") + #1) `rem` (![uint64T] "buffer_size"));;
            struct.storeF (Channel T) "count" "c" ((struct.loadF (Channel T) "count" "c") - #1);;
            Mutex__Unlock (struct.loadF (Channel T) "lock" "c");;
            Break)));;
      (![T] "ret_val", (~ (![boolT] "closed_local")))
    else
      let: "return_early" := ref_to boolT #false in
      Skip;;
      (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
        Mutex__Lock (struct.loadF (Channel T) "lock" "c");;
        (if: (struct.loadF (Channel T) "state" "c") = closed
        then
          Mutex__Unlock (struct.loadF (Channel T) "lock" "c");;
          "closed_local" <-[boolT] #true;;
          Break
        else
          (if: (struct.loadF (Channel T) "state" "c") = sender_ready
          then
            struct.storeF (Channel T) "state" "c" receiver_done;;
            "ret_val" <-[T] (struct.loadF (Channel T) "v" "c");;
            Mutex__Unlock (struct.loadF (Channel T) "lock" "c");;
            "return_early" <-[boolT] #true;;
            Break
          else
            (if: (struct.loadF (Channel T) "state" "c") = start
            then
              struct.storeF (Channel T) "state" "c" receiver_ready;;
              Mutex__Unlock (struct.loadF (Channel T) "lock" "c");;
              Break
            else
              Mutex__Unlock (struct.loadF (Channel T) "lock" "c");;
              Continue))));;
      (if: ![boolT] "closed_local"
      then (![T] "ret_val", (~ (![boolT] "closed_local")))
      else
        (if: ![boolT] "return_early"
        then
          Skip;;
          (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
            Mutex__Lock (struct.loadF (Channel T) "lock" "c");;
            (if: (~ ((struct.loadF (Channel T) "state" "c") = receiver_done))
            then
              Mutex__Unlock (struct.loadF (Channel T) "lock" "c");;
              Break
            else
              Mutex__Unlock (struct.loadF (Channel T) "lock" "c");;
              Continue));;
          (![T] "ret_val", (~ (![boolT] "closed_local")))
        else
          Skip;;
          (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
            Mutex__Lock (struct.loadF (Channel T) "lock" "c");;
            (if: (struct.loadF (Channel T) "state" "c") = closed
            then
              Mutex__Unlock (struct.loadF (Channel T) "lock" "c");;
              "closed_local" <-[boolT] #true;;
              Break
            else
              (if: (struct.loadF (Channel T) "state" "c") = sender_done
              then
                struct.storeF (Channel T) "state" "c" start;;
                "ret_val" <-[T] (struct.loadF (Channel T) "v" "c");;
                Mutex__Unlock (struct.loadF (Channel T) "lock" "c");;
                Break
              else
                Mutex__Unlock (struct.loadF (Channel T) "lock" "c");;
                Continue)));;
          (![T] "ret_val", (~ (![boolT] "closed_local")))))).

(* c.Close()

   is equivalent to:

   close(c) *)
Definition Channel__Close (T:ty): val :=
  rec: "Channel__Close" "c" :=
    (if: "c" = #null
    then Panic "close of nil channel"
    else #());;
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      Mutex__Lock (struct.loadF (Channel T) "lock" "c");;
      (if: (struct.loadF (Channel T) "state" "c") = closed
      then Panic "close of closed channel"
      else #());;
      (if: ((struct.loadF (Channel T) "state" "c") = receiver_done) || ((struct.loadF (Channel T) "state" "c") = sender_done)
      then
        Mutex__Unlock (struct.loadF (Channel T) "lock" "c");;
        Continue
      else
        struct.storeF (Channel T) "state" "c" closed;;
        Mutex__Unlock (struct.loadF (Channel T) "lock" "c");;
        Break));;
    #().

(* v := c.ReceiveDiscardOk

   is equivalent to:
   v := c<-
   It seems like Go requires ignored return values to be annotated with _ but channels don't
   require this so this will need to be translated. *)
Definition Channel__ReceiveDiscardOk (T:ty): val :=
  rec: "Channel__ReceiveDiscardOk" "c" :=
    let: "return_val" := ref (zero_val T) in
    let: ("0_ret", "1_ret") := Channel__Receive T "c" in
    "return_val" <-[T] "0_ret";;
    "1_ret";;
    ![T] "return_val".

(* A non-blocking receive operation. If there is not a sender available in an unbuffered channel,
   we "offer" for a single program step by setting receiver_ready to true, unlocking, then
   immediately locking, which is necessary when a potential matching party is using TrySend.
   See the various <n>CaseSelect functions for a description of how this is used to model selects. *)
Definition Channel__TryReceive (T:ty): val :=
  rec: "Channel__TryReceive" "c" :=
    let: "ret_val" := ref (zero_val T) in
    (if: "c" = #null
    then (#false, ![T] "ret_val", #false)
    else
      let: "buffer_size" := ref_to uint64T (slice.len (struct.loadF (Channel T) "buffer" "c")) in
      let: "closed_local" := ref_to boolT #false in
      let: "selected" := ref_to boolT #false in
      (if: (![uint64T] "buffer_size") ≠ #0
      then
        Mutex__Lock (struct.loadF (Channel T) "lock" "c");;
        (if: (struct.loadF (Channel T) "count" "c") = #0
        then
          (if: (struct.loadF (Channel T) "state" "c") = closed
          then
            "closed_local" <-[boolT] #true;;
            "selected" <-[boolT] #true
          else #());;
          Mutex__Unlock (struct.loadF (Channel T) "lock" "c")
        else
          "ret_val" <-[T] (SliceGet T (struct.loadF (Channel T) "buffer" "c") (struct.loadF (Channel T) "first" "c"));;
          struct.storeF (Channel T) "first" "c" (((struct.loadF (Channel T) "first" "c") + #1) `rem` (![uint64T] "buffer_size"));;
          struct.storeF (Channel T) "count" "c" ((struct.loadF (Channel T) "count" "c") - #1);;
          "selected" <-[boolT] #true;;
          Mutex__Unlock (struct.loadF (Channel T) "lock" "c"));;
        (![boolT] "selected", ![T] "ret_val", (~ (![boolT] "closed_local")))
      else
        let: "offer" := ref_to boolT #false in
        Mutex__Lock (struct.loadF (Channel T) "lock" "c");;
        (if: (struct.loadF (Channel T) "state" "c") = closed
        then
          "closed_local" <-[boolT] #true;;
          "selected" <-[boolT] #true
        else
          (if: (struct.loadF (Channel T) "state" "c") = sender_ready
          then
            struct.storeF (Channel T) "state" "c" receiver_done;;
            "ret_val" <-[T] (struct.loadF (Channel T) "v" "c");;
            "selected" <-[boolT] #true
          else #());;
          (if: (struct.loadF (Channel T) "state" "c") = start
          then
            struct.storeF (Channel T) "state" "c" receiver_ready;;
            "offer" <-[boolT] #true
          else #()));;
        Mutex__Unlock (struct.loadF (Channel T) "lock" "c");;
        (if: ![boolT] "offer"
        then
          Mutex__Lock (struct.loadF (Channel T) "lock" "c");;
          (if: (struct.loadF (Channel T) "state" "c") = sender_done
          then
            "ret_val" <-[T] (struct.loadF (Channel T) "v" "c");;
            struct.storeF (Channel T) "state" "c" start;;
            "selected" <-[boolT] #true
          else #());;
          (if: (struct.loadF (Channel T) "state" "c") = receiver_ready
          then struct.storeF (Channel T) "state" "c" start
          else #());;
          Mutex__Unlock (struct.loadF (Channel T) "lock" "c")
        else #());;
        (if: ![boolT] "closed_local"
        then (![boolT] "selected", ![T] "ret_val", (~ (![boolT] "closed_local")))
        else
          (if: (![boolT] "selected") && (~ (![boolT] "offer"))
          then
            Skip;;
            (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
              Mutex__Lock (struct.loadF (Channel T) "lock" "c");;
              (if: (~ ((struct.loadF (Channel T) "state" "c") = receiver_done))
              then
                Mutex__Unlock (struct.loadF (Channel T) "lock" "c");;
                Break
              else
                Mutex__Unlock (struct.loadF (Channel T) "lock" "c");;
                Continue))
          else #());;
          (![boolT] "selected", ![T] "ret_val", (~ (![boolT] "closed_local")))))).

(* A non-blocking send operation. If there is not a receiver available in an unbuffered channel,
   we "offer" for a single program step by setting sender_ready to true, unlocking, then
   immediately locking, which is necessary when a potential matching party is using TryReceive.
   See the various <n>CaseSelect functions for a description of how this is used to model selects. *)
Definition Channel__TrySend (T:ty): val :=
  rec: "Channel__TrySend" "c" "val" :=
    (if: "c" = #null
    then #false
    else
      let: "selected" := ref_to boolT #false in
      let: "buffer_size" := ref_to uint64T (slice.len (struct.loadF (Channel T) "buffer" "c")) in
      (if: (![uint64T] "buffer_size") ≠ #0
      then
        Mutex__Lock (struct.loadF (Channel T) "lock" "c");;
        (if: (struct.loadF (Channel T) "state" "c") = closed
        then Panic "send on closed channel"
        else #());;
        (if: (~ ((struct.loadF (Channel T) "count" "c") ≥ (![uint64T] "buffer_size")))
        then
          let: "last" := ref_to uint64T (((struct.loadF (Channel T) "first" "c") + (struct.loadF (Channel T) "count" "c")) `rem` (![uint64T] "buffer_size")) in
          SliceSet T (struct.loadF (Channel T) "buffer" "c") (![uint64T] "last") "val";;
          struct.storeF (Channel T) "count" "c" ((struct.loadF (Channel T) "count" "c") + #1);;
          "selected" <-[boolT] #true
        else #());;
        Mutex__Unlock (struct.loadF (Channel T) "lock" "c");;
        ![boolT] "selected"
      else
        let: "offer" := ref_to boolT #false in
        Mutex__Lock (struct.loadF (Channel T) "lock" "c");;
        (if: (struct.loadF (Channel T) "state" "c") = closed
        then Panic "send on closed channel"
        else #());;
        (if: (struct.loadF (Channel T) "state" "c") = receiver_ready
        then
          struct.storeF (Channel T) "state" "c" sender_done;;
          struct.storeF (Channel T) "v" "c" "val";;
          "selected" <-[boolT] #true
        else #());;
        (if: (struct.loadF (Channel T) "state" "c") = start
        then
          struct.storeF (Channel T) "state" "c" sender_ready;;
          struct.storeF (Channel T) "v" "c" "val";;
          "offer" <-[boolT] #true
        else #());;
        Mutex__Unlock (struct.loadF (Channel T) "lock" "c");;
        (if: ![boolT] "offer"
        then
          Mutex__Lock (struct.loadF (Channel T) "lock" "c");;
          (if: (struct.loadF (Channel T) "state" "c") = receiver_done
          then
            struct.storeF (Channel T) "state" "c" start;;
            "selected" <-[boolT] #true
          else #());;
          (if: (struct.loadF (Channel T) "state" "c") = sender_ready
          then struct.storeF (Channel T) "state" "c" start
          else #());;
          Mutex__Unlock (struct.loadF (Channel T) "lock" "c")
        else #());;
        (if: (![boolT] "selected") && (~ (![boolT] "offer"))
        then
          Skip;;
          (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
            Mutex__Lock (struct.loadF (Channel T) "lock" "c");;
            (if: (~ ((struct.loadF (Channel T) "state" "c") = sender_done))
            then
              Mutex__Unlock (struct.loadF (Channel T) "lock" "c");;
              Break
            else
              Mutex__Unlock (struct.loadF (Channel T) "lock" "c");;
              Continue))
        else #());;
        ![boolT] "selected")).

(* c.Len()

   is equivalent to:
   len(c)

   This might not be worth specifying since it is hard to make good use of channel length
   semantics. *)
Definition Channel__Len (T:ty): val :=
  rec: "Channel__Len" "c" :=
    (if: "c" = #null
    then #0
    else
      let: "chan_len" := ref_to uint64T #0 in
      Mutex__Lock (struct.loadF (Channel T) "lock" "c");;
      "chan_len" <-[uint64T] (struct.loadF (Channel T) "count" "c");;
      Mutex__Unlock (struct.loadF (Channel T) "lock" "c");;
      ![uint64T] "chan_len").

(* c.Cap()

   is equivalent to:
   cap(c) *)
Definition Channel__Cap (T:ty): val :=
  rec: "Channel__Cap" "c" :=
    (if: "c" = #null
    then #0
    else slice.len (struct.loadF (Channel T) "buffer" "c")).

Definition SelectDir: ty := uint64T.

(* case Chan <- Send *)
Definition SelectSend : expr := #0.

(* case <-Chan: *)
Definition SelectRecv : expr := #1.

(* default *)
Definition SelectDefault : expr := #2.

(* value is used for the value the sender will send and also used to return the received value by
   reference. *)
Definition SelectCase (T: ty) : descriptor := struct.decl [
  "channel" :: ptrT;
  "dir" :: SelectDir;
  "Value" :: T;
  "Ok" :: boolT
].

(* Simple knuth shuffle. *)
Definition Shuffle: val :=
  rec: "Shuffle" "n" :=
    let: "order" := ref_to (slice.T uint64T) (NewSlice uint64T "n") in
    let: "i" := ref_to uint64T #0 in
    (for: (λ: <>, (![uint64T] "i") < "n"); (λ: <>, "i" <-[uint64T] ((![uint64T] "i") + #1)) := λ: <>,
      SliceSet uint64T (![slice.T uint64T] "order") (![uint64T] "i") (![uint64T] "i");;
      Continue);;
    let: "i" := ref_to uint64T ((slice.len (![slice.T uint64T] "order")) - #1) in
    (for: (λ: <>, (![uint64T] "i") > #0); (λ: <>, "i" <-[uint64T] ((![uint64T] "i") - #1)) := λ: <>,
      let: "j" := ref_to uint64T ((rand.RandomUint64 #()) `rem` ((![uint64T] "i") + #1)) in
      let: "temp" := ref_to uint64T (SliceGet uint64T (![slice.T uint64T] "order") (![uint64T] "i")) in
      SliceSet uint64T (![slice.T uint64T] "order") (![uint64T] "i") (SliceGet uint64T (![slice.T uint64T] "order") (![uint64T] "j"));;
      SliceSet uint64T (![slice.T uint64T] "order") (![uint64T] "j") (![uint64T] "temp");;
      Continue);;
    ![slice.T uint64T] "order".

(* Uses the applicable Try<Operation> function on the select case's channel. Default is always
   selectable so simply returns true. *)
Definition TrySelect (T:ty): val :=
  rec: "TrySelect" "select_case" :=
    let: "channel" := ref_to ptrT (struct.loadF (SelectCase T) "channel" "select_case") in
    (if: (struct.loadF (SelectCase T) "dir" "select_case") = SelectSend
    then Channel__TrySend T (![ptrT] "channel") (struct.loadF (SelectCase T) "Value" "select_case")
    else
      (if: (struct.loadF (SelectCase T) "dir" "select_case") = SelectRecv
      then
        let: "item" := ref (zero_val T) in
        let: "ok" := ref (zero_val boolT) in
        let: "selected" := ref (zero_val boolT) in
        let: (("0_ret", "1_ret"), "2_ret") := Channel__TryReceive T (![ptrT] "channel") in
        "selected" <-[boolT] "0_ret";;
        "item" <-[T] "1_ret";;
        "ok" <-[boolT] "2_ret";;
        struct.storeF (SelectCase T) "Value" "select_case" (![T] "item");;
        struct.storeF (SelectCase T) "Ok" "select_case" (![boolT] "ok");;
        ![boolT] "selected"
      else
        (if: (struct.loadF (SelectCase T) "dir" "select_case") = SelectDefault
        then #true
        else #false))).

(* Models a 2 case select statement. Returns 0 if case 1 selected, 1 if case 2 selected.
   Requires that case 1 not have dir = SelectDefault. If case_2 is a default, this will never block.
   This is similar to the reflect package dynamic select statements and should give us a true to
   runtime Go model with a fairly intuitive spec/translation.

   	This:
   	select {
   		case c1 <- 0:
   			<case 1 body>
   		case v, ok := <-c2:
   			<case 2 body>
   	}

   	Will be translated to:

   case_1 := channel.NewSendCase(c1, 0)
   case_2 := channel.NewRecvCase(c2)
   var uint64 selected_case = TwoCaseSelect(case_1, case_2)

   	if selected_case == 0 {
   		<case 1 body>
   	}
   	if selected_case == 1 {
   			var ok bool = case_2.ok
   			var v uint64 = case_2.value
   			<case 2 body>
   		} *)
Definition TwoCaseSelect (T1:ty) (T2:ty): val :=
  rec: "TwoCaseSelect" "case_1" "case_2" :=
    let: "selected_case" := ref_to uint64T #0 in
    let: "selected" := ref_to boolT #false in
    let: "order" := ref_to (slice.T uint64T) (Shuffle #2) in
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      ForSlice uint64T <> "i" (![slice.T uint64T] "order")
        ((if: ("i" = #0) && (~ (![boolT] "selected"))
        then
          "selected" <-[boolT] (TrySelect T1 "case_1");;
          (if: ![boolT] "selected"
          then "selected_case" <-[uint64T] #0
          else #())
        else #());;
        (if: (("i" = #1) && (~ (![boolT] "selected"))) && ((struct.loadF (SelectCase T2) "dir" "case_2") ≠ SelectDefault)
        then
          "selected" <-[boolT] (TrySelect T2 "case_2");;
          (if: ![boolT] "selected"
          then "selected_case" <-[uint64T] #1
          else #())
        else #()));;
      (if: (~ (![boolT] "selected")) && ((struct.loadF (SelectCase T2) "dir" "case_2") = SelectDefault)
      then Break
      else
        (if: ![boolT] "selected"
        then Break
        else Continue)));;
    ![uint64T] "selected_case".

Definition ThreeCaseSelect (T1:ty) (T2:ty) (T3:ty): val :=
  rec: "ThreeCaseSelect" "case_1" "case_2" "case_3" :=
    let: "selected_case" := ref_to uint64T #0 in
    let: "selected" := ref_to boolT #false in
    let: "order" := ref_to (slice.T uint64T) (Shuffle #3) in
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      ForSlice uint64T <> "i" (![slice.T uint64T] "order")
        ((if: ("i" = #0) && (~ (![boolT] "selected"))
        then
          "selected" <-[boolT] (TrySelect T1 "case_1");;
          (if: ![boolT] "selected"
          then "selected_case" <-[uint64T] #0
          else #())
        else #());;
        (if: ("i" = #1) && (~ (![boolT] "selected"))
        then
          "selected" <-[boolT] (TrySelect T2 "case_2");;
          (if: ![boolT] "selected"
          then "selected_case" <-[uint64T] #1
          else #())
        else #());;
        (if: (("i" = #2) && (~ (![boolT] "selected"))) && ((struct.loadF (SelectCase T3) "dir" "case_3") ≠ SelectDefault)
        then
          "selected" <-[boolT] (TrySelect T3 "case_3");;
          (if: ![boolT] "selected"
          then "selected_case" <-[uint64T] #2
          else #())
        else #()));;
      (if: (~ (![boolT] "selected")) && ((struct.loadF (SelectCase T3) "dir" "case_3") = SelectDefault)
      then Break
      else
        (if: ![boolT] "selected"
        then Break
        else Continue)));;
    ![uint64T] "selected_case".

Definition NewSendCase (T:ty): val :=
  rec: "NewSendCase" "channel" "value" :=
    struct.mk (SelectCase T) [
      "channel" ::= "channel";
      "dir" ::= SelectSend;
      "Value" ::= "value"
    ].

Definition NewRecvCase (T:ty): val :=
  rec: "NewRecvCase" "channel" :=
    struct.mk (SelectCase T) [
      "channel" ::= "channel";
      "dir" ::= SelectRecv
    ].

(* The type does not matter here, picking a simple primitive. *)
Definition NewDefaultCase: val :=
  rec: "NewDefaultCase" <> :=
    struct.mk (SelectCase uint64T) [
      "dir" ::= SelectDefault
    ].

End code.
