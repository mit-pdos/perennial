From Perennial.Helpers Require Import List ModArith.
 
 From Goose.github_com.goose_lang.goose Require Import channel.
 
 From iris.algebra Require Import excl gset.
 From Perennial.algebra Require Import ghost_var.
 From Perennial.goose_lang.lib Require Import typed_slice.
 From Perennial.goose_lang Require Import notation typing.
 From Perennial.goose_lang Require Import proofmode wpc_proofmode.
 From Perennial.goose_lang.lib Require Import typed_mem.
 From Perennial.goose_lang.automation Require Import extra_tactics.
 From Perennial.goose_lang Require Import prelude. 
 From Perennial.goose_lang.lib Require Export
      persistent_readonly slice slice.typed_slice struct loop lock control map.typed_map time proph rand string.
 From Perennial.goose_lang Require Export proofmode wpc_proofmode array.
 From Perennial.goose_lang Require Export into_val.
 From Perennial.program_proof Require Import std_proof. 
 
 Context `{hG: heapGS Σ, !ffi_semantics _ _, !ext_types _}.
 Context `{ghost_varG0: ghost_varG Σ nat}.
 
 Implicit Types (v:val).
 
 Open Scope Z_scope.
 
 Section UnbufferedChannel.
 Context `{ghost_varG1: ghost_varG Σ (list (iProp Σ))}.
 Context `{ghost_varG2: ghost_varG Σ (list val)}.
 Context `{ghost_varG3: ghost_varG Σ bool}.
 
 Definition closeable
      (state: nat) (index: nat) (num_uses: nat): bool :=
     bool_decide (state = 0%nat ∧ state = 3%nat ∧ state = 4%nat )
      .
 Definition closed
      (state: nat): bool :=
     bool_decide (state = 5%nat ∧ state = 6%nat ∧ state = 7%nat)
      .
 
 (* R is the proposition that the sender must prove to close the channel.
 The receiver can gain this proposition on the first receive after close only
 since it will not block and return the null value each time after.
 The lists Ps, Qs, and Vs denote the sender/receiver propositions and values 
 respectively that will be used to pass messages/ownership between channel 
 endpoints. num_uses is the number of times we will send/receive on the channel.
 If num_uses is greater than the size of any of the 3 lists, then the default
 values of True/0 will be required. This means that we can use only one aspect
 of these specs gracefully but also demands that the user sends the default
 value of 0 if they only intend to use the channel for synchronization, which 
 I think is a reasonable style point anyway. *)
 Definition is_UnbufferedChannel (l: loc) 
 (Ps: list (iProp Σ)) (Qs: list (iProp Σ)) (Vs: list val) (R: iProp Σ) (num_uses: nat) (chan_type: ty)
  γs γr γ1 γ2 γ3 γ4 γ5: iProp _ :=
   ∃ (mu_l: loc) ,
   "#mu" ∷ l ↦[(Channel chan_type) :: "lock"]□ #mu_l ∗ 
   "#Hlock" ∷ is_lock (nroot .@ "Channel") (#mu_l)
      (∃ (state: nat) (closeable_b: bool) (close_prop_ready_b: bool) (own_val: dfrac) (value: val)
      (index: nat), 
     (* List of props that the sender must prove each time it sends. *)
     "HPs" ∷ ghost_var γ1 (DfracOwn (1/2)) Ps ∗
     (* List of props that the receiver must prove each time it sends. *)
     "HQs" ∷ ghost_var γ2 (DfracOwn (1/2)) Qs ∗
     (* List of values that the sender must send. *)
     "HVs" ∷ ghost_var γ3 (DfracOwn (1/2)) Vs  ∗
     (* Whether the channel can be closed. This gets set to true persistently 
     after all sends and receives have completed. *)
     "HCloseableGhostVar"  ∷ ghost_var γ4 own_val closeable_b  ∗
     (* When true, the receiver has not yet consumed the proposition that can be 
     gained on the first receive after a close *)
     "HReceiverClosedProp" ∷  ghost_var γ5 (DfracOwn (1/2)) close_prop_ready_b ∗  
     (* This is somewhat obvious since we can only close when the index 
     is maxed out but having a prop here makes it easy to destruct whether
     we are in the final state or not when all of the ready/done booleans
     are false *)
     "%HMaxIndex" ∷ ⌜ index ≤ num_uses ⌝ ∗ 
     (* When all booleans are false and index is maxed out, we know we will not 
     send any more values. Closeable becomes persistent at this point so that we 
     don't try to reuse the channel. *)
     "HCloseable"  ∷ 
     (if (closeable state index num_uses )
     then 
     ( "%HCloseableTrue" ∷ ⌜ closeable_b = true ∧ own_val = DfracDiscarded ⌝)
     else 
      ( "%HCloseableFalse" ∷  ⌜ closeable_b = false ∧  own_val = (DfracOwn 1) ⌝)) ∗ 
      (* Once we set closeable we don't try to set any of the bools or change 
      the index again so this can be an iff which makes it easier to get the 
      index and prove everything else is false for the close specs *)
     "HCloseableIff"  ∷ 
     (if closeable_b then 
     ( "%HAllFalseIndMax" ∷ ⌜ (closeable state index num_uses ) ⌝)
     else True) ∗ 
     (* When we can close the channel, the lock takes receiver permissions. 
     This is to allow the closer to be aware that the receiver is not attempting 
     to receive a real value. *)
     "HCloseableTakeReceiverIndex"  ∷ (if closeable_b then ((ghost_var γr (DfracOwn (1/2)) index) ∗ (ghost_var γs (DfracOwn (1/2)) index)) else True) ∗  
     (* The receiver can gain the closed prop only once. It will take ownership from the 
     lock by setting close_prop_ready_b to false and making it persistent. *)
     "HClosePropConsumed" ∷ (if (closed state) then if close_prop_ready_b then R else True else True ) ∗ 
     (* Send side permissions are required to close but the sender gives up permission after closing. 
     This is to prevent sending on a closed channel which panics. 
     This also provides a means to prove that closed is false on the send side 
     since we need to ghost_var_agree with the sender index to match with the 
     Send precondition that states that index is less than max(length Vs), 
     which will produce a contradiction. *)
     "HClosedTakeSenderPermission" ∷ (if closed state then (ghost_var γs (DfracOwn (1/2)) index) else True) ∗ 
     (* Various struct fields *)
     "Hstate" ∷ l ↦[(Channel chan_type) :: "state"] #(W64 state) ∗
     "Hvalue" ∷ l ↦[(Channel chan_type) :: "v"] value ∗
     (* The send/receive permissions that are owned by the lock. 
     These also allow us to relate the sender/receiver index so that we can
     know that the other side is at most 1 off even when we aren't holding
     the lock. *)
     "HSendFirst" ∷ (if bool_decide(state = 2%nat)  then if bool_decide (closeable_b = false) then 
     ((ghost_var γs (DfracOwn (1/2)) index) ∗ (ghost_var γr (DfracOwn (1/2)) index) ∗ (nth index Ps True) ∗ ⌜ value = (nth index Vs (zero_val chan_type)) ⌝)  else True else True)  ∗  
      "HRecFirst" ∷ (if bool_decide(state = 1%nat) then if bool_decide (closeable_b = false) then
     ((ghost_var γs (DfracOwn (1/2)) index) ∗ (ghost_var γr (DfracOwn (1/2)) index) ∗ (nth index Qs True)) else True else True) ∗  
      "HRecSecond" ∷ (if bool_decide(state = 3%nat) then 
     (((ghost_var γs (DfracOwn (1/2)) index) ∗ (ghost_var γr (DfracOwn (1/2)) (index + 1)%nat ))  ∗ (nth index Qs True)) else True)  ∗  
      "HSendSecond" ∷ (if bool_decide(state = 4%nat) then 
     ((ghost_var γs (DfracOwn (1/2)) (index + 1)%nat ) ∗ (ghost_var γr (DfracOwn (1/2)) index) ∗ (nth index Ps True) ∗ ⌜ value = (nth index Vs (zero_val chan_type)) ⌝) else True  ) ∗ 
     (* 'start state' here refers to when neither the receiver nor the sender are waiting for the other.  *) 
     "HStart" ∷ (if bool_decide(state = 0%nat)
     then
     ((ghost_var γs (DfracOwn (1/2)) index) ∗ (ghost_var γr (DfracOwn (1/2)) index)) else True )  
     )
      
 .       
 
 (* Permission to send on the channel *)
 Definition own_UnbufferedChannel_Sender (l: loc) (i: nat) γs: iProp _ :=
   "HSenderIndex" ∷ ghost_var γs (DfracOwn (1/2)) i
 .
 
 Definition own_UnbufferedChannel_SenderProps (l: loc) (P: iProp Σ) (Q: iProp Σ) (R: iProp Σ) (v: val) (i: nat) (num_uses: nat) (chan_type: ty) γs: iProp _ :=
   ∃ 
   (Ps: list (iProp Σ)) (Qs: list (iProp Σ)) (Vs: list val) γ1 γ2 γ3 γ4 γ5 γr,
   "#HChanHandle" ∷  is_UnbufferedChannel l Ps Qs Vs R num_uses chan_type γs γr γ1 γ2 γ3 γ4 γ5 ∗
   "HChanHandleSenderPermission" ∷  own_UnbufferedChannel_Sender l i γs ∗
   (* Make sure we don't have permission when we have sent everything *)
    "%HMax" ∷  ⌜ i < num_uses ⌝  ∗ 
   (* These allow us to specify the props/value that we will 
   acquire/prove/send next *)
    "%HPssender" ∷  ⌜ (nth i Ps True%I) = P ⌝ ∗
    "%HQssender" ∷  ⌜ (nth i Qs True%I) = Q ⌝ ∗
    "%Hvssender" ∷ ⌜ (nth i Vs (zero_val chan_type)) = v ⌝
 .
 
 (* This is the permission we need to close. We use the sender permissions
 here since we can give them up to the lock and not try to close twice. 
 It also does not make sense to close on the receiving end so we don't allow
 this. *)
 Definition own_UnbufferedChannel_CloserProps (l: loc) (i: nat) (R: iProp Σ) (chan_type: ty) γs: iProp _ :=
   ∃ (Ps: list (iProp Σ)) (Qs: list (iProp Σ)) (Vs: list val) (num_uses: nat) γ1 γ2 γ3 γ4 γ5 γr,
   "Hchanhand" ∷  is_UnbufferedChannel l Ps Qs Vs R num_uses chan_type γs γr γ1 γ2 γ3 γ4 γ5 ∗
   "Hchanhandsender" ∷  own_UnbufferedChannel_Sender l i γs ∗
   (* Might not be necessary but should make it easier to connect this 
   with the lock invariants *)
   "%HCap" ∷  ⌜ i = num_uses ⌝ ∗ 
   (* We gain this on exit of the last send which makes it easy to prove 
   that all of the other booleans are false when we try to close *)
   "#Hcloseable"  ∷ ghost_var γ4 DfracDiscarded true 
 .
 
 (* If we have sent everything, we can only close. *)
 Definition own_UnbufferedChannel_SenderProps_Or_Closeable
  (l: loc) (i: nat) (num_uses: nat) (R: iProp Σ) (chan_type: ty) γs: iProp _ :=
 match bool_decide(i < num_uses) with
   | false => own_UnbufferedChannel_CloserProps l i R chan_type γs
   | true => own_UnbufferedChannel_Sender  l i γs
 end
  .
 
 Definition own_UnbufferedChannel_Receiver (l: loc) (i: nat) γr: iProp _ :=
   "Hreceiverindex" ∷ ghost_var γr (DfracOwn (1/2)) i
 .
 
 Definition own_UnbufferedChannel_ReceiverProps (l: loc) (P: iProp Σ) (Q: iProp Σ) (R: iProp Σ) (v: val) (i: nat) (num_uses:nat) (chan_type: ty) γr γ5: iProp _ :=
   ∃ 
   (Ps: list (iProp Σ)) (Qs: list (iProp Σ)) (Vs: list val)  γ1 γ2 γ3 γ4 γs,
   "#HChanHandle" ∷  is_UnbufferedChannel l Ps Qs Vs R num_uses chan_type γs γr γ1 γ2 γ3 γ4 γ5 ∗
    "HChanHandleReceiver" ∷  own_UnbufferedChannel_Receiver l i γr ∗
     "%HPsreceiver" ∷  ⌜(nth i Ps True%I) = P⌝ ∗
     "%HQsreceiver" ∷  ⌜ (nth i Qs True%I) = Q ⌝ ∗
     "%Hvsreceiver" ∷ ⌜ (nth i Vs (zero_val chan_type)) = v ⌝ ∗ 
     "%HMax" ∷  ⌜ i < num_uses  ⌝ ∗ 
     (* The receiver must keep track of whether or not they have 
     consumed the close propositon, which can only happen once *)
     "HReceiverClosedProp" ∷  ghost_var γ5 (DfracOwn (1/2)) true
 .
 
 (* Notably, we don't need receiver permissions to receive on a closed channel. 
 Once we know a channel is able to be closed, we know the sender 
 won't send anything else and receive on a closed channel always returns the
 same thing. *)
 Definition own_UnbufferedChannel_ReceiverClosed (l: loc) (i: nat) (R: iProp Σ) γr γ5: iProp _ :=
   ∃ (Ps: list (iProp Σ)) (Qs: list (iProp Σ)) (Vs: list val) (num_uses: nat) (chan_type:ty) γ1 γ2 γ3 γ4 γs,
   "#Hchanhand" ∷  is_UnbufferedChannel l Ps Qs Vs R num_uses chan_type γs γr γ1 γ2 γ3 γ4 γ5 ∗
   "%HCap" ∷  ⌜ i = num_uses ⌝ ∗ 
   "#Hcloseable"  ∷ ghost_var γ4 DfracDiscarded true 
 .
 
 (* γ5 gives a single receiver the permission to acquire the closed 
 proposition from the sender the first time a blocking receive on a closed 
 channel is complete. After that point, while there wouldn't be much useful
 semantics for it, it is perfectly valid to duplicate the receiver permissions
 so that other threads can pointlessly receive on a closed channel and 
 return the null value. I am trying to be minimal here since it may be 
 possible in the future to regain the original permissions *)
 Definition own_UnbufferedChannel_ReceiverConsumeCloseProp (l: loc) (i: nat) (R: iProp Σ) γr γ5: iProp _ :=
   "#HRecClosed" ∷ own_UnbufferedChannel_ReceiverClosed l i R γr γ5 ∗ 
   "HReceiverClosedProp" ∷  ghost_var γ5 (DfracOwn (1/2)) true   
 .
 
 (* Once we have received all of the values we know the sender will not send
 anymore but may close the channel. Note that we can regain 
 own_UnbufferedChannel_Receiver from the persistent props so we only need to retain
 the receiver permission to receive again. *)
 Definition own_UnbufferedChannel_ReceiverProps_Or_Closed
  (l: loc) (i: nat) (num_uses: nat) (R: iProp Σ) (chan_type: ty) γr γ5: iProp _ :=
 match bool_decide(i < num_uses) with
   | false =>  own_UnbufferedChannel_ReceiverConsumeCloseProp l i R γr γ5
   | true => 
   (∃ (P: iProp Σ) (Q: iProp Σ) (v: val),
   own_UnbufferedChannel_ReceiverProps l P Q R v i num_uses chan_type γr γ5)
 end
  .
 
 Definition TryReceive_Success (l: loc) 
 (P: iProp Σ) (R: iProp Σ) (v: val) (i: nat) (num_uses: nat) (chan_type: ty) γr γ5 : iProp _ :=
 own_UnbufferedChannel_ReceiverProps_Or_Closed
     l (i + 1) num_uses R chan_type γr γ5 ∗ P.
 
 Definition TryReceive_SenderNotReady (l: loc) 
 (P: iProp Σ)  (Q: iProp Σ) (R: iProp Σ) (v: val) (i: nat) (num_uses: nat) (chan_type: ty) γr γ5 : iProp _ :=
  own_UnbufferedChannel_ReceiverProps l P Q R v i num_uses chan_type γr γ5 ∗ Q.
 
 Definition TryReceive_Xor (l: loc) 
 (P: iProp Σ) (Q: iProp Σ) (R: iProp Σ) (v: val) (i: nat) (num_uses: nat) (chan_type: ty) γr γ5 ret_bool ret_val : iProp _ :=
 (* If there is no sender waiting, we just keep the same iProps, otherwise 
 this is the same as Receive *) 
 match ret_bool with
   | false => TryReceive_SenderNotReady l P Q R v i num_uses chan_type γr γ5 ∗ ⌜ret_val = (zero_val chan_type)⌝
   | true => TryReceive_Success l P R v i num_uses chan_type γr γ5 ∗ ⌜ret_val = v⌝
 end
 . 
 
 (* Initializing a channel requires specifying 3 lists. 
 Ps is the list of propositions that the sender must prove to send.
 Qs is the list of propositions the receiver must prove to receive.
 Vs is the list of values the sender sends and the receiver receives.
 R is the proposition the sender must prove to close and the receiver
 can gain on the first receive after close. *)
 Lemma wp_UnbufferedChannel__New  (R: iProp Σ) (num_uses: nat)
 (Ps: list (iProp Σ)) (Qs: list (iProp Σ)) (Vs: list val) (chan_type: ty)
  : num_uses > 0%nat ->
   {{{ True }}}
     NewChannel chan_type #()
   {{{(l: loc) γs γr γ1 γ2 γ3 γ4 γ5, RET #l; 
   own_UnbufferedChannel_ReceiverProps l (hd True%I Ps) (hd True%I Qs) R (hd (zero_val chan_type) Vs) 0 num_uses chan_type γr γ5 ∗
   own_UnbufferedChannel_SenderProps l (hd True%I Ps) (hd True%I Qs) R (hd (zero_val chan_type) Vs) 0 num_uses chan_type γs  ∗
    is_UnbufferedChannel l Ps Qs Vs R num_uses chan_type γs γr γ1 γ2 γ3 γ4 γ5
    }}}.
 Proof.
 Admitted. 

(* The lemmas below can be used after sending to get permission to send the next item or close. *)

(* Once we have sent the prop/value at index i we can gain permission to send index i+1 
if we are still below num_uses. *)
Lemma next_send (l: loc) 
  (P: iProp Σ) (Q: iProp Σ) (R: iProp Σ) (v: val) (i: nat) (num_uses: nat) (chan_type: ty)
  (Ps: list (iProp Σ)) (Qs: list (iProp Σ)) (Vs: list val) γs :
  i < num_uses ∧ nth i Ps True%I = P ∧ nth i Qs True%I = Q
  ∧ nth i Vs (zero_val chan_type) = v ->
  (∃ γ1 γ2 γ3 γ4 γ5 γr,
  is_UnbufferedChannel l Ps Qs Vs R num_uses chan_type γs γr γ1 γ2 γ3 γ4 γ5 ∗
  own_UnbufferedChannel_SenderProps_Or_Closeable l i num_uses R chan_type γs)
  ==∗  
  own_UnbufferedChannel_SenderProps l P Q R v i  num_uses chan_type γs
  .
Proof.
  intros H. iIntros "H". iNamed "H".  unfold own_UnbufferedChannel_SenderProps_Or_Closeable. 
  rewrite bool_decide_true. 
  { unfold own_UnbufferedChannel_SenderProps. iModIntro. iExists Ps. iExists Qs.
  iExists Vs. iExists γ1. iExists γ2. iExists γ3. iExists γ4. iExists γ5. iExists γr. iDestruct "H" as "[H1 H2]". iFrame "#". iFrame. iPureIntro. done.
  }
  apply H.
Qed.

(* Once we have sent everything, we can get permission to close. *)
Lemma last_send (l: loc) 
(P: iProp Σ) (Q: iProp Σ) (R: iProp Σ) (v: val) (i: nat) (num_uses: nat) (chan_type: ty)
(Ps: list (iProp Σ)) (Qs: list (iProp Σ)) (Vs: list val) γs :
   i = num_uses ->
   own_UnbufferedChannel_SenderProps_Or_Closeable l i num_uses R chan_type γs
   ==∗  
   own_UnbufferedChannel_CloserProps l i R chan_type γs
   .
Proof.
  intros H. iIntros "H". iNamed "H".  unfold own_UnbufferedChannel_SenderProps_Or_Closeable. 
  rewrite bool_decide_false. 
  { done. }
  lia.
Qed. 

 

 (* By proving P and sending v, we can gain Q. i is the number of times we 
 have sent so far which is used as an index into the lists of propositions
  and values that we declare when we initialize the channel.
  If i is num_uses-1, we will get permission to close the channel. 
 *)
 Lemma wp_UnbufferedChannel__Send (l: loc) 
 (P: iProp Σ) (Q: iProp Σ) (R: iProp Σ) (v: val) (i: nat) (num_uses: nat) (chan_type: ty) γs :
 val_ty v chan_type -> 
 i + 1 < 2 ^ 63 ->
   {{{ own_UnbufferedChannel_SenderProps l P Q R v i num_uses chan_type γs ∗ P }}}
    Channel__Send chan_type #l v
   {{{ RET #(); 
   own_UnbufferedChannel_SenderProps_Or_Closeable l (i + 1) num_uses R chan_type γs ∗ Q  }}}.
 Proof.
   Admitted.
  
 (* By proving Q, we can gain P and know that the return value is v. 
 i is the number of times we have received so far which is used as an index
 into the lists of propositions and values. *)
 Lemma wp_ReusableChanHandle__Receive (l: loc) 
 (P: iProp Σ) (Q: iProp Σ) (R: iProp Σ) (v: val) (i: nat) (num_uses: nat) (chan_type: ty) γr γ5 :
   {{{ own_UnbufferedChannel_ReceiverProps l P Q R v i num_uses chan_type γr γ5 ∗ Q }}}
     Channel__Receive chan_type #l
   {{{ RET (v, #false); own_UnbufferedChannel_ReceiverProps_Or_Closed
     l (i + 1) num_uses R chan_type γr γ5 ∗ P }}}.
 Proof.
   Admitted.
 
 (* This should be used when we are using a channel closure as a notification. 
 For example, we can use a channel as a join handle by passing it to a goroutine
 that will close when it is done with its work and having the launching goroutine
 receive as a 'join'. We would formalize the result of this work with the 
 proposition R which can only be gained once. *)
 Lemma wp_ReusableChanHandle__ReceiveConsumeCloseProp 
  (l: loc) (R: iProp Σ) (i: nat) (chan_type: ty) γr γ5:
  {{{ own_UnbufferedChannel_ReceiverConsumeCloseProp l i R γr γ5 }}}
     Channel__Receive chan_type #l
   {{{ RET ( (zero_val chan_type), #true); own_UnbufferedChannel_ReceiverClosed l i R γr γ5 ∗ R }}}.
 Proof.
   Admitted. 
 
 
 (* Receive after the closed prop has been gained. This spec is somewhat unlikely
 to be useful since checking multiple times for closed is redundant but makes 
 clear that receiving multiple times on a closed channel is benign. If you are 
 using this, consider if you could instead use a select statement in Go which will 
 use TryReceive in Goose.  *)
 Lemma wp_UnbufferedChannel__ReceiveClosed 
  (l: loc) (R: iProp Σ) (i: nat) (chan_type: ty) γr γ5:
  {{{  own_UnbufferedChannel_ReceiverClosed l i R γr γ5  }}}
     Channel__Receive chan_type #l
   {{{ RET ( (zero_val chan_type), #true); True }}}.
 Proof.
   Admitted. 
 
 (* We can close once and must own the closer iProp R to do so. This should be 
 true if closing is not meant to synchronize. *)
 Lemma wp_UnbufferedChannel__Close (l: loc) 
 (P: iProp Σ) (Q: iProp Σ) (R: iProp Σ) (i: nat) (chan_type: ty) γs :
 i + 1 < 2 ^ 63 ->
   {{{ own_UnbufferedChannel_CloserProps l i R chan_type γs ∗ R}}}
    Channel__Close chan_type #l
   {{{RET #(); True }}}.
   Proof.
     Admitted. 
 
 Lemma wp_ReusableChanHandle__TryReceive (l: loc) 
 (P: iProp Σ) (Q: iProp Σ) (R: iProp Σ) (v: val) (i: nat) (num_uses: nat) (chan_type: ty) γr γ5 :
   {{{ own_UnbufferedChannel_ReceiverProps l P Q R v i num_uses chan_type γr γ5 ∗ Q }}}
     Channel__TryReceive chan_type #l
   {{{ (ret_bool: bool) (ret_val: val),  
     RET (#ret_bool, ret_val, #false); 
     TryReceive_Xor l P Q R v i num_uses chan_type γr γ5 ret_bool ret_val 
      }}}.
 Proof.
   Admitted. 
 
 Definition TryReceiveClosedPropConsume_Success (l: loc) 
 (R: iProp Σ) (i: nat) γr γ5 : iProp _ :=
 own_UnbufferedChannel_ReceiverClosed l i R γr γ5 ∗ R.
 
 Definition TryReceive_CloserNotReady (l: loc) 
  (R: iProp Σ) (i: nat) γr γ5 : iProp _ :=
  own_UnbufferedChannel_ReceiverConsumeCloseProp l i R γr γ5.
 
 Definition TryReceiveClosedPropConsume_Xor (l: loc) 
 (R: iProp Σ) (i: nat) γr γ5 ret_bool : iProp _ :=
 (* If there is no sender waiting, we just keep the same iProps, otherwise 
 this is the same as Receive *) 
 match ret_bool with
   | false => TryReceive_CloserNotReady l R i γr γ5 
   | true => TryReceiveClosedPropConsume_Success l R i γr γ5
 end
 . 
 
 (* We cannot use TryReceive to gain the closed proposition R since it will 
 not block even if the channel isn't closed. This spec can be used after all 
 receive propositions/values have been gained, i.e. in a range for loop where we 
 receive until the sender closes, at which point the spec here tells us we 
 return false. *)
 Lemma wp_ReusableChanHandle__TryReceiveClosed 
  (l: loc) (R: iProp Σ) (i: nat) (chan_type: ty) γr γ5:
  {{{ own_UnbufferedChannel_ReceiverConsumeCloseProp l i R γr γ5 }}}
     Channel__TryReceive chan_type #l
   {{{ (ret_bool: bool),  RET ( #ret_bool ,(zero_val chan_type),  #ret_bool);
    TryReceiveClosedPropConsume_Xor l R i γr γ5 ret_bool }}}.
 Proof.
   Admitted. 
 
 Definition TrySend_Success (l: loc) 
 (Q: iProp Σ) (R: iProp Σ) (v: val) (i: nat) (num_uses: nat) (chan_type: ty) γs : iProp _ :=
 own_UnbufferedChannel_SenderProps_Or_Closeable l (i + 1) num_uses R chan_type γs ∗ Q.
 
 Definition TrySend_Failure (l: loc) 
 (P: iProp Σ)  (Q: iProp Σ) (R: iProp Σ) (v: val) (i: nat) (num_uses: nat) (chan_type: ty) γs : iProp _ :=
   own_UnbufferedChannel_SenderProps l P Q R v i num_uses chan_type γs ∗ P.
 
 Definition TrySend_Xor (l: loc) 
 (P: iProp Σ) (Q: iProp Σ) (R: iProp Σ) (v: val) (i: nat) (num_uses: nat) chan_type γs ret_val : iProp _ :=
 (* If a receiver isn't ready, we simply keep all of our iProps. If one is, 
 we have the same postcondition as send *) 
 match ret_val with
   | false => TrySend_Failure l P Q R v i num_uses chan_type γs 
   | true => TrySend_Success l Q R v i num_uses chan_type γs  
 end
 .
 
 Lemma wp_UnbufferedChannel__TrySend (l: loc) 
 (P: iProp Σ) (Q: iProp Σ) (R: iProp Σ) (v: val) (i: nat) (num_uses: nat) (chan_type: ty) γs :
 val_ty v chan_type -> 
 i + 1 < 2 ^ 63 ->
   {{{ own_UnbufferedChannel_SenderProps l P Q R v i num_uses chan_type γs ∗ P }}}
    Channel__TrySend chan_type #l v
   {{{ (ret_val: bool), RET #ret_val;
   TrySend_Xor l P Q R v i num_uses chan_type γs ret_val }}}.
 Proof.
   Admitted.
 
 End UnbufferedChannel.