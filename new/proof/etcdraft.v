From New.code.go_etcd_io.raft Require Import v3.
From New.proof Require Import grove_prelude.
From New.proof Require Import sync.

Module MessageType.
Definition t := w32.
End MessageType.

Module blackHole.
Record t := mk {}.
End blackHole.

Instance into_val_blackHole `{ffi_syntax} : IntoVal blackHole.t :=
  {|
    to_val_def := λ v, struct.val_aux blackHole []
  |}.
Program Instance into_val_typed_blackHole `{ffi_syntax} : IntoValTyped blackHole.t blackHole :=
{| default_val := blackHole.mk |}.
Next Obligation. rewrite to_val_unseal /=. solve_has_go_type. Qed.
Next Obligation.
  intros. rewrite zero_val_eq to_val_unseal /= struct.val_aux_unseal //=.
Qed.
Next Obligation. Admitted.
Final Obligation. solve_decision. Qed.

Instance wp_struct_make_blackHole `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} :
  PureWp True
  (struct.make blackHole (struct.fields_val []%V))
  #(blackHole.mk)
.
Proof.
  pose proof wp_struct_make.
  rewrite /PureWp => *. iIntros "Hwp".
  wp_pure_lc "Hlc".
  iEval (rewrite to_val_unseal /=) in "Hwp". by iApply "Hwp".
Qed.

Module testLeaderElectionStruct.
Record t :=
  mk {
      network : loc;
      state : w64;
      expTerm : w64
    }.
End testLeaderElectionStruct.
Instance into_val_testLeaderElectionStruct `{ffi_syntax} : IntoVal testLeaderElectionStruct.t :=
  {|
    to_val_def :=
      λ v, struct.val_aux testLeaderElectionStruct [
               "network" ::= #v.(testLeaderElectionStruct.network);
               "state" ::= #v.(testLeaderElectionStruct.state);
               "expTerm" ::= #v.(testLeaderElectionStruct.expTerm)
             ]%V
  |}.
Program Instance into_val_typed_testLeaderElectionStruct `{ffi_syntax} : IntoValTyped testLeaderElectionStruct.t testLeaderElectionStruct :=
{| default_val := testLeaderElectionStruct.mk
                    (default_val _) (default_val _) (default_val _) |}.
Next Obligation. rewrite to_val_unseal /=. solve_has_go_type. Qed.
Next Obligation.
  intros. rewrite zero_val_eq to_val_unseal /= struct.val_aux_unseal //=.
  rewrite zero_val_eq /= to_val_unseal //=.
Qed.
Next Obligation. Admitted.
Final Obligation. solve_decision. Qed.

Instance wp_struct_make_testLeaderElectionStruct `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}
  network state expTerm :
  PureWp True
    (struct.make testLeaderElectionStruct (struct.fields_val [
                                               "network" ::= #network;
                                               "state" ::= #state;
                                               "expTerm" ::= #expTerm
                                             ]%V))
    #(testLeaderElectionStruct.mk network state expTerm)
.
Proof.
  pose proof wp_struct_make.
  rewrite /PureWp => *. iIntros "Hwp".
  wp_pure_lc "Hlc".
  iEval (rewrite to_val_unseal /=) in "Hwp". by iApply "Hwp".
Qed.

Module Message.
Record t :=
  mk {
    Type' : MessageType.t;
    To: w64;
    From: w64;
    Term: w64;
    LogTerm: w64;
    Index: w64;
    Entries: slice.t;
    Commit: w64;
    Vote: w64;
    Snapshot: loc;
    Reject: bool;
    RejectHint: w64;
    Context: slice.t;
    Responses: slice.t;
  }.
End Message.
Instance into_val_Message `{ffi_syntax} : IntoVal Message.t :=
  {|
    to_val_def :=
      λ v, struct.val_aux raftpb.Message [
               "Type" ::= #v.(Message.Type');
               "To" ::= #v.(Message.To);
               "From" ::= #v.(Message.From);
               "Term" ::= #v.(Message.Term);
               "LogTerm" ::= #v.(Message.LogTerm);
               "Index" ::= #v.(Message.Index);
               "Entries" ::= #v.(Message.Entries);
               "Commit" ::= #v.(Message.Commit);
               "Vote" ::= #v.(Message.Vote);
               "Snapshot" ::= #v.(Message.Snapshot);
               "Reject" ::= #v.(Message.Reject);
               "RejectHint" ::= #v.(Message.RejectHint);
               "Context" ::= #v.(Message.Context);
               "Responses" ::= #v.(Message.Responses)
             ]%V
  |}.
Program Instance into_val_typed_Message `{ffi_syntax} : IntoValTyped Message.t raftpb.Message :=
{| default_val := Message.mk (default_val _) (default_val _) (default_val _) (default_val _)
                    (default_val _) (default_val _) (default_val _) (default_val _)
                    (default_val _) (default_val _) (default_val _) (default_val _)
                    (default_val _) (default_val _)
|}.
Next Obligation. rewrite to_val_unseal /=. solve_has_go_type. Qed.
Next Obligation.
  intros. rewrite zero_val_eq to_val_unseal /= struct.val_aux_unseal /=.
  rewrite zero_val_eq /= !to_val_unseal //.
Qed.
Next Obligation. Admitted.
Final Obligation. solve_decision. Qed.

Instance wp_struct_make_Message `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}
  Type' To From Term LogTerm Index Entries Commit Vote Snapshot Reject RejectHint Context Responses:
  PureWp True
    (struct.make raftpb.Message (struct.fields_val [
                              "Type" ::= #Type';
                              "To" ::= #To;
                              "From" ::= #From;
                              "Term" ::= #Term;
                              "LogTerm" ::= #LogTerm;
                              "Index" ::= #Index;
                              "Entries" ::= #Entries;
                              "Commit" ::= #Commit;
                              "Vote" ::= #Vote;
                              "Snapshot" ::= #Snapshot;
                              "Reject" ::= #Reject;
                              "RejectHint" ::= #RejectHint;
                              "Context" ::= #Context;
                              "Responses" ::= #Responses
                            ]%V))
    #(Message.mk Type' To From Term LogTerm Index Entries Commit Vote Snapshot Reject RejectHint
                 Context Responses)
.
Proof.
  pose proof wp_struct_make.
  rewrite /PureWp => *. iIntros "Hwp".
  wp_pure_lc "Hlc".
  iEval (rewrite to_val_unseal /=) in "Hwp". by iApply "Hwp".
Qed.

Program Instance iv_Message_Type `{ffi_syntax} : IntoValStructField "Type" raftpb.Message Message.Type'.
Final Obligation. intros. repeat (rewrite ?to_val_unseal ?struct.val_aux_unseal //=). Qed.

Program Instance iv_Message_To `{ffi_syntax} : IntoValStructField "To" raftpb.Message Message.To.
Final Obligation. intros. repeat (rewrite ?to_val_unseal ?struct.val_aux_unseal //=). Qed.

Program Instance iv_Message_From `{ffi_syntax} : IntoValStructField "From" raftpb.Message Message.From.
Final Obligation. intros. repeat (rewrite ?to_val_unseal ?struct.val_aux_unseal //=). Qed.

Program Instance iv_Message_Term `{ffi_syntax} : IntoValStructField "Term" raftpb.Message Message.Term.
Final Obligation. intros. repeat (rewrite ?to_val_unseal ?struct.val_aux_unseal //=). Qed.

Program Instance iv_Message_LogTerm `{ffi_syntax} : IntoValStructField "LogTerm" raftpb.Message Message.LogTerm.
Final Obligation. intros. repeat (rewrite ?to_val_unseal ?struct.val_aux_unseal //=). Qed.

Program Instance iv_Message_Index `{ffi_syntax} : IntoValStructField "Index" raftpb.Message Message.Index.
Final Obligation. intros. repeat (rewrite ?to_val_unseal ?struct.val_aux_unseal //=). Qed.

Program Instance iv_Message_Entries `{ffi_syntax} : IntoValStructField "Entries" raftpb.Message Message.Entries.
Final Obligation. intros. repeat (rewrite ?to_val_unseal ?struct.val_aux_unseal //=). Qed.

Program Instance iv_Message_Commit `{ffi_syntax} : IntoValStructField "Commit" raftpb.Message Message.Commit.
Final Obligation. intros. repeat (rewrite ?to_val_unseal ?struct.val_aux_unseal //=). Qed.

Program Instance iv_Message_Vote `{ffi_syntax} : IntoValStructField "Vote" raftpb.Message Message.Vote.
Final Obligation. intros. repeat (rewrite ?to_val_unseal ?struct.val_aux_unseal //=). Qed.

Program Instance iv_Message_Snapshot `{ffi_syntax} : IntoValStructField "Snapshot" raftpb.Message Message.Snapshot.
Final Obligation. intros. repeat (rewrite ?to_val_unseal ?struct.val_aux_unseal //=). Qed.

Program Instance iv_Message_Reject `{ffi_syntax} : IntoValStructField "Reject" raftpb.Message Message.Reject.
Final Obligation. intros. repeat (rewrite ?to_val_unseal ?struct.val_aux_unseal //=). Qed.

Program Instance iv_Message_RejectHint `{ffi_syntax} : IntoValStructField "RejectHint" raftpb.Message Message.RejectHint.
Final Obligation. intros. repeat (rewrite ?to_val_unseal ?struct.val_aux_unseal //=). Qed.

Program Instance iv_Message_Context `{ffi_syntax} : IntoValStructField "Context" raftpb.Message Message.Context.
Final Obligation. intros. repeat (rewrite ?to_val_unseal ?struct.val_aux_unseal //=). Qed.

Program Instance iv_Message_Responses `{ffi_syntax} : IntoValStructField "Responses" raftpb.Message Message.Responses.
Final Obligation. intros. repeat (rewrite ?to_val_unseal ?struct.val_aux_unseal //=). Qed.

Module network.
Record t :=
  mk {
      t' : loc;
      peers : loc ;
      storage : loc ;
      dropm64 : loc ;
      ignorem : loc ;
      msgHook : func.t ;
    }.
End network.

Section proof.
Context `{!heapGS Σ}.

(* FIXME: move to builtin *)
Instance wp_int_gt (l r : w64) : PureWp True (int_gt #l #r) #(bool_decide (sint.Z l > sint.Z r)).
Proof. Admitted.

Lemma wp_newNetworkWithConfigInit (peers : list interface.t) peers_sl :
  {{{
        peers_sl ↦* peers
  }}}
    newNetworkWithConfigInit #func.nil #peers_sl
  {{{
        (nw : loc), RET #nw; True
  }}}
.
Proof.
Admitted.

Lemma wp_entsWithConfig terms_sl (terms : list u64) :
  {{{
        terms_sl ↦* terms
  }}}
    entsWithConfig #func.nil #terms_sl
  {{{ (r : loc), RET #r; True }}}
.
Proof.
Admitted.

Lemma wp_network__send (nw : loc) msgs_sl dq (msgs : list Message.t) :
  {{{
        msgs_sl ↦*{dq}  msgs
  }}}
    network__send #nw #msgs_sl
  {{{ RET #(); True }}}
.
Proof.
  iIntros (?) "Hsl HΦ".
  wp_call.
  wp_alloc nw_ptr as "?".
  wp_pures.
  wp_alloc msgs_ptr as "?".
  wp_pures.
  wp_for.
  wp_pures.
  wp_load.
  wp_pures.
  case_bool_decide as Hlt.
  - rewrite decide_True //. (* Case: more messages to send *)
    wp_pures.
    rewrite -!default_val_eq_zero_val.
    wp_alloc m as "Hm".
    wp_pures.
    iDestruct (own_slice_len with "Hsl") as %Hsl.
    destruct msgs.
    { exfalso. simpl in *. rewrite !word.signed_eq_swrap_unsigned /word.swrap in Hlt. word. }
    iDestruct (own_slice_elem_acc 0 with "Hsl") as "[Helem Hsl]".
    { done. }
    wp_load.
    wp_pure.
    {
      (* FIXME(word): handle sint.Z *)
      rewrite !word.signed_eq_swrap_unsigned /word.swrap in Hlt.
      word.
    }
    wp_load.
    wp_pures.
    iDestruct ("Hsl" with "[$]") as "Hsl".
    rewrite list_insert_id; last done.
    wp_store.
    wp_pures.
    wp_alloc p as "?".
    wp_pures.
    iDestruct (struct_fields_split with "Hm") as "Hm".
    { done. }
    { apply _. }
    rewrite /struct_fields /=.
    repeat (iDestruct "Hm" as "[H1 Hm]";
            unshelve iSpecialize ("H1" $! _ _ _ _ _ _); try tc_solve;
            iNamed "H1").
    wp_load.
    wp_load.
    wp_pures.
    admit. (* TODO: load peers from network *)
  - rewrite decide_False; last naive_solver.
    rewrite decide_True; last naive_solver.
    wp_pures. by iApply "HΦ".
Admitted.

Ltac wp_steps :=
  wp_pures; try ((wp_load; wp_steps) || (wp_store; wp_steps)).

Lemma wp_testLeaderElection2 :
  {{{ True }}}
    testLeaderElection2 #null #false
  {{{ RET #(); True }}}.
Proof.
  Set Ltac Profiling.
  iIntros (?) "_ HΦ".
  wp_call.
  wp_alloc preVote as "?".
  wp_pures.
  wp_alloc t_ptr as "?".
  wp_steps.
  rewrite -!default_val_eq_zero_val.
  wp_alloc cfg as "Hcfg".
  wp_pures.
  wp_alloc candState as "HcandState".
  wp_steps.
  wp_alloc candTerm as "HcandTerm".
  wp_steps.

  wp_alloc nopStepper as "HnopStepper".
  wp_pures.
  wp_alloc nopStepperPtr as "HnopStepperPtr".
  wp_steps.
  wp_alloc tests as "Htests".
  wp_steps.

  wp_apply wp_slice_literal.
  { instantiate (1:=[_ ; _ ; _ ]). done. }
  iIntros (?) "?".

  wp_pures.
  wp_apply (wp_newNetworkWithConfigInit with "[$]").
  iIntros (?) "Hnw1".

  wp_steps.
  (* FIXME: slice literal simplification *)
  Ltac solve_slice_literal :=
    repeat ((by instantiate (1:=nil)) || instantiate (1:=cons _ _); simpl; f_equal).
  wp_apply wp_slice_literal.
  { solve_slice_literal. }
  iIntros (?) "?".
  wp_pures.
  wp_apply (wp_newNetworkWithConfigInit with "[$]").
  iIntros (?) "Hnw2".

  wp_steps.
  wp_apply wp_slice_literal.
  { solve_slice_literal. }
  iIntros (?) "?".
  wp_pures.
  (* Time wp_apply (wp_newNetworkWithConfigInit with "[$]"). *)
  Time wp_bind (newNetworkWithConfigInit _ _); iApply (wp_newNetworkWithConfigInit with "[$]"); iModIntro.
  iIntros (?) "Hnw3".

  wp_steps.
  wp_apply wp_slice_literal.
  { solve_slice_literal. }
  iIntros (?) "?".
  wp_pures.
  wp_apply (wp_newNetworkWithConfigInit with "[$]").
  iIntros (?) "Hnw4".

  wp_steps.
  wp_apply wp_slice_literal.
  { solve_slice_literal. }
  iIntros (?) "?".
  wp_pures.
  wp_apply (wp_newNetworkWithConfigInit with "[$]").
  iIntros (?) "Hnw5".

  wp_steps.

  wp_apply wp_slice_literal.
  { solve_slice_literal. }
  iIntros (?) "?".
  wp_pures.
  wp_apply (wp_entsWithConfig with "[$]").
  iIntros (?) "Hr1".

  wp_steps.
  wp_apply wp_slice_literal.
  { solve_slice_literal. }
  iIntros (?) "?".
  wp_pures.
  wp_apply (wp_entsWithConfig with "[$]").
  iIntros (?) "Hr2".

  wp_steps.
  wp_apply wp_slice_literal.
  { solve_slice_literal. }
  iIntros (?) "?".
  wp_pures.
  wp_apply (wp_entsWithConfig with "[$]").
  iIntros (?) "Hr3".

  wp_pures.
  wp_apply wp_slice_literal.
  { solve_slice_literal. }
  iIntros (?) "?".
  wp_pures.
  wp_apply (wp_newNetworkWithConfigInit with "[$]").
  iIntros (?) "Hnw6".
  wp_pures.
  wp_apply wp_slice_literal.
  { solve_slice_literal. }
  iIntros (?) "?".
  wp_steps.

  wp_apply wp_slice_for_range.
  iFrame.
  simpl foldr.
  (* Entire for loop is unfolded here. TODO: is there a way to unfold one iteration at a time? *)
  wp_pures.
  wp_alloc i as "?".
  wp_pures.
  wp_alloc tt as "Htt".
  wp_pures.

  Show Ltac Profile.
Admitted.

End proof.
