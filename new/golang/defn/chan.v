From New.golang.defn Require Export loop assume predeclared.
From New.code.github_com.goose_lang.goose.model Require Import channel.

Module chan.
Section defns.
Context {ext : ffi_syntax} {go_gctx : GoGlobalContext}.

Definition receive elem_type : val :=
  λ: "c", MethodResolve (go.PointerType $ channel.Channel elem_type) "Receive" "c" #().
Definition send elem_type : val :=
  λ: "c", MethodResolve (go.PointerType $ channel.Channel elem_type) "Send" "c".

Definition for_range elem_type : val :=
  λ: "c" "body",
    (for: (λ: <>, #true)%V; (λ: <>, Skip)%V := λ: <>,
       let: ("v", "ok") := receive elem_type "c" in
       if: "ok" then
         "body" "v"
       else
         (* channel is closed *)
         break: #()
    ).

(* One could opt for reflection/dynamic typing here, mirroring the actual Go
   reflect package. However, this does not line up so nicely with the generic
   channel model.
   In particular, using `Channel[T]` for `chan T` would require support for
   dynamically instantiating generics, which Go probably anyways does not
   support since it uses monomorphization. One could alternatively only
   instantiate Channel[T] with `any` and use type assertions to get the right
   types, but this would not match the way tests are written against the channel
   model, so this also seems improper.
*)

(* Semantics is:
   - Shuffle the list of non-default cases.
   - Try the cases in order, finishing the select if one is ready.
   - if there's a default then select it; else, go back to the beginning.
 *)
Definition try_comm_clause (c : comm_clause) : val :=
  λ: "blocking",
    let (case', body) := c in
    match case' with
    | SendCase elem_type ch e =>
        let: "success" :=
          MethodResolve (go.PointerType $ channel.Channel elem_type) "TrySend" ch e "blocking" in
        if: "success" then ((λ: <>, body)%V #(), #true)
        else (#(), #false)
    | RecvCase elem_type ch =>
        let: (("success", "v"), "ok") :=
          MethodResolve (go.PointerType $ channel.Channel elem_type) "TryReceive" ch "blocking" in
        if: "success" then ((λ: "$recvVal", body)%V ("v", "ok"), #true)
        else (#(), #false)
    end.

(** [try_select] is used as the core of both [select_blocking] and [select_nonblocking] *)
Definition try_select (blocking : bool) : list comm_clause → expr :=
  foldr (λ clause cases_remaining,
      let: ("v", "done") := try_comm_clause clause #blocking in
      if: ~"done" then (λ: <>, cases_remaining)%V #()
      else ("v", #true))%E
    (#(), #false)%E.
End defns.
End chan.


Module go.
Section defs.
Context {ext : ffi_syntax}.
Context {go_lctx : GoLocalContext} {go_gctx : GoGlobalContext}.

Class ChanSemantics `{!GoSemanticsFunctions} :=
{
  #[global] package_sem :: channel.Assumptions;

  #[global] convert_channel dir1 dir2 elem (c : chan.t) ::
    ⟦Convert (go.ChannelType dir1 elem) (go.ChannelType dir2 elem), #c⟧ ⤳[under] #c;

  #[global] make2_chan `{!t ↓u go.ChannelType dir elem_type} ::
    FuncUnfold go.make2 [t]
    (λ: "cap", FuncResolve channel.NewChannel [elem_type] #() "cap")%V;
  #[global] make1_chan `{!t ↓u go.ChannelType dir elem_type} ::
    FuncUnfold go.make1 [t]
    (λ: "<>", FuncResolve go.make2 [t] #() #(W64 0))%V;
  #[global] close_chan `{!t ↓u go.ChannelType dir elem_type} ::
    FuncUnfold go.close [t]
    (λ: "c", MethodResolve (go.PointerType $ channel.Channel elem_type) "Close" "c" #())%V;
  #[global] len_chan `{!t ↓u go.ChannelType dir elem_type} ::
    FuncUnfold go.len [t]
    (λ: "c", MethodResolve (go.PointerType $ channel.Channel elem_type) "Len" "c" #())%V;
  #[global] cap_chan `{!t ↓u go.ChannelType dir elem_type} ::
    FuncUnfold go.cap [t]
    (λ: "c", MethodResolve (go.PointerType $ channel.Channel elem_type) "Cap" "c" #())%V;

  chan_select_nonblocking default_handler clauses :
    is_go_step_pure SelectStmt (SelectStmtClausesV (Some default_handler) clauses) =
    (λ e',
       ∃ clauses',
         clauses' ≡ₚ clauses ∧
         e' =
         (let: ("v", "succeeded") := chan.try_select false clauses' in
          if: "succeeded" then "v"
          else (λ: <>, default_handler)%V #())%E
    );
  chan_select_blocking clauses :
    is_go_step_pure SelectStmt (SelectStmtClausesV None clauses) =
    (λ e',
       ∃ clauses',
         clauses' ≡ₚ clauses ∧
         e' =
         (let: ("v", "succeeded") := chan.try_select true clauses' in
          if: "succeeded" then "v"
          else (λ: <>, SelectStmt (SelectStmtClauses None clauses))%V #())%E
    );
}.
End defs.
End go.

#[global] Opaque chan.receive chan.send chan.for_range.
