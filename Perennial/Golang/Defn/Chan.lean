/-
Port of `new/golang/defn/chan.v`. Channels are implemented by the Go channel
model (`github.com/mit-pdos/perennial/goose/model/channel`), whose generated
translation lives in namespace `github_com.mit_pdos.perennial.goose.model.channel`
(Rocq: `channel`).
-/
import Perennial.Golang.Defn.Loop
import Perennial.Golang.Defn.Assume
import Perennial.Golang.Defn.Predeclared
import Perennial.Code.github_com.mit_pdos.perennial.goose.model.channel

namespace Perennial

namespace chan
section defns
variable [ffi_syntax] [GoGlobalContext]

open github_com.mit_pdos.perennial.goose.model in
def receive (elem_type : go.type) : val :=
  λ: "c", MethodResolve (go.PointerType (channel.Channel elem_type)) "Receive" "c" #()

open github_com.mit_pdos.perennial.goose.model in
def send (elem_type : go.type) : val :=
  λ: "c", MethodResolve (go.PointerType (channel.Channel elem_type)) "Send" "c"

def for_range (elem_type : go.type) : val :=
  λ: "c" "body",
    (for: (λ: <>, #true : val) ; (λ: <>, #() : val) := λ: <>,
       let: ("v", "ok") := receive elem_type "c" in
       if: "ok" then
         "body" "v"
       else
         -- channel is closed
         break: #()
    )

/-
One could opt for reflection/dynamic typing here, mirroring the actual Go
reflect package. However, this does not line up so nicely with the generic
channel model.
In particular, using `Channel[T]` for `chan T` would require support for
dynamically instantiating generics, which Go probably anyways does not support
since it uses monomorphization. One could alternatively only instantiate
Channel[T] with `any` and use type assertions to get the right types, but this
would not match the way tests are written against the channel model, so this
also seems improper.

Semantics is:
- Shuffle the list of non-default cases.
- Try the cases in order, finishing the select if one is ready.
- if there's a default then select it; else, go back to the beginning.
-/
open github_com.mit_pdos.perennial.goose.model in
def try_comm_clause (c : comm_clause) : val :=
  match c with
  | CommClause case' body =>
  λ: "blocking",
    match case' with
    | SendCase elem_type ch e =>
        gl(let: "success" :=
          MethodResolve (go.PointerType (channel.Channel elem_type)) "TrySend" ch e "blocking" in
        if: "success" then ((λ: <>, body : val) #(), #true)
        else (#(), #false))
    | RecvCase elem_type ch =>
        gl(let: (("success", "v"), "ok") :=
          MethodResolve (go.PointerType (channel.Channel elem_type)) "TryReceive" ch "blocking" in
        if: "success" then ((λ: <>, body : val) #() ("v", "ok"), #true)
        else (#(), #false))

/-- `try_select` is used as the core of both `select_blocking` and
`select_nonblocking` -/
def try_select (blocking : Bool) : List comm_clause → expr :=
  List.foldr (fun clause cases_remaining =>
      gl(let: ("v", "done") := try_comm_clause clause #blocking in
      if: ⟨go.bool⟩! "done" then (λ: <>, cases_remaining : val) #()
      else ("v", #true)))
    gl((#(), #false))

end defns
end chan

namespace go
section defs
variable [ffi_syntax] [GoLocalContext] [GoGlobalContext]
open github_com.mit_pdos.perennial.goose.model

class ChanSemantics [GoSemanticsFunctions] : Prop where
  [package_sem : channel.Assumptions]

  convert_channel (dir1 dir2 : go.chan_dir) (elem : go.type) (c : chan.t) :
    ⟦Convert (go.ChannelType dir1 elem) (go.ChannelType dir2 elem), #c⟧ ⤳[under] #c

  make2_chan {t : go.type} {dir : go.chan_dir} {elem_type : go.type}
    [t ↓u go.ChannelType dir elem_type] :
    FuncUnfold go.make2 [t]
    (λ: "cap", FuncResolve channel.NewChannel [elem_type] #() "cap" : val)
  make1_chan {t : go.type} {dir : go.chan_dir} {elem_type : go.type}
    [t ↓u go.ChannelType dir elem_type] :
    FuncUnfold go.make1 [t]
    (λ: "<>", FuncResolve go.make2 [t] #() #(W64 0) : val)
  close_chan {t : go.type} {dir : go.chan_dir} {elem_type : go.type}
    [t ↓u go.ChannelType dir elem_type] :
    FuncUnfold go.close [t]
    (λ: "c", MethodResolve (go.PointerType (channel.Channel elem_type)) "Close" "c" #() : val)
  len_chan {t : go.type} {dir : go.chan_dir} {elem_type : go.type}
    [t ↓u go.ChannelType dir elem_type] :
    FuncUnfold go.len [t]
    (λ: "c", MethodResolve (go.PointerType (channel.Channel elem_type)) "Len" "c" #() : val)
  cap_chan {t : go.type} {dir : go.chan_dir} {elem_type : go.type}
    [t ↓u go.ChannelType dir elem_type] :
    FuncUnfold go.cap [t]
    (λ: "c", MethodResolve (go.PointerType (channel.Channel elem_type)) "Cap" "c" #() : val)

  chan_select_nonblocking (default_handler : expr) (clauses : List comm_clause) :
    is_go_step_pure SelectStmt (SelectStmtClausesV (some default_handler) clauses) =
    (fun (e' : expr) =>
       ∃ clauses',
         clauses'.Perm clauses ∧
         e' =
         gl(let: ("v", "succeeded") := chan.try_select false clauses' in
          if: "succeeded" then "v"
          else (λ: <>, default_handler : val) #()))
  chan_select_blocking (clauses : List comm_clause) :
    is_go_step_pure SelectStmt (SelectStmtClausesV none clauses) =
    (fun (e' : expr) =>
       ∃ clauses',
         clauses'.Perm clauses ∧
         e' =
         gl(let: ("v", "succeeded") := chan.try_select true clauses' in
          if: "succeeded" then "v"
          else (λ: <>, SelectStmt (SelectStmtClauses none clauses) : val) #()))

attribute [instance] ChanSemantics.package_sem ChanSemantics.convert_channel
  ChanSemantics.make2_chan ChanSemantics.make1_chan ChanSemantics.close_chan
  ChanSemantics.len_chan ChanSemantics.cap_chan
export ChanSemantics (convert_channel make2_chan make1_chan close_chan len_chan cap_chan
  chan_select_nonblocking chan_select_blocking)

end defs
end go

attribute [irreducible] chan.receive chan.send chan.for_range

end Perennial
