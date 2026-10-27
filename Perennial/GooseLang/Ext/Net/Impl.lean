/-
The network extension of GooseLang [Trusted definitions!].

A toy network between the nodes of a distributed system
(`DistLang.lean`). Every node has an address (a string), its local state. The
network is global: for every address, the set of messages sent to it so far.
A message carries its sender's address, attached by the network: a node
cannot send a message in the name of another.

**A toy, not a model of a real network.** It is the example extension of the
distributed adequacy theorem (`netfs`). Its Go side
(`netfs/netext`) has no implementation: its primitives are stubs, so the
model is the specification an implementation would have to meet, not a
description of existing Go code.

* `SendOp (to, data)` adds the message `(me, data)` to the messages of the
  address `to`, where `me` is the sending node's address. The network need not
  know the address `to` beforehand.
* `RecvOp ()` returns some message `(from, data)` sent to the receiving
  node's address, as the pair `(from, data)`, or stutters (steps to itself:
  the receive waits). A message is never removed: the network may deliver a
  message any number of times (duplication), in any order (reordering), or
  never (loss).
* Neither operation changes the heap or the node's address; addresses and data
  are passed and returned as Go values (`#to`, `#data`).
* Crashes (`ExtSemantics.crash`): the address survives unchanged.
-/
module

public import Perennial.GooseLang.Lang

@[expose] public section

namespace Perennial

inductive NetOp where
  | SendOp | RecvOp
deriving DecidableEq, Inhabited

instance : Pos.Countable NetOp where
  encode o := Pos.Countable.encode (match o with | .SendOp => (0 : Nat) | .RecvOp => 1)
  decode p := match (Pos.Countable.decode p : Option Nat) with
    | some 0 => some .SendOp | some 1 => some .RecvOp | _ => none
  decode_encode o := by cases o <;> simp [Pos.Countable.decode_encode]

/-- A message: its sender's address and its data. -/
structure NetMsg where
  sender : GoString
  data : List w8
deriving DecidableEq

/-- The network: for every address, the messages sent to it so far. An address
not in the map has received no message. -/
abbrev NetState := GMap GoString (GSet NetMsg)

instance : Inhabited NetState := ⟨∅⟩

/-- The messages sent to the address `a`. -/
def NetState.msgs (n : NetState) (a : GoString) : GSet NetMsg := (n !! a).getD ∅

/-- The network extension. Its local state is the node's address. It has no
values of its own. -/
@[reducible] def netExt : GooseExt where
  name := "github.com/mit-pdos/perennial/goose/testdata/examples/netfs/netext"
  Op := NetOp
  Val := Empty
  LocalState := GoString
  GlobalState := NetState

section net
variable [GooseExts] [GoGlobalContext]

/-- The step relation of the network, for the node with address `me`. -/
def NetStep (op : NetOp) (v : val) (h : GMap Loc (NonAtomic val)) (me : GoString)
    (n : NetState) (e' : Expr) (h' : GMap Loc (NonAtomic val)) (me' : GoString)
    (n' : NetState) : Prop :=
  h' = h ∧ me' = me ∧
  match op with
  | .SendOp => ∃ (to : GoString) (data : List w8),
      v = PairV (#to) (#data) ∧ e' = Val (#()) ∧
      n' = <[to := n.msgs to ∪ {[⟨me, data⟩]}]> n
  | .RecvOp => v = #() ∧ n' = n ∧
      (e' = ExternalOp (extOp netExt NetOp.RecvOp) (Val v) ∨
        ∃ m, m ∈ n.msgs me ∧ e' = Val (PairV (#m.sender) (#m.data)))

end net

/-- On a crash, the node keeps its address. -/
instance net_semantics : ExtSemantics netExt where
  step := NetStep
  crash me me' := me' = me

end Perennial
