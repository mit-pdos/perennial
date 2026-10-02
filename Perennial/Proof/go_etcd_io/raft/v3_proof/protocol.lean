/-
Port of `new/proof/go_etcd_io/raft/v3_proof/protocol.v`: the (axiomatized)
abstract raft log and specifications of `node.Ready`, `node.Advance` and
`node.Propose`.

Lean notes:
* Everything lives in `namespace go_etcd_io.raft.v3_proof` (Rocq: top level);
  Rocq's `Module node`/`Module message` (axiomatized types) would clash with
  the generated `go_etcd_io.raft.v3.node`, so they are `v3_proof.node.t` and
  `v3_proof.message.t`. Generated raft names are written `v3.node`, ...
* The broadcast and bag idioms fix `hlc := HasLC.hasLC` and need `[allG GF]`.
  The bag over `error.t = interface.t` needs `Pos.Countable interface.t`, which
  (as in `channel_dsp.lean`, `etcd/pkg/v3/wait.lean`) is derived from an
  explicit `[Pos.Countable val]` assumption.
-/
import Perennial.Proof.go_etcd_io.raft.v3_proof.base
import Perennial.Golang.Theory.Chan.Idioms.Broadcast
import Perennial.Golang.Theory.Chan.Idioms.Bag
import Perennial.Golang.Theory.Chan.AuSpec.ChanAuBase

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace go_etcd_io.raft.v3_proof

/-- Rocq `Module node. Axiom t : Type. End node.` -/
axiom node.t : Type

/-- Rocq `Module message. Axiom t : Type. End message.` -/
axiom message.t : Type

namespace entry
/-- Rocq `entry.t`. -/
abbrev t : Type := List w8
end entry

namespace astate
/-- Rocq `astate.t`. -/
structure t where
  mk ::
  log : List entry.t
end astate

/-! ### Global definitions, not specific to a particular (generation of a) node. -/

/-- Rocq `Axiom raft_names : Type`. -/
axiom raft_names : Type

/-- Rocq `Axiom own_raft_log` (Rocq abstracts only over `Σ`). -/
axiom own_raft_log {GF : BundledGFunctors} (γ : raft_names) (log : List (List w8)) : IProp GF

/-- Rocq `Axiom is_raft_log`. -/
axiom is_raft_log {GF : BundledGFunctors} (γ : raft_names) (log : List (List w8)) : IProp GF

/-- Rocq `Axiom is_raft_log_pers`. -/
axiom is_raft_log_pers {GF : BundledGFunctors} (γ : raft_names) (log : List (List w8)) :
    Persistent (is_raft_log (GF := GF) γ log)

instance is_raft_log_pers_inst {GF : BundledGFunctors} (γ : raft_names) (log : List (List w8)) :
    Persistent (is_raft_log (GF := GF) γ log) :=
  is_raft_log_pers γ log

section countable
variable [ext : ffi_syntax] [val_countable : Pos.Countable val]

instance interface_countable : Pos.Countable interface.t :=
  .ofInjective (fun
      | .ok i => Pos.Countable.encode (val.InterfaceV (some (i.ty, i.v)))
      | .nil => Pos.Countable.encode (val.InterfaceV none))
    (by
      rintro (⟨⟨a, b⟩⟩ | _) (⟨⟨c, d⟩⟩ | _) h <;> have h := Pos.encode_inj h <;> simp_all)

end countable

section wps
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : heapGS HasLC.hasLC GF] [allG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
variable [val_countable : Pos.Countable val]

local notation "raft" => pkg_id.go_etcd_io.raft.v3

/-- Rocq `MsgProp`. -/
def MsgProp : w32 := W32 2

/-- Rocq `own_propose_message`. -/
def own_propose_message (γraft : raft_names) (pm : v3.msgWithResult.t) : IProp GF :=
  iprop(∃ (data_sl : slice.t) (data : List w8) (γch : chan_names),
    "Hmsg" ∷ ⌜pm.m'.Type' = MsgProp⌝ ∗
    "Hentries" ∷ pm.m'.Entries' ↦* [data_sl] ∗
    "data_sl" ∷ data_sl ↦* data ∗
    "Hupd" ∷ (|={⊤,∅}=> ∃ log, own_raft_log γraft log ∗
      (own_raft_log γraft (log ++ [data]) ={∅,⊤}=∗ True)) ∗
    -- FIXME: probably can only send once.
    "Hresult" ∷ is_chan_bag (V := interface.t) γch pm.result'
      (fun _ => iprop(True)))

/-- Rocq `is_node_inner` (`Local`). -/
def is_node_inner (γraft : raft_names) (n : v3.node.t) : IProp GF :=
  iprop(∃ (γp γa γd : chan_names),
    "#Hpropc" ∷ is_chan_bag (V := interface.t) γp n.propc' (fun _ => iprop(True)) ∗
    "#Hadvancec_is" ∷ is_chan n.advancec' γa Unit ∗
    "#Hadvancec" ∷ inv nroot (∃ s, own_chan γa Unit s) ∗
    "#Hdone" ∷ own_broadcast_chan n.done' γd iprop(True) broadcast.t.Unknown)

/-- Rocq `is_node`. -/
def is_node (γraft : raft_names) (n : loc) : IProp GF :=
  iprop(∃ nd : v3.node.t,
    "n_ptr" ∷ n ↦□ nd ∗
    "Hinner" ∷ is_node_inner γraft nd)

instance is_node_inner_pers (γraft : raft_names) (n : v3.node.t) :
    Persistent (is_node_inner (GF := GF) γraft n) := by
  unfold is_node_inner; infer_instance

instance is_node_pers (γraft : raft_names) (n : loc) :
    Persistent (is_node (GF := GF) γraft n) := by
  unfold is_node; infer_instance

theorem wp_node__Ready (γraft : raft_names) (n : loc) :
    {{ is_pkg_init (PROP := IProp GF) raft ∗ is_node γraft n }}
      (App (Val (n @!! go.type.PointerType v3.node @!! go!"Ready")) (Val #()))
    {{ (ready : chan.t), RET #ready; True }} := by
  wp_start as Hpre
  iNamed Hpre
  iStructNamed n_ptr
  wp_auto
  wp_end

theorem wp_node__Advance (γraft : raft_names) (n : loc) :
    {{ is_pkg_init (PROP := IProp GF) raft ∗ is_node γraft n }}
      (App (Val (n @!! go.type.PointerType v3.node @!! go!"Advance")) (Val #()))
    {{ RET #(); True }} := by
  sorry -- Rocq: Admitted

theorem wp_node__Propose (γraft : raft_names) (n : loc) (ctx : interface.t_ok)
    (ctx_desc : context.Context_desc.t (IProp GF)) (data_sl : slice.t) (data : List w8) :
    {{ is_pkg_init (PROP := IProp GF) raft ∗
        "#Hctx" ∷ context.is_Context ctx ctx_desc ∗
        "#Hnode" ∷ is_node γraft n ∗
        "#data_sl" ∷ data_sl ↦*□ data ∗
        "Hupd" ∷ (|={⊤,∅}=> ∃ log, own_raft_log γraft log ∗
          (own_raft_log γraft (log ++ [data]) ={∅,⊤}=∗ True)) }}
      (App (App (Val (n @!! go.type.PointerType v3.node @!! go!"Propose"))
        (Val #(interface.ok ctx))) (Val #data_sl))
    {{ (err : interface.t), RET #err; if err = interface.nil then True else True }} := by
  sorry -- Rocq: Admitted

end wps

end go_etcd_io.raft.v3_proof

end Perennial
