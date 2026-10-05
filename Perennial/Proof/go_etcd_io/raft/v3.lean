/-
Port of `new/proof/go_etcd_io/raft/v3.v`: the client-facing `Node` interface.

Lean notes: Rocq's `n : interface.t` with `n = interface.mk ..` is
`n : interface.t_ok` here (Rocq's `interface.mk` builds a `t_ok`). Rocq also
imports `grove_prelude`, which is not needed (the proof is FFI-generic).
-/
import Perennial.Proof.go_etcd_io.raft.v3_proof.base
import Perennial.Proof.go_etcd_io.raft.v3_proof.protocol

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace go_etcd_io.raft.v3_proof

section proof
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : heapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

local notation "raft" => pkg_id.go_etcd_io.raft.v3

/-- Rocq `is_Node`. -/
def is_Node (γ : RaftNames) (n : interface.t_ok) : IProp GF :=
  iprop(∃ n_ptr : loc,
    "%Hn" ∷ ⌜n = interface.mk (go.type.PointerType v3.node) #n_ptr⌝ ∗
    "#Hnode" ∷ is_node γ n_ptr)

instance is_Node_pers (γ : RaftNames) (n : interface.t_ok) :
    Persistent (is_Node (GF := GF) γ n) := by
  unfold is_Node; infer_instance

theorem Node.wp_Propose (ctx : interface.t_ok) (ctx_desc : context.Context_desc.t (IProp GF))
    (n : interface.t_ok) (γraft : RaftNames) (data_sl : slice.t) (data : List w8) :
    {{ isPkgInit (PROP := IProp GF) raft ∗
        "#Hctx" ∷ context.isContext ctx ctx_desc ∗
        "#Hnode" ∷ is_Node γraft n ∗
        "#data_sl" ∷ data_sl ↦*□ data ∗
        "Hupd" ∷ (|={⊤,∅}=> ∃ log, ownRaftLog γraft log ∗
          (ownRaftLog γraft (log ++ [data]) ={∅,⊤}=∗ True)) }}
      (App (App (Val #(methods n.ty go!"Propose" n.v)) (Val #(interface.ok ctx))) (Val #data_sl))
    {{ (err : interface.t), RET #err; True }} := by
  wp_start_folded as Hpre
  iNamed Hpre
  iNamed Hnode
  subst Hn
  wp_apply +noauto (node.wp_Propose γraft n_ptr ctx ctx_desc data_sl data) $$ [$]
  iintro %err -
  iapply HΦ
  itrivial

end proof

end go_etcd_io.raft.v3_proof

end Perennial
