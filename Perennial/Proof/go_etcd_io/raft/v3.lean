/-
The client-facing `Node` interface.

Interface values are `n : interface.t_ok` (non-nil, as built by
`interface.mk`). The proof is FFI-generic.
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

local notation "raft" => pkg_id.go_etcd_io.raft.v3

/-- `n` is a `Node` interface value backed by a `*node` satisfying `is_node`. -/
def is_Node (γ : RaftNames) (n : GoInterfaceOk) : IProp GF :=
  iprop(∃ n_ptr : Loc,
    "%Hn" ∷ ⌜n = interface.mk (go.GoType.PointerType v3.node.ty) #n_ptr⌝ ∗
    "#Hnode" ∷ is_node γ n_ptr)

instance is_Node_pers (γ : RaftNames) (n : GoInterfaceOk) :
    Persistent (is_Node (GF := GF) γ n) := by
  unfold is_Node; infer_instance

theorem Node.wp_Propose (ctx : GoInterfaceOk) (ctx_desc : context.ContextDesc (IProp GF))
    (n : GoInterfaceOk) (γraft : RaftNames) (data_sl : GoSlice) (data : List w8) :
    {{ isPkgInit (PROP := IProp GF) raft ∗
        "#Hctx" ∷ context.isContext ctx ctx_desc ∗
        "#Hnode" ∷ is_Node γraft n ∗
        "#data_sl" ∷ data_sl ↦*□ data ∗
        "Hupd" ∷ (|={⊤,∅}=> ∃ log, ownRaftLog γraft log ∗
          (ownRaftLog γraft (log ++ [data]) ={∅,⊤}=∗ True)) }}
      (App (App (Val #(methods n.ty go!"Propose" n.v)) (Val #(interface.ok ctx))) (Val #data_sl))
    {{ (err : GoInterface), RET #err; True }} := by
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
