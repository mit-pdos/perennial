/-
The (axiomatized) abstract raft log and specifications of `node.Ready`, `node.Advance` and
`node.Propose`.

Notes:
* Everything lives in `namespace go_etcd_io.raft.v3_proof`, so the axiomatized
  types `Node`/`Message` do not clash with the generated
  `go_etcd_io.raft.v3.node`. Generated raft names are written `v3.node`, ...
* The broadcast and bag idioms fix `hlc := HasLC.hasLC` and need `[allG GF]`.
* The invariants in `isNodeInner` (`"#Hpropc"`, `"#Hadvancec"`) and
  `ownProposeMessage` are chosen so that `node.wp_Advance` and
  `node.wp_Propose` are provable; see their docstrings.
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

/-- Abstract type of raft nodes. -/
axiom Node : Type

/-- Abstract type of raft messages. -/
axiom Message : Type

/-- A log entry. -/
abbrev Entry : Type := List w8

/-- The abstract state: the log. -/
structure AState where
  mk ::
  log : List Entry

/-! ### Global definitions, not specific to a particular (generation of a) node. -/

/-- Ghost names of a raft instance. -/
axiom RaftNames : Type

/-- Ownership of the abstract raft log. -/
axiom ownRaftLog {GF : BundledGFunctors} (γ : RaftNames) (log : List (List w8)) : IProp GF

/-- Persistent knowledge about the abstract raft log. -/
axiom isRaftLog {GF : BundledGFunctors} (γ : RaftNames) (log : List (List w8)) : IProp GF

axiom isRaftLog_pers {GF : BundledGFunctors} (γ : RaftNames) (log : List (List w8)) :
    Persistent (isRaftLog (GF := GF) γ log)

instance isRaftLog_pers_inst {GF : BundledGFunctors} (γ : RaftNames) (log : List (List w8)) :
    Persistent (isRaftLog (GF := GF) γ log) :=
  isRaftLog_pers γ log

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

local notation "raft" => pkg_id.go_etcd_io.raft.v3

theorem isInitialized_access :
    isPkgInit (PROP := IProp GF) raft ⊢ v3.isInitialized :=
  isPkgInit_access (PROP := IProp GF) raft

/-- The message type of a proposal. -/
def MsgProp : w32 := W32 2

/-- `Pos.Countable` for `msgWithResult` (needed for a bag of them), through an
injection into nested pairs of its fields. -/
instance msgWithResult_countable : Pos.Countable v3.msgWithResult :=
  .ofInjective (fun pm =>
      let m := pm.m'
      Pos.Countable.encode ((m.Type', m.To', m.From', m.Term', m.LogTerm', m.Index', m.Entries'),
        (m.Commit', m.Vote', m.Snapshot', m.Reject', m.RejectHint', m.Context', m.Responses'),
        pm.result'))
    (by
      rintro ⟨⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _⟩, _⟩
        ⟨⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _⟩, _⟩ h
      have h := Pos.encode_inj h
      simp only [Prod.mk.injEq] at h
      obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, ⟨h8, h9, h10, h11, h12, h13, h14⟩, h15⟩ := h
      subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
      rfl)

/-- Ownership of a proposal message carrying `data`.

`Entries` is a one-element slice of an `Entry` whose `Data` is `data_sl`, and
`data_sl ↦*□ data` is persistent (not full ownership, which `Propose` does not
have: its precondition is `data_sl ↦*□ data`). -/
def ownProposeMessage (γraft : RaftNames) (pm : v3.msgWithResult) : IProp GF :=
  iprop(∃ (data_sl : GoSlice) (data : List w8) (γch : ChanNames) (e : v3.raftpb.Entry),
    "Hmsg" ∷ ⌜pm.m'.Type' = MsgProp⌝ ∗
    "%He" ∷ ⌜e.Data' = data_sl⌝ ∗
    "Hentries" ∷ pm.m'.Entries' ↦* [e] ∗
    "#data_sl" ∷ data_sl ↦*□ data ∗
    "Hupd" ∷ (|={⊤,∅}=> ∃ log, ownRaftLog γraft log ∗
      (ownRaftLog γraft (log ++ [data]) ={∅,⊤}=∗ True)) ∗
    -- FIXME: probably can only send once.
    "Hresult" ∷ isChanBag (V := GoInterface) γch pm.result'
      (fun _ => iprop(True)))

/-- The invariants of a node's channels.

* `"#Hpropc"`: a bag of `msgWithResult` whose elements are
  `ownProposeMessage`s (needed to send a proposal on it).
* `"#Hadvancec"`: a bag (`isChanBag`, whose invariant excludes `Closed`, so the
  send in `Advance` does not panic) with trivial payload. -/
def isNodeInner (γraft : RaftNames) (n : v3.node) : IProp GF :=
  iprop(∃ (γp γa γd : ChanNames),
    "#Hpropc" ∷ isChanBag (V := v3.msgWithResult) γp n.propc' (ownProposeMessage γraft) ∗
    "#Hadvancec" ∷ isChanBag (V := Unit) γa n.advancec' (fun _ => iprop(True)) ∗
    "#Hdone" ∷ ownBroadcastChan n.done' γd iprop(True) Broadcast.Unknown)

/-- `n` points to a node satisfying `isNodeInner`. -/
def is_node (γraft : RaftNames) (n : Loc) : IProp GF :=
  iprop(∃ nd : v3.node,
    "n_ptr" ∷ n ↦□ nd ∗
    "Hinner" ∷ isNodeInner γraft nd)

instance isNodeInner_pers (γraft : RaftNames) (n : v3.node) :
    Persistent (isNodeInner (GF := GF) γraft n) := by
  unfold isNodeInner; infer_instance

instance is_node_pers (γraft : RaftNames) (n : Loc) :
    Persistent (is_node (GF := GF) γraft n) := by
  unfold is_node; infer_instance

theorem node.wp_Ready (γraft : RaftNames) (n : Loc) :
    {{ isPkgInit (PROP := IProp GF) raft ∗ is_node γraft n }}
      (App (Val (n @!! go.GoType.PointerType v3.node.ty @!! go!"Ready")) (Val #()))
    {{ (ready : GoChan), RET #ready; True }} := by
  wp_start as Hpre
  iNamed Hpre
  iStructNamed n_ptr
  wp_auto
  wp_end

theorem node.wp_Advance (γraft : RaftNames) (n : Loc) :
    {{ isPkgInit (PROP := IProp GF) raft ∗ is_node γraft n }}
      (App (Val (n @!! go.GoType.PointerType v3.node.ty @!! go!"Advance")) (Val #()))
    {{ RET #(); True }} := by
  wp_start as Hpre
  iNamed Hpre
  iNamed Hinner
  iStructNamed n_ptr
  wp_auto_lc 2
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, nd.advancec', γa, ()
    isplit
    · ipureintro; exact ⟨rfl, rfl⟩
    isplit
    · iapply is_bag_is_chan $$ Hadvancec
    iapply bag_send_au _ _ _ _ _ $$ [$Hlc1 $Hlc2] Hadvancec [] [HΦ]
    · itrivial
    inext
    wp_auto
    wp_end
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, nd.done', γd
    isplit
    · ipureintro; rfl
    isplit
    · iapply ownBroadcastChan_is_chan $$ Hdone
    iapply broadcast_chan_receive _ _ _ _ _ $$ Hdone
    iintro ⟨_, _⟩
    wp_auto
    wp_end
  · iapply BigAndL.bigAndL_nil.2
    itrivial

/-- Proved by inlining `stepWait` and `stepWithWaitOption (wait := true)`. -/
theorem node.wp_Propose (γraft : RaftNames) (n : Loc) (ctx : GoInterfaceOk)
    (ctx_desc : context.ContextDesc (IProp GF)) (data_sl : GoSlice) (data : List w8) :
    {{ isPkgInit (PROP := IProp GF) raft ∗
        "#Hctx" ∷ context.isContext ctx ctx_desc ∗
        "#Hnode" ∷ is_node γraft n ∗
        "#data_sl" ∷ data_sl ↦*□ data ∗
        "Hupd" ∷ (|={⊤,∅}=> ∃ log, ownRaftLog γraft log ∗
          (ownRaftLog γraft (log ++ [data]) ={∅,⊤}=∗ True)) }}
      (App (App (Val (n @!! go.GoType.PointerType v3.node.ty @!! go!"Propose"))
        (Val #(interface.ok ctx))) (Val #data_sl))
    {{ (err : GoInterface), RET #err; if err = interface.nil then True else True }} := by
  wp_start as ⟨#Hctx, #Hnode, #data_sl, Hupd⟩
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral _))) (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := v3.raftpb.Entry) (t := v3.raftpb.Entry.ty)
    [{ (zero_val v3.raftpb.Entry) with Data' := data_sl }]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %sl_ptr ⟨Hsl, -⟩
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  iunfold is_node at Hnode
  icases Hnode with ⟨%nd, #Hn, #Hinner⟩
  iunfold isNodeInner at Hinner
  icases Hinner with ⟨%γp, %γa, %γd, #Hpropc, #Hadvancec, #Hdone⟩
  iStructNamed Hn
  wp_auto_lc 4
  ihave #Hinit := isInitialized_access $$ Hpkg
  iNamed Hinit
  wp_apply (chan.wp_make2 (V := GoInterface) (W64 1)) as %res %γres ⟨#Hres_is, %Hcap, Hres_own⟩
  · ipureintro; decide
  imod start_bag (fun _ => iprop(True)) (.Buffered []) res γres trivial $$ Hres_is Hres_own with #Hres
  iunfold context.isContext at Hctx
  iNamed Hctx
  iunfold context.isContextDef at Hctx
  iNamed Hctx
  wp_apply HDone $$ [] as %dch %dγ #HDone_ch
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- send the proposal on `propc`
    simp only [chan.blockingClausePre]
    iexists v3.msgWithResult, inferInstance, inferInstance, inferInstance, inferInstance,
      nd.propc', γp, _
    isplit
    · ipureintro; exact ⟨rfl, rfl⟩
    isplit
    · iapply is_bag_is_chan $$ Hpropc
    iapply bag_send_au _ _ _ _ _ $$ [$Hlc1 $Hlc2] Hpropc [Hsl Hupd] [-]
    · unfold ownProposeMessage
      iexists data_sl, data, γres, _
      iframe # ∗
      ipureintro; exact ⟨rfl, rfl⟩
    inext
    wp_auto
    wp_apply HDone $$ [] as %dch2 %dγ2 #HDone_ch2
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- the result arrives
      simp only [chan.blockingClausePre]
      iexists GoInterface, inferInstance, inferInstance, inferInstance, inferInstance, res, γres
      isplit
      · ipureintro; rfl
      isplit
      · iapply is_bag_is_chan $$ Hres
      iapply bag_recv_au _ _ _ _ $$ [$Hlc3 $Hlc4] Hres
      inext
      iintro %v _
      wp_auto
      cases v
      all_goals
        wp_auto
        wp_end
        rw [ite_self]; itrivial
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- `ctx.Done()` is closed
      simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, dch2, dγ2
      isplit
      · ipureintro; rfl
      isplit
      · iapply context.isContextDone_is_chan $$ HDone_ch2
      iapply context.isContextDone_receive _ _ _ _ $$ HDone_ch2
      iintro _
      wp_auto
      ihave #HErr' := HErr $$ %Broadcast.Unknown
      wp_apply HErr' as %err _
      wp_end
      rw [ite_self]; itrivial
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- the node is stopped
      simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, nd.done', γd
      isplit
      · ipureintro; rfl
      isplit
      · iapply ownBroadcastChan_is_chan $$ Hdone
      iapply broadcast_chan_receive _ _ _ _ _ $$ Hdone
      iintro ⟨_, _⟩
      wp_auto
      wp_end
      rw [ite_self]; itrivial
    · iapply BigAndL.bigAndL_nil.2
      itrivial
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `ctx.Done()` is closed
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, dch, dγ
    isplit
    · ipureintro; rfl
    isplit
    · iapply context.isContextDone_is_chan $$ HDone_ch
    iapply context.isContextDone_receive _ _ _ _ $$ HDone_ch
    iintro _
    wp_auto
    ihave #HErr' := HErr $$ %Broadcast.Unknown
    wp_apply HErr' as %err _
    wp_end
    rw [ite_self]; itrivial
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- the node is stopped
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, nd.done', γd
    isplit
    · ipureintro; rfl
    isplit
    · iapply ownBroadcastChan_is_chan $$ Hdone
    iapply broadcast_chan_receive _ _ _ _ _ $$ Hdone
    iintro ⟨_, _⟩
    wp_auto
    wp_end
    rw [ite_self]; itrivial
  · iapply BigAndL.bigAndL_nil.2
    itrivial

end wps

end go_etcd_io.raft.v3_proof

end Perennial
