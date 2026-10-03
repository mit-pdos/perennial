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
* Deviations from Rocq (so that `wp_node__Advance` and `wp_node__Propose`,
  admitted in Rocq, are provable; their statements are unchanged): the
  invariants in `is_node_inner` (`"#Hpropc"`, `"#Hadvancec"`) and
  `own_propose_message` are changed, see their docstrings. New:
  `msgWithResult_countable`, `is_initialized_access`.
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

section wps
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : heapGS HasLC.hasLC GF] [allG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

local notation "raft" => pkg_id.go_etcd_io.raft.v3

theorem is_initialized_access :
    is_pkg_init (PROP := IProp GF) raft ⊢ v3.is_initialized :=
  is_pkg_init_access (PROP := IProp GF) raft

/-- Rocq `MsgProp`. -/
def MsgProp : w32 := W32 2

/-- `Pos.Countable` for `msgWithResult` (needed for a bag of them), through an
injection into nested pairs of its fields (Lean addition). -/
instance msgWithResult_countable : Pos.Countable v3.msgWithResult.t :=
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

/-- Rocq `own_propose_message`.

Lean deviations: Rocq has `"Hentries" ∷ pm.m'.Entries' ↦* [data_sl]` (a slice of
`Entry`s described as a slice of byte slices) and `"data_sl" ∷ data_sl ↦* data`
(full ownership, which `Propose` does not have: its precondition is
`data_sl ↦*□ data`). Here `Entries` is a one-element slice of an `Entry` whose
`Data` is `data_sl`, and `data_sl ↦*□ data`. -/
def own_propose_message (γraft : raft_names) (pm : v3.msgWithResult.t) : IProp GF :=
  iprop(∃ (data_sl : slice.t) (data : List w8) (γch : chan_names) (e : v3.raftpb.Entry.t),
    "Hmsg" ∷ ⌜pm.m'.Type' = MsgProp⌝ ∗
    "%He" ∷ ⌜e.Data' = data_sl⌝ ∗
    "Hentries" ∷ pm.m'.Entries' ↦* [e] ∗
    "#data_sl" ∷ data_sl ↦*□ data ∗
    "Hupd" ∷ (|={⊤,∅}=> ∃ log, own_raft_log γraft log ∗
      (own_raft_log γraft (log ++ [data]) ={∅,⊤}=∗ True)) ∗
    -- FIXME: probably can only send once.
    "Hresult" ∷ is_chan_bag (V := interface.t) γch pm.result'
      (fun _ => iprop(True)))

/-- Rocq `is_node_inner` (`Local`).

Lean deviations:
* `"#Hpropc"`: Rocq `is_chan_bag γp n.propc' (λ (_ : error.t), True)`, a bag at
  element type `error` (its `V` is inferred from the predicate) although `propc`
  is a `chan msgWithResult`; here a bag of `msgWithResult` whose elements are
  `own_propose_message`s (needed to send a proposal on it).
* `"#Hadvancec"`: Rocq `is_chan n.advancec' γa unit ∗ inv nroot (∃ s, own_chan γa unit s)`,
  which allows a closed `advancec` (then the send in `Advance` panics); here a
  bag (`is_chan_bag`, whose invariant excludes `Closed`) with trivial payload. -/
def is_node_inner (γraft : raft_names) (n : v3.node.t) : IProp GF :=
  iprop(∃ (γp γa γd : chan_names),
    "#Hpropc" ∷ is_chan_bag (V := v3.msgWithResult.t) γp n.propc' (own_propose_message γraft) ∗
    "#Hadvancec" ∷ is_chan_bag (V := Unit) γa n.advancec' (fun _ => iprop(True)) ∗
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
  wp_start as Hpre
  iNamed Hpre
  iNamed Hinner
  iStructNamed n_ptr
  wp_auto_lc 2
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blocking_clause_pre]
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
  · simp only [chan.blocking_clause_pre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, nd.done', γd
    isplit
    · ipureintro; rfl
    isplit
    · iapply own_broadcast_chan_is_chan $$ Hdone
    iapply broadcast_chan_receive _ _ _ _ _ $$ Hdone
    iintro ⟨_, _⟩
    wp_auto
    wp_end
  · iapply BigAndL.bigAndL_nil.2
    itrivial

/-- (Rocq: admitted. Proved here by inlining `stepWait` and
`stepWithWaitOption (wait := true)`, with the changed `is_node_inner` and
`own_propose_message`.) -/
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
  wp_start as ⟨#Hctx, #Hnode, #data_sl, Hupd⟩
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral _))) (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := v3.raftpb.Entry.t) (t := v3.raftpb.Entry)
    [{ (zero_val v3.raftpb.Entry.t) with Data' := data_sl }]
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
  iunfold is_node_inner at Hinner
  icases Hinner with ⟨%γp, %γa, %γd, #Hpropc, #Hadvancec, #Hdone⟩
  iStructNamed Hn
  wp_auto_lc 4
  ihave #Hinit := is_initialized_access $$ Hpkg
  iNamed Hinit
  wp_apply (chan.wp_make2 (V := interface.t) (W64 1)) as %res %γres ⟨#Hres_is, %Hcap, Hres_own⟩
  · ipureintro; decide
  imod start_bag (fun _ => iprop(True)) (.Buffered []) res γres trivial $$ Hres_is Hres_own with #Hres
  iunfold context.is_Context at Hctx
  iNamed Hctx
  iunfold context.is_Context_def at Hctx
  iNamed Hctx
  wp_apply HDone $$ [] as %dch %dγ #HDone_ch
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- send the proposal on `propc`
    simp only [chan.blocking_clause_pre]
    iexists v3.msgWithResult.t, inferInstance, inferInstance, inferInstance, inferInstance,
      nd.propc', γp, _
    isplit
    · ipureintro; exact ⟨rfl, rfl⟩
    isplit
    · iapply is_bag_is_chan $$ Hpropc
    iapply bag_send_au _ _ _ _ _ $$ [$Hlc1 $Hlc2] Hpropc [Hsl Hupd] [-]
    · unfold own_propose_message
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
      simp only [chan.blocking_clause_pre]
      iexists interface.t, inferInstance, inferInstance, inferInstance, inferInstance, res, γres
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
      simp only [chan.blocking_clause_pre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, dch2, dγ2
      isplit
      · ipureintro; rfl
      isplit
      · iapply context.is_Context_Done_is_chan $$ HDone_ch2
      iapply context.is_Context_Done_receive _ _ _ _ $$ HDone_ch2
      iintro _
      wp_auto
      ihave #HErr' := HErr $$ %broadcast.t.Unknown
      wp_apply HErr' as %err _
      wp_end
      rw [ite_self]; itrivial
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- the node is stopped
      simp only [chan.blocking_clause_pre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, nd.done', γd
      isplit
      · ipureintro; rfl
      isplit
      · iapply own_broadcast_chan_is_chan $$ Hdone
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
    simp only [chan.blocking_clause_pre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, dch, dγ
    isplit
    · ipureintro; rfl
    isplit
    · iapply context.is_Context_Done_is_chan $$ HDone_ch
    iapply context.is_Context_Done_receive _ _ _ _ $$ HDone_ch
    iintro _
    wp_auto
    ihave #HErr' := HErr $$ %broadcast.t.Unknown
    wp_apply HErr' as %err _
    wp_end
    rw [ite_self]; itrivial
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- the node is stopped
    simp only [chan.blocking_clause_pre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, nd.done', γd
    isplit
    · ipureintro; rfl
    isplit
    · iapply own_broadcast_chan_is_chan $$ Hdone
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
