From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.vrsm.apps Require Import exactlyonce.
From Perennial.program_proof Require Import marshal_stateless_proof.
From Perennial.program_proof.vrsm.replica Require Import definitions.
From Perennial.algebra Require Import map.

Section vsm_definitions.

Context `{sm_record:Sm.t}.
Import Sm.
Instance e : EqDecision OpType := (OpType_EqDecision).

Implicit Type γst:gname.

Class vsmG Σ :=
  VsmG {
      vsm_mapG :> mapG Σ u64 (list OpType)
    }.
Definition vsmΣ := #[mapΣ u64 (list OpType)].
Global Instance subG_vsmΣ {Σ} : subG vsmΣ Σ → vsmG Σ.
Proof. intros. solve_inG. Qed.

Context `{!gooseGlobalGS Σ, !heapGS Σ, !vsmG Σ}.

Implicit Type own_VersionedStateMachine : gname → (list OpType) → u64 → iProp Σ.

Definition is_state γst vnum ops : iProp Σ := vnum ⤳[γst]□ ops.

Definition is_Versioned_applyVolatileFn (applyVolatileFn:val) own_VersionedStateMachine : iProp Σ :=
  ∀ ops γst op op_sl op_bytes (latestVnum vnum:u64),
  {{{
        ⌜has_op_encoding op_bytes op⌝ ∗
        ⌜uint.nat vnum > uint.nat latestVnum⌝ ∗
        readonly (own_slice_small op_sl byteT (DfracOwn 1) op_bytes) ∗
        own_VersionedStateMachine γst ops latestVnum ∗
        (∀ (vnum':u64), ⌜uint.nat latestVnum <= uint.nat vnum'⌝ →
                  ⌜uint.nat vnum' < uint.nat vnum⌝ → is_state γst vnum' ops) ∗
        is_state γst vnum (ops ++ [op])
  }}}
    applyVolatileFn (slice_val op_sl) #vnum
  {{{
        reply_sl q, RET (slice_val reply_sl);
        own_VersionedStateMachine γst (ops ++ [op]) vnum ∗
        own_slice_small reply_sl byteT (DfracOwn q) (compute_reply ops op)
  }}}
.

Definition is_Versioned_setStateFn (setStateFn:val) own_VersionedStateMachine : iProp Σ :=
  ∀ ops_prev ops snap snap_sl (latestVnum:u64) γst γst' vnum,
  {{{
        ⌜has_snap_encoding snap ops⌝ ∗
        readonly (own_slice_small snap_sl byteT (DfracOwn 1) snap) ∗
        own_VersionedStateMachine γst ops_prev latestVnum ∗
        is_state γst' vnum ops
  }}}
    setStateFn (slice_val snap_sl) #vnum
  {{{
        RET #(); own_VersionedStateMachine γst' (ops) vnum
  }}}
.

Definition is_Versioned_getStateFn (getStateFn:val) own_VersionedStateMachine : iProp Σ :=
  ∀ ops γst latestVnum,
  {{{
        own_VersionedStateMachine γst ops latestVnum
  }}}
    getStateFn #()
  {{{
        snap snap_sl, RET (slice_val snap_sl); own_VersionedStateMachine γst ops latestVnum ∗
        ⌜has_snap_encoding snap ops⌝ ∗
        readonly (own_slice_small snap_sl byteT (DfracOwn 1) snap)
  }}}
.

Definition is_Versioned_applyReadonlyFn (applyReadonlyFn:val) own_VersionedStateMachine : iProp Σ :=
  ∀ ops op op_sl op_bytes γst latestVnum,
  {{{
        ⌜is_readonly_op op⌝ ∗
        ⌜has_op_encoding op_bytes op⌝ ∗
        readonly (own_slice_small op_sl byteT (DfracOwn 1) op_bytes) ∗
        own_VersionedStateMachine γst ops latestVnum
  }}}
    applyReadonlyFn (slice_val op_sl)
  {{{
        reply_sl q (lastModifiedVnum:u64),
        RET (#lastModifiedVnum, slice_val reply_sl);
        ⌜uint.nat lastModifiedVnum <= uint.nat latestVnum⌝ ∗
        own_VersionedStateMachine γst ops latestVnum ∗
        own_slice_small reply_sl byteT (DfracOwn q) (compute_reply ops op) ∗
        □(∀ (vnum:u64), ⌜uint.nat vnum < uint.nat latestVnum⌝ → ⌜uint.nat lastModifiedVnum <= uint.nat vnum⌝ →
            ∃ someOps, is_state γst vnum someOps ∗
                       ⌜compute_reply someOps op = compute_reply ops op⌝)
  }}}
.

Definition is_VersionedStateMachine (sm:loc) own_VersionedStateMachine : iProp Σ :=
  ∃ applyVolatileFn setStateFn getStateFn applyReadonlyFn,
  "#HapplyVolatile" ∷ readonly (sm ↦[VersionedStateMachine :: "ApplyVolatile"] applyVolatileFn) ∗
  "#HapplyVolatile_spec" ∷ is_Versioned_applyVolatileFn applyVolatileFn own_VersionedStateMachine ∗

  "#HsetState" ∷ readonly (sm ↦[VersionedStateMachine :: "SetState"] setStateFn) ∗
  "#HsetState_spec" ∷ is_Versioned_setStateFn setStateFn own_VersionedStateMachine ∗

  "#HgetState" ∷ readonly (sm ↦[VersionedStateMachine :: "GetState"] getStateFn) ∗
  "#HgetState_spec" ∷ is_Versioned_getStateFn getStateFn own_VersionedStateMachine ∗

  "#HapplyReadonly" ∷ readonly (sm ↦[VersionedStateMachine :: "ApplyReadonly"] applyReadonlyFn) ∗
  "#HapplyReadonly_spec" ∷ is_Versioned_applyReadonlyFn applyReadonlyFn own_VersionedStateMachine
.

End vsm_definitions.
