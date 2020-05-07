From RecordUpdate Require Import RecordSet.

From Perennial.program_proof Require Import disk_lib.
From Perennial.program_proof Require Import wal.invariant.

Section goose_lang.
Context `{!heapG Σ}.
Context `{!lockG Σ}.
Context `{!walG Σ}.

Implicit Types (v:val) (z:Z).
Implicit Types (γ: wal_names (Σ:=Σ)).
Implicit Types (s: log_state.t) (memLog: slidingM.t) (txns: list (u64 * list update.t)).
Implicit Types (pos: u64) (txn_id: nat).

Context (P: log_state.t -> iProp Σ).
Let N := walN.
Let circN := walN .@ "circ".

Theorem wp_MkLog_init d (bs: list Block) :
  {{{ 0 d↦∗ repeat block0 513 ∗
      513 d↦∗ bs ∗
      P (log_state.mk (list_to_map (imap (λ i x, (513 + Z.of_nat i, x)) bs)) [(U64 0, [])] 0 0)  }}}
    MkLog #d
  {{{ γ l, RET #l; is_wal P l γ }}}.
Proof.
Admitted.

(* this seems odd - will it really be able to recover the circular log from this
assumption? how do we make this assumption modular? *)
Theorem wp_MkLog_recover l0 d γ σ :
  {{{ is_wal_inner l0 γ σ ∗ is_circular circN (circular_pred γ) γ.(circ_name) }}}
    MkLog #d
  {{{ σ' γ' l, RET #l;
      ⌜relation.denote (log_crash) σ σ' tt⌝ ∗
      is_wal_inner l γ' σ' ∗ is_circular circN (circular_pred γ') γ'.(circ_name) }}}.
Proof.
Admitted.

End goose_lang.
