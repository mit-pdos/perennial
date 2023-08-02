From Perennial.program_proof.mvcc Require Import
     txn_prelude txn_repr db_repr db_new_txn txn_run.

Section program.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

Definition spec_body
           (body : val) (txn : loc) tid r
           (P : dbmap -> Prop) (Q : dbmap -> dbmap -> Prop)
           (Rc : dbmap -> dbmap -> iProp Σ) (Ra : dbmap -> iProp Σ)
           γ τ : iProp Σ :=
  ∀ Φ,
  own_txn txn tid r γ τ ∗ ⌜P r⌝ ∗ txnmap_ptstos τ r -∗
  (∀ ok : bool,
     (own_txn txn tid r γ τ ∗
      if ok
      then ∃ w, ⌜Q r w ∧ dom r = dom w⌝ ∗ (Rc r w ∧ Ra r) ∗ txnmap_ptstos τ w
      else Ra r) -∗ Φ #ok) -∗
  WP body #txn {{ v, Φ v }}.

Theorem wp_DB__Run
        (db : loc) (body : val)
        (P : dbmap -> Prop) (Q : dbmap -> dbmap -> Prop)
        (Rc : dbmap -> dbmap -> iProp Σ) (Ra : dbmap -> iProp Σ)
        γ :
  (∀ r w, (Decision (Q r w))) ->
  is_db db γ -∗
  {{{ ∀ txn tid r τ, spec_body body txn tid r P Q Rc Ra γ τ }}}
  <<< ∀∀ (r : dbmap), ⌜P r⌝ ∗ dbmap_ptstos γ 1 r >>>
    DB__Run #db body @ ↑mvccN
  <<< ∃∃ (ok : bool) (w : dbmap), if ok then ⌜Q r w⌝ ∗ dbmap_ptstos γ 1 w else dbmap_ptstos γ 1 r >>>
  {{{ RET #ok; if ok then Rc r w else Ra r }}}.
Proof.
  iIntros (Hdec) "#Hdb !>".
  iIntros (Φ) "Hbody HAU".
  wp_call.
  
  (*@ func (db *DB) Run(body func(txn *Txn) bool) bool {                      @*)
  (*@     txn := db.NewTxn()                                                  @*)
  (*@                                                                         @*)
  wp_apply (wp_DB__NewTxn with "Hdb").
  iIntros (txn) "Htxn".
  wp_pures.
  
  (*@     return txn.Run(body)                                                @*)
  (*@ }                                                                       @*)
  wp_apply (wp_txn__Run with "[$Htxn Hbody]"); [done | done |].
  iMod "HAU" as (r) "[[%HP Hdbpts] HAU]".
  iModIntro.
  iExists r.
  iFrame.
  iSplit; first done.
  iIntros (ok w) "Hpost".
  iMod ("HAU" $! ok w with "Hpost") as "HΦ".
  iIntros "!> [Htxn HR]".
  by iApply "HΦ".
Qed.

End program.
