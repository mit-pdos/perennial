From Perennial.program_proof Require Export grove_prelude marshal_stateless_proof.
(* From Goose.github_com.mit_pdos.vmvcc Require Export tpcc_deprecated. *)
Export Perennial.goose_lang.lib.slice.typed_slice.

Definition dbval := option (list u8).
Notation Nil := (None : dbval).
Notation Value x := (Some x : dbval).

Definition to_dbval (b : bool) (v : list u8) :=
  if b then Value v else Nil.

Definition dbmaps := gmap (u64 * (list u8)) dbval.

Section program.
Context `{!heapGS Σ}.

Definition own_txn (txn : loc) (tid : nat) (view : dbmaps) (γ τ : gname) : iProp Σ.
Admitted.

Definition own_txn_uninit (txn : loc) (γ : gname) : iProp Σ.
Admitted.

Definition txnmaps_ptsto (τ : gname) (mapid : u64) (k : list u8) (v : dbval) : iProp Σ.
Admitted.

Definition txnmaps_ptstos τ (ms : dbmaps) : iProp Σ :=
  [∗ map] x ↦ v ∈ ms, txnmaps_ptsto τ x.1 x.2 v.

Definition dbmaps_ptsto (γ : gname) (mapid : u64) (k : list u8) (q : Qp) (v : dbval) : iProp Σ.
Admitted.

Definition dbmaps_ptstos γ q (ms : dbmaps) : iProp Σ :=
  [∗ map] x ↦ v ∈ ms, dbmaps_ptsto γ x.1 x.2 q v.

(* Axiomatized transaction interface. *)
Definition spec_body
           (body : val) (txn : loc) (tid : nat) (r : dbmaps)
           (P : dbmaps -> Prop) (Q : dbmaps -> dbmaps -> Prop)
           (Rc : dbmaps -> dbmaps -> iProp Σ) (Ra : dbmaps -> iProp Σ)
           γ τ : iProp Σ :=
  ∀ Φ,
  own_txn txn tid r γ τ ∗ ⌜P r⌝ ∗ txnmaps_ptstos τ r -∗
  (∀ ok : bool,
     (own_txn txn tid r γ τ ∗
      if ok
      then ∃ w, ⌜Q r w ∧ dom r = dom w⌝ ∗ (Rc r w ∧ Ra r) ∗ txnmaps_ptstos τ w
      else Ra r) -∗ Φ #ok) -∗
  WP body #txn {{ v, Φ v }}.

Theorem wp_txn__DoTxn
        txn (body : val)
        (P : dbmaps -> Prop) (Q : dbmaps -> dbmaps -> Prop)
        (Rc : dbmaps -> dbmaps -> iProp Σ) (Ra : dbmaps -> iProp Σ)
        γ :
  (∀ r w, (Decision (Q r w))) ->
  ⊢ {{{ own_txn_uninit txn γ ∗ (∀ tid r τ, spec_body body txn tid r P Q Rc Ra γ τ) }}}
    <<< ∀∀ (r : dbmaps), ⌜P r⌝ ∗ dbmaps_ptstos γ 1 r >>>
      Txn__DoTxn #txn body @ ⊤
    <<< ∃∃ (ok : bool) (w : dbmaps), if ok then ⌜Q r w⌝ ∗ dbmaps_ptstos γ 1 w else dbmaps_ptstos γ 1 r >>>
    {{{ RET #ok; own_txn_uninit txn γ ∗ if ok then Rc r w else Ra r }}}.
Admitted.

Definition spec_body_readonly
           (body : val) (txn : loc) tid r
           (P : dbmaps -> Prop) (Rc Ra : dbmaps -> iProp Σ)
           γ τ : iProp Σ :=
  ∀ Φ,
  own_txn txn tid r γ τ ∗ ⌜P r⌝ ∗ txnmaps_ptstos τ r -∗
  (∀ ok : bool,
     own_txn txn tid r γ τ ∗ txnmaps_ptstos τ r ∗
     (if ok then (Rc r ∧ Ra r) else Ra r) -∗ Φ #ok) -∗
  WP body #txn {{ v, Φ v }}.

Theorem wp_txn__DoTxn_readonly
        txn (body : val) (P : dbmaps -> Prop) (Rc Ra : dbmaps -> iProp Σ) γ :
  ⊢ {{{ own_txn_uninit txn γ ∗ (∀ tid r τ, spec_body_readonly body txn tid r P Rc Ra γ τ) }}}
    <<< ∀∀ (r : dbmaps), ⌜P r⌝ ∗ dbmaps_ptstos γ 1 r >>>
      Txn__DoTxn #txn body @ ⊤
    <<< dbmaps_ptstos γ 1 r >>>
    {{{ (ok : bool), RET #ok; own_txn_uninit txn γ ∗ if ok then Rc r else Ra r }}}.
Admitted.

Definition spec_body_xres_readonly
           (body : val) (txn : loc) tid r
           (P : dbmaps -> Prop) γ τ : iProp Σ :=
  ∀ Φ,
  own_txn txn tid r γ τ ∗ ⌜P r⌝ ∗ txnmaps_ptstos τ r -∗
  (∀ ok : bool,
     own_txn txn tid r γ τ ∗ txnmaps_ptstos τ r -∗ Φ #ok) -∗
  WP body #txn {{ v, Φ v }}.

Theorem wp_txn__DoTxn_xres_readonly
        txn (body : val) (P : dbmaps -> Prop) γ :
  ⊢ {{{ own_txn_uninit txn γ ∗ (∀ tid r τ, spec_body_xres_readonly body txn tid r P γ τ) }}}
    <<< ∀∀ (r : dbmaps), ⌜P r⌝ ∗ dbmaps_ptstos γ 1 r >>>
      Txn__DoTxn #txn body @ ⊤
    <<< dbmaps_ptstos γ 1 r >>>
    {{{ (ok : bool), RET #ok; own_txn_uninit txn γ }}}.
Admitted.

Theorem wp_txn__Read
        txn (mid : u64) (key : Slice.t)
        (k : list u8) tid view dbv γ τ :
  {{{ own_txn txn tid view γ τ ∗ txnmaps_ptsto τ mid k dbv ∗
      own_slice key byteT 1 k
  }}}
    Txn__Read #txn #mid (to_val key)
  {{{ (vS : Slice.t) (found : bool) (v : list u8), RET (to_val vS, #found);
      own_txn txn tid view γ τ ∗ txnmaps_ptsto τ mid k dbv ∗
      own_slice key byteT 1 k ∗ own_slice vS byteT 1 v ∗ ⌜dbv = to_dbval found v⌝
  }}}.
Admitted.

Theorem wp_txn__Write
        txn (mid : u64) (key value : Slice.t)
        (k v : list u8) tid view dbv γ τ :
  {{{ own_txn txn tid view γ τ ∗ txnmaps_ptsto τ mid k dbv ∗
      own_slice key byteT 1 k ∗ own_slice value byteT 1 v
  }}}
    Txn__Write #txn #mid (to_val key) (to_val value)
  {{{ RET #();
      own_txn txn tid view γ τ ∗ txnmaps_ptsto τ mid k (Value v)
  }}}.
Admitted.

Theorem wp_txn__Delete
        txn (mid : u64) (key : Slice.t)
        (k : list u8) tid view dbv γ τ :
  {{{ own_txn txn tid view γ τ ∗ txnmaps_ptsto τ mid k dbv ∗
      own_slice key byteT 1 k
  }}}
    Txn__Delete #txn #mid (to_val key)
  {{{ RET #();
      own_txn txn tid view γ τ ∗ txnmaps_ptsto τ mid k Nil
  }}}.
Admitted.

End program.
