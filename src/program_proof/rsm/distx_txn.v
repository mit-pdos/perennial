From Perennial.program_proof.rsm Require Import distx distx_replicagroup.
From Goose.github_com.mit_pdos.rsm Require Import distx.

Section program.
  Context `{!heapGS Σ, !distx_ghostG Σ}.

  Definition txn_ptsto (τ : gname) (k : dbkey) (v : dbval) : iProp Σ.
  Admitted.

  Definition txn_ptstos (τ : gname) (m : dbmap) : iProp Σ :=
    [∗ map] k ↦ v ∈ m, txn_ptsto τ k v.

  Definition own_txn_uninit (txn : loc) (γ : distx_names) : iProp Σ.
  Admitted.

  (* TODO: we didn't expose [view] as in vMVCC, is that an issue? *)
  Definition own_txn (txn : loc) (tid : nat) (γ : distx_names) (τ : gname) : iProp Σ.
  Admitted.

  Theorem wp_Txn__Delete (txn : loc) (tid : nat) (key : string) (value : dbval) γ τ :
    {{{ own_txn txn tid γ τ ∗ txn_ptsto τ key value }}}
      Txn__Delete #txn #(LitString key)
    {{{ RET #(); own_txn txn tid γ τ ∗ txn_ptsto τ key None }}}.
  Proof.
    (*@ func (txn *Txn) Delete(key string) {                                    @*)
    (*@     // TODO                                                             @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_Txn__abort (txn : loc) (tid : nat) (γ : distx_names) (τ : gname) :
    txnres_abt γ tid -∗
    {{{ own_txn txn tid γ τ }}}
      Txn__abort #txn
    {{{ RET #(); own_txn_uninit txn γ }}}.
  Proof.
    (*@ func (txn *Txn) abort() {                                               @*)
    (*@     for _, rg := range(txn.rgs) {                                       @*)
    (*@         // Should abort in parallel.                                    @*)
    (*@         if uint64(len(rg.wrs)) != 0 {                                   @*)
    (*@             rg.Abort(txn.ts)                                            @*)
    (*@         }                                                               @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_Txn__commit (txn : loc) (tid : nat) (wrs : dbmap) (γ : distx_names) (τ : gname) :
    txnres_cmt γ tid wrs -∗
    {{{ own_txn txn tid γ τ }}}
      Txn__commit #txn
    {{{ RET #(); own_txn_uninit txn γ }}}.
  Proof.
    (*@ func (txn *Txn) commit() {                                              @*)
    (*@     for _, rg := range(txn.rgs) {                                       @*)
    (*@         // Should commit in parallel.                                   @*)
    (*@         if uint64(len(rg.wrs)) != 0 {                                   @*)
    (*@             rg.Commit(txn.ts)                                           @*)
    (*@         }                                                               @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_Txn__begin (txn : loc) (γ : distx_names) :
    ⊢ {{{ own_txn_uninit txn γ }}}
      <<< ∀∀ (ts : nat), ts_auth γ ts >>>
        Txn__begin #txn @ ↑distxN
      <<< ∃∃ (ts' : nat), ts_auth γ ts' ∗ ⌜(ts < ts')%nat⌝ >>>
      {{{ RET #(); ∃ τ, own_txn txn ts' γ τ }}}.
  Proof.
    (*@ func (txn *Txn) begin() {                                               @*)
    (*@     // TODO                                                             @*)
    (*@     // Ghost action: Linearize.                                         @*)
    (*@     txn.ts = GetTS()                                                    @*)
    (*@ }                                                                       @*)
  Admitted.

  Definition logs_txnst (ts : nat) (st : txnst) (logs : gmap groupid dblog) :=
    match st with
    | StPrepared wrs => all_prepared ts wrs logs
    | StCommitted => True
    | StAborted => some_aborted ts logs
    end.

  Definition groups_txnst γ (ts : nat) (st : txnst) : iProp Σ :=
    ∃ logs,
      clog_lbs γ logs ∧ ⌜logs_txnst ts st logs⌝.

  Theorem wp_Txn__prepare (txn : loc) (tid : nat) (γ : distx_names) (τ : gname) :
    {{{ own_txn txn tid γ τ }}}
      Txn__prepare #txn
    {{{ (status : txnst), RET #(txnst_to_u64 status);
        own_txn txn tid γ τ ∗ groups_txnst γ tid status
    }}}.
  Proof.
    (*@ func (txn *Txn) prepare() uint64 {                                      @*)
    (*@     var status = TXN_PREPARED                                           @*)
    (*@     var gid uint64 = 0                                                  @*)
    (*@                                                                         @*)
    (*@     for gid < uint64(len(txn.rgs)) {                                    @*)
    (*@         rg := txn.rgs[gid]                                              @*)
    (*@                                                                         @*)
    (*@         if uint64(len(rg.wrs)) == 0 {                                   @*)
    (*@             continue                                                    @*)
    (*@         }                                                               @*)
    (*@                                                                         @*)
    (*@         status = rg.Prepare(txn.ts)                                     @*)
    (*@         if status != TXN_PREPARED {                                     @*)
    (*@             break                                                       @*)
    (*@         }                                                               @*)
    (*@                                                                         @*)
    (*@         gid++                                                           @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    (*@     return status                                                       @*)
    (*@ }                                                                       @*)
  Admitted.

  Definition spec_body
    (body : val) (txn : loc) tid r
    (P : dbmap -> Prop) (Q : dbmap -> dbmap -> Prop)
    (Rc : dbmap -> dbmap -> iProp Σ) (Ra : dbmap -> iProp Σ)
    γ τ : iProp Σ :=
    ∀ Φ,
    own_txn txn tid γ τ ∗ ⌜P r⌝ ∗ txn_ptstos τ r -∗
    (∀ ok : bool,
       (own_txn txn tid γ τ ∗
        if ok
        then ∃ w, ⌜Q r w ∧ dom r = dom w⌝ ∗ (Rc r w ∧ Ra r) ∗ txn_ptstos τ w
        else Ra r) -∗ Φ #ok) -∗
    WP body #txn {{ v, Φ v }}.

  Theorem wp_Txn__Run
    txn (body : val)
    (P : dbmap -> Prop) (Q : dbmap -> dbmap -> Prop)
    (Rc : dbmap -> dbmap -> iProp Σ) (Ra : dbmap -> iProp Σ) γ :
    (∀ r w, (Decision (Q r w))) ->
    ⊢ {{{ own_txn_uninit txn γ ∗ (∀ tid r τ, spec_body body txn tid r P Q Rc Ra γ τ) }}}
      <<< ∀∀ (r : dbmap), ⌜P r⌝ ∗ db_ptstos γ r >>>
        Txn__Run #txn body @ ↑distxN
      <<< ∃∃ (ok : bool) (w : dbmap), if ok then ⌜Q r w⌝ ∗ db_ptstos γ w else db_ptstos γ r >>>
      {{{ RET #ok; own_txn_uninit txn γ ∗ if ok then Rc r w else Ra r }}}.
  Proof.
    (*@ func (txn *Txn) Run(body func(txn *Txn) bool) bool {                    @*)
    (*@     txn.begin()                                                         @*)
    (*@     cmt := body(txn)                                                    @*)
    (*@     if !cmt {                                                           @*)
    (*@         // This transaction has not really requested to prepare yet, so no @*)
    (*@         // cleanup tasks are required.                                  @*)
    (*@         return false                                                    @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    (*@     status := txn.prepare()                                             @*)
    (*@                                                                         @*)
    (*@     if status == TXN_COMMITTED {                                        @*)
    (*@         // A backup coordinator must have committed this transaction, so there's @*)
    (*@         // nothing we need to do here.                                  @*)
    (*@         return true                                                     @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    (*@     if status == TXN_ABORTED {                                          @*)
    (*@         // Ghost action: Abort this transaction.                        @*)
    (*@         txn.abort()                                                     @*)
    (*@         return false                                                    @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    (*@     // Ghost action: Commit this transaction.                           @*)
    (*@     txn.commit()                                                        @*)
    (*@     return true                                                         @*)
    (*@ }                                                                       @*)
  Admitted.

End program.
