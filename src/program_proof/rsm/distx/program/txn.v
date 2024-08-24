From Perennial.program_proof.rsm.distx Require Import prelude.
From Perennial.program_proof.rsm.distx.program Require Import replica_group.
From Perennial.program_proof.rsm.distx.invariance Require Import linearize.
From Goose.github_com.mit_pdos.rsm Require Import distx.

Section program.
  Context `{!heapGS Σ, !distx_ghostG Σ}.

  Definition txnmap_auth (τ : gname) (m : dbmap) : iProp Σ.
  Admitted.

  Definition txnmap_ptsto (τ : gname) (k : dbkey) (v : dbval) : iProp Σ.
  Admitted.

  Definition txnmap_ptstos (τ : gname) (m : dbmap) : iProp Σ :=
    [∗ map] k ↦ v ∈ m, txnmap_ptsto τ k v.

  Lemma txnmap_alloc m :
    ⊢ |==> ∃ τ, txnmap_auth τ m ∗ ([∗ map] k ↦ v ∈ m, txnmap_ptsto τ k v).
  Admitted.

  Definition own_txn_uninit (txn : loc) (γ : distx_names) : iProp Σ.
  Admitted.

  Definition own_txn_init (txn : loc) (tid : nat) (γ : distx_names) : iProp Σ.
  Admitted.

  (* TODO: we didn't expose [view] as in vMVCC, is that an issue? *)
  Definition own_txn (txn : loc) (tid : nat) (γ : distx_names) (τ : gname) : iProp Σ.
  Admitted.

  Definition own_txn_ready_ptgs (txn : loc) (tid : nat) (γ : distx_names) (τ : gname) : iProp Σ.
  Admitted.

  Theorem wp_KeyToGroup (key : string) :
    {{{ True }}}
      KeyToGroup #(LitString key)
    {{{ (gid : u64), RET #gid; ⌜key_to_group key = (uint.nat gid)⌝ }}}.
  Proof.
    (*@ func KeyToGroup(key string) uint64 {                                    @*)
    (*@     // TODO                                                             @*)
    (*@     return 0                                                            @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_Txn__Read (txn : loc) (tid : nat) (key : string) (value : dbval) γ τ :
    {{{ own_txn txn tid γ τ ∗ txnmap_ptsto τ key value }}}
      Txn__Read #txn #(LitString key)
    {{{ RET (dbval_to_val value); own_txn txn tid γ τ ∗ txnmap_ptsto τ key value }}}.
  Proof.
    (*@ func (txn *Txn) Read(key string) Value {                                @*)
    (*@     gid := KeyToGroup(key)                                              @*)
    (*@                                                                         @*)
    (*@     pwrs := txn.wrs[gid]                                                @*)
    (*@     vlocal, ok := pwrs[key]                                             @*)
    (*@     if ok {                                                             @*)
    (*@         return vlocal                                                   @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    (*@     rg := txn.rgs[gid]                                                  @*)
    (*@     v := rg.Read(txn.ts, key)                                           @*)
    (*@     return v                                                            @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_Txn__Write (txn : loc) (tid : nat) (key : string) (value : string) γ τ :
    {{{ own_txn txn tid γ τ ∗ (∃ vprev, txnmap_ptsto τ key vprev) }}}
      Txn__Write #txn #(LitString key) #(LitString value)
    {{{ RET #(); own_txn txn tid γ τ ∗ txnmap_ptsto τ key (Some value) }}}.
  Proof.
    (*@ func (txn *Txn) Write(key string, value string) {                       @*)
    (*@     gid := KeyToGroup(key)                                              @*)
    (*@     pwrs := txn.wrs[gid]                                                @*)
    (*@     v := Value{                                                         @*)
    (*@         b : true,                                                       @*)
    (*@         s : value,                                                      @*)
    (*@     }                                                                   @*)
    (*@     pwrs[key] = v                                                       @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_Txn__Delete (txn : loc) (tid : nat) (key : string) (value : dbval) γ τ :
    {{{ own_txn txn tid γ τ ∗ txnmap_ptsto τ key value }}}
      Txn__Delete #txn #(LitString key)
    {{{ RET #(); own_txn txn tid γ τ ∗ txnmap_ptsto τ key None }}}.
  Proof.
    (*@ func (txn *Txn) Delete(key string) {                                    @*)
    (*@     gid := KeyToGroup(key)                                              @*)
    (*@     pwrs := txn.wrs[gid]                                                @*)
    (*@     v := Value{                                                         @*)
    (*@         b : false,                                                      @*)
    (*@     }                                                                   @*)
    (*@     pwrs[key] = v                                                       @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_Txn__abort (txn : loc) (tid : nat) (γ : distx_names) (τ : gname) :
    txnres_abt γ tid -∗
    {{{ own_txn txn tid γ τ }}}
      Txn__abort #txn
    {{{ RET #(); own_txn_uninit txn γ }}}.
  Proof.
    (*@ func (txn *Txn) abort() {                                               @*)
    (*@     for _, gid := range(txn.ptgs) {                                     @*)
    (*@         rg := txn.rgs[gid]                                              @*)
    (*@         pwrs := txn.wrs[gid]                                            @*)
    (*@                                                                         @*)
    (*@         // Should abort in parallel.                                    @*)
    (*@         if uint64(len(pwrs)) != 0 {                                     @*)
    (*@             rg.Abort(txn.ts)                                            @*)
    (*@         }                                                               @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_Txn__commit (txn : loc) (tid : nat) (wrs : dbmap) γ τ :
    txnres_cmt γ tid wrs -∗
    {{{ own_txn txn tid γ τ }}}
      Txn__commit #txn
    {{{ RET #(); own_txn_uninit txn γ }}}.
  Proof.
    (*@ func (txn *Txn) commit() {                                              @*)
    (*@     for _, gid := range(txn.ptgs) {                                     @*)
    (*@         rg := txn.rgs[gid]                                              @*)
    (*@         pwrs := txn.wrs[gid]                                            @*)
    (*@                                                                         @*)
    (*@         // Should commit in parallel.                                   @*)
    (*@         if uint64(len(pwrs)) != 0 {                                     @*)
    (*@             rg.Commit(txn.ts)                                           @*)
    (*@         }                                                               @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_Txn__begin (txn : loc) γ :
    ⊢ {{{ own_txn_uninit txn γ }}}
      <<< ∀∀ (ts : nat), ts_auth γ ts >>>
        Txn__begin #txn @ ↑tsNS
      <<< ∃∃ (ts' : nat), ts_auth γ ts' ∗ ⌜(ts < ts')%nat⌝ >>>
      {{{ RET #(); own_txn_init txn ts' γ }}}.
  Proof.
    (*@ func (txn *Txn) begin() {                                               @*)
    (*@     // TODO                                                             @*)
    (*@     // Ghost action: Linearize.                                         @*)
    (*@     txn.ts = GetTS()                                                    @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_Txn__setptgs txn tid γ τ :
    {{{ own_txn txn tid γ τ }}}
      Txn__setptgs #txn
    {{{ RET #(); own_txn_ready_ptgs txn tid γ τ }}}.
  Proof.
    (*@ func (txn *Txn) setptgs() {                                             @*)
    (*@     var ptgs []uint64 = make([]uint64, 0)                               @*)
    (*@                                                                         @*)
    (*@     for gid, pwrs := range(txn.wrs) {                                   @*)
    (*@         if uint64(len(pwrs)) != 0 {                                     @*)
    (*@             ptgs = append(ptgs, gid)                                    @*)
    (*@         }                                                               @*)
    (*@     }                                                                   @*)
    (*@     txn.ptgs = ptgs                                                     @*)
    (*@ }                                                                       @*)
  Admitted.

  Definition groups_txnst γ (ts : nat) (st : txnst) : iProp Σ :=
    match st with
    | StPrepared wrs => all_prepared γ ts wrs
    | StCommitted => (∃ wrs, txnres_cmt γ ts wrs)
    | StAborted => txnres_abt γ ts
    end.

  Theorem wp_Txn__prepare txn tid γ τ :
    {{{ own_txn txn tid γ τ }}}
      Txn__prepare #txn
    {{{ (status : txnst), RET #(txnst_to_u64 status);
        own_txn_ready_ptgs txn tid γ τ ∗ groups_txnst γ tid status
    }}}.
  Proof.
    (*@ func (txn *Txn) prepare() uint64 {                                      @*)
    (*@     var status = TXN_PREPARED                                           @*)
    (*@                                                                         @*)
    (*@     txn.setptgs()                                                       @*)
    (*@                                                                         @*)
    (*@     var i uint64 = 0                                                    @*)
    (*@     for i < uint64(len(txn.ptgs)) {                                     @*)
    (*@         gid := txn.ptgs[i]                                              @*)
    (*@         rg := txn.rgs[gid]                                              @*)
    (*@         pwrs := txn.wrs[gid]                                            @*)
    (*@                                                                         @*)
    (*@         status = rg.Prepare(txn.ts, slicem(pwrs))                       @*)
    (*@         if status != TXN_PREPARED {                                     @*)
    (*@             break                                                       @*)
    (*@         }                                                               @*)
    (*@                                                                         @*)
    (*@         i++                                                             @*)
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
    own_txn txn tid γ τ ∗ ⌜P r⌝ ∗ txnmap_ptstos τ r -∗
    (∀ ok : bool,
       (own_txn txn tid γ τ ∗
        if ok
        then ∃ w, ⌜Q r w ∧ dom w ⊆ dom r⌝ ∗ (Rc r w ∧ Ra r) ∗ txnmap_ptstos τ w
        else Ra r) -∗ Φ #ok) -∗
    WP body #txn {{ v, Φ v }}.

  Theorem wp_Txn__Run
    txn (body : val)
    (P : dbmap -> Prop) (Q : dbmap -> dbmap -> Prop)
    (Rc : dbmap -> dbmap -> iProp Σ) (Ra : dbmap -> iProp Σ) γ :
    (∀ r w, (Decision (Q r w))) ->
    know_distx_inv γ -∗
    {{{ own_txn_uninit txn γ ∗ (∀ tid r τ, spec_body body txn tid r P Q Rc Ra γ τ) }}}
    <<< ∀∀ (r : dbmap), ⌜P r⌝ ∗ db_ptstos γ r >>>
      Txn__Run #txn body @ ↑sysNS
    <<< ∃∃ (ok : bool) (w : dbmap), if ok then ⌜Q r w⌝ ∗ db_ptstos γ (w ∪ r) else db_ptstos γ r >>>
    {{{ RET #ok; own_txn_uninit txn γ ∗ if ok then Rc r w else Ra r }}}.
  Proof.
    iIntros (Hdec) "#Hinv !>".
    iIntros (Φ) "[Htxn Hbody] HAU".
    wp_rec. wp_pures.

    (*@ func (txn *Txn) Run(body func(txn *Txn) bool) bool {                    @*)
    (*@     txn.begin()                                                         @*)
    (*@                                                                         @*)
    wp_apply (wp_Txn__begin with "Htxn").
    iInv "Hinv" as "> HinvO" "HinvC".
    iMod (ncfupd_mask_subseteq (⊤ ∖ ↑sysNS)) as "Hclose"; first solve_ndisj.
    iMod "HAU" as (r) "[[%HP Hdbpts] HAUC]".
    iModIntro.
    iNamed "HinvO".
    iDestruct (txnsys_inv_expose_future_extract_ts with "Htxn") as (future ts) "[Htxn Hts]".
    (* Prove [key_inv] are linearizable after [ts]. *)
    iDestruct (keys_inv_before_linearize with "Hkeys Hts") as "[Hkeys Hts]".
    iExists ts.
    (* Pass [ts_auth γ ts] to the underlying layer. *)
    iFrame "Hts".
    iIntros (tid) "[Hts %Htidgt]".
    iDestruct (ts_witness with "Hts") as "#Htidlb".

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
    pose proof (peek_spec future tid) as Hpeek.
    destruct (peek future tid).
    { (* Case: No commit of timestamp [ts] in the future. *)
      iMod (txnsys_inv_linearize_abort NC Q with "Htidlb Hdbpts Htxn Hkeys")
        as "(Hdbpts & Htxn & Hkeys & Hwrsexcl & #HQ & #Hlnrzs & #Hlnrzed)".
      { (* TODO: Prove [dom r ⊆ keys_all]. *) admit. }
      { apply Htidgt. }
      { apply Hpeek. }
      { done. }
      (* Choose the will-abort branch. Use [∅] as placeholder. *)
      iMod ("HAUC" $! false ∅ with "Hdbpts") as "HΦ".
      iMod "Hclose" as "_".
      iMod ("HinvC" with "[Htxn Hkeys Hgroups]") as "_".
      { admit. }
      (* Allocate transaction local view [txnmap_ptstos τ r]. *)
      iMod (txnmap_alloc r) as (τ) "[Htxnmap Htxnpts]".
      iIntros "!> Htxn".
      iAssert (own_txn txn tid γ τ)%I with "[Htxn Htxnmap]" as "Htxn".
      { admit. }
      wp_apply ("Hbody" with "[$Htxn $Htxnpts]"); first done.
      iIntros (cmt) "[Htxn Hpost]".
      wp_pures.
      wp_if_destruct.
      { iApply "HΦ".
        (* TODO: weaken [own_txn] to [own_txn_uninit]. *)
        admit.
      }
      wp_apply (wp_Txn__prepare with "Htxn").
      iIntros (status) "[Htxn Hstatus]".
  Admitted.

End program.
