From iris.algebra Require Import dfrac_agree.
From iris.algebra.lib Require Import mono_nat mono_list gmap_view.
From Perennial.program_proof Require Import disk_prelude.

Definition dbval := option u64.
Notation Nil := (None : dbval).
Notation Value x := (Some x : dbval).

Definition N_TXN_SITES : Z := 64.

Definition sids_all := U64 <$> seqZ 0 N_TXN_SITES.

(* Logical version chain. *)
Local Definition vchainR := mono_listR (leibnizO dbval).
Local Definition key_vchainR := gmapR u64 vchainR.
(* GC-related ghost states. *)
Local Definition tidsR := gmap_viewR u64 (leibnizO unit).
Local Definition sid_tidsR := gmapR u64 tidsR.
Local Definition sid_min_tidR := gmapR u64 mono_natR.

Lemma sids_all_lookup (sid : u64) :
  int.Z sid < N_TXN_SITES ->
  sids_all !! (int.nat sid) = Some sid.
Proof.
  intros H.
  unfold sids_all.
  rewrite list_lookup_fmap.
  rewrite lookup_seqZ_lt; last word.
  simpl. f_equal. word.
Qed.

Class mvcc_ghostG Σ :=
  {
    mvcc_key_vchainG :> inG Σ key_vchainR;
    mvcc_sid_tidsG :> inG Σ sid_tidsR;
    mvcc_sid_min_tidG :> inG Σ sid_min_tidR;
  }.

Definition mvcc_ghostΣ :=
  #[
     GFunctor key_vchainR;
     GFunctor sid_tidsR;
     GFunctor sid_min_tidR
   ].

Global Instance subG_mvcc_ghostG {Σ} :
  subG mvcc_ghostΣ Σ → mvcc_ghostG Σ.
Proof. solve_inG. Qed.

Record mvcc_names :=
  {
    mvcc_key_vchain : gname;
    mvcc_sid_tids_gn : gname;
    mvcc_sid_min_tid_gn : gname
  }.

Section definitions.
Context `{!mvcc_ghostG Σ}.

Definition vchain_ptsto γ q (k : u64) (vchain : list dbval) : iProp Σ :=
  own γ.(mvcc_key_vchain) {[k := ●ML{# q } (vchain : list (leibnizO dbval))]}.

Definition vchain_lb γ (k : u64) (vchain : list dbval) : iProp Σ :=
  own γ.(mvcc_key_vchain) {[k := ◯ML (vchain : list (leibnizO dbval))]}.

Lemma vchain_witness γ q k vchain :
  vchain_ptsto γ q k vchain -∗ vchain_lb γ k vchain.
Admitted.

Lemma vchain_update {γ k vchain} vchain' :
  (prefix vchain vchain') → vchain_ptsto γ 1 k vchain ==∗ vchain_ptsto γ 1 k vchain'.
Admitted.

Lemma vchain_false {γ q q' k vchain vchain'} :
  (1 < q + q')%Qp ->
  vchain_ptsto γ q k vchain -∗
  vchain_ptsto γ q' k vchain' -∗
  False.
Admitted.

Lemma vchain_combine {γ q q' k vchain vchain'} :
  (q + q' = 1)%Qp ->
  vchain_ptsto γ q k vchain -∗
  vchain_ptsto γ q' k vchain' -∗
  vchain_ptsto γ 1 k vchain ∧ ⌜vchain' = vchain⌝.
Admitted.

Lemma vchain_split {γ} q q' k vchain :
  (q + q' = 1)%Qp ->
  vchain_ptsto γ 1 k vchain -∗
  vchain_ptsto γ q k vchain ∗ vchain_ptsto γ q' k vchain.
Admitted.

(* The following points-to facts are defined in terms of the underlying CC resources. *)
Definition view_ptsto γ (k : u64) (v : option u64) (tid : u64) : iProp Σ :=
  ∃ vchain, vchain_lb γ k vchain ∗ ⌜vchain !! (int.nat tid) = Some v⌝.

Definition mods_token γ (k tid : u64) : iProp Σ :=
  ∃ vchain, vchain_ptsto γ (1/4) k vchain ∗ ⌜Z.of_nat (length vchain) ≤ (int.Z tid) + 1⌝.

Theorem view_ptsto_agree γ (k : u64) (v v' : option u64) (tid : u64) :
  view_ptsto γ k v tid -∗ view_ptsto γ k v' tid -∗ ⌜v = v'⌝.
Admitted.

(* Definitions/theorems about GC-related resources. *)
Definition site_active_tids_half_auth γ (sid : u64) tids : iProp Σ :=
  own γ.(mvcc_sid_tids_gn) {[sid := (gmap_view_auth (DfracOwn (1 / 2)) tids)]}.

Definition site_active_tids_frag γ (sid : u64) tid : iProp Σ :=
  own γ.(mvcc_sid_tids_gn) {[sid := (gmap_view_frag (V:=leibnizO unit) tid (DfracOwn 1) tt)]}.

Lemma site_active_tids_elem_of γ (sid : u64) tids tid :
  site_active_tids_half_auth γ sid tids -∗ site_active_tids_frag γ sid tid -∗ ⌜tid ∈ (dom tids)⌝.
Admitted.

Lemma site_active_tids_agree γ (sid : u64) tids tids' :
  site_active_tids_half_auth γ sid tids -∗
  site_active_tids_half_auth γ sid tids' -∗
  ⌜tids = tids'⌝.
Admitted.

Lemma site_active_tids_insert {γ sid tids} tid :
  tid ∉ dom tids ->
  site_active_tids_half_auth γ sid tids -∗
  site_active_tids_half_auth γ sid tids ==∗
  site_active_tids_half_auth γ sid (<[tid := tt]>tids) ∗
  site_active_tids_half_auth γ sid (<[tid := tt]>tids) ∗
  site_active_tids_frag γ sid tid.
Admitted.

Lemma site_active_tids_delete {γ sid tids} tid :
  site_active_tids_frag γ sid tid -∗
  site_active_tids_half_auth γ sid tids -∗
  site_active_tids_half_auth γ sid tids ==∗
  site_active_tids_half_auth γ sid (delete tid tids) ∗
  site_active_tids_half_auth γ sid (delete tid tids). 
Admitted.

(**
 * Q: Can we hide the [sid] from [active_tid]?
 * The problem of hiding it is that we lose the info of from which txn site
 * this tid is allocated, which creates problem in [txnMgr.deactivate] as
 * we cannot deduce [tid] is in the set of active TIDs of that site.
 *)
Definition active_tid γ (tid sid : u64) : iProp Σ :=
  (site_active_tids_frag γ sid tid ∧ ⌜int.Z sid < N_TXN_SITES⌝) ∧ ⌜0 < int.Z tid < 2 ^ 64 - 1⌝ .

Definition site_min_tid_half_auth γ (sid : u64) tidN : iProp Σ :=
  own γ.(mvcc_sid_min_tid_gn) {[sid := (●MN{#(1 / 2)} tidN)]}.

Definition site_min_tid_lb γ (sid : u64) tidN : iProp Σ :=
  own γ.(mvcc_sid_min_tid_gn) {[sid := (◯MN tidN)]}.

Lemma site_min_tid_valid γ (sid : u64) tidN tidlbN :
  site_min_tid_half_auth γ sid tidN -∗
  site_min_tid_lb γ sid tidlbN -∗
  ⌜(tidlbN ≤ tidN)%nat⌝.
Admitted.

Lemma site_min_tid_lb_weaken γ (sid : u64) tidN tidN' :
  (tidN' ≤ tidN)%nat ->
  site_min_tid_lb γ sid tidN -∗
  site_min_tid_lb γ sid tidN'.
Admitted.

Lemma site_min_tid_agree γ (sid : u64) tidN tidN' :
  site_min_tid_half_auth γ sid tidN -∗
  site_min_tid_half_auth γ sid tidN' -∗
  ⌜tidN = tidN'⌝.
Admitted.

Lemma site_min_tid_update {γ sid tidN} tidN' :
  (tidN ≤ tidN')%nat ->
  site_min_tid_half_auth γ sid tidN -∗
  site_min_tid_half_auth γ sid tidN ==∗
  site_min_tid_half_auth γ sid tidN' ∗ site_min_tid_half_auth γ sid tidN'.
Admitted.

Lemma site_min_tid_witness {γ sid tidN} :
  site_min_tid_half_auth γ sid tidN -∗
  site_min_tid_lb γ sid tidN.
Admitted.

Definition min_tid_lb γ tidN : iProp Σ :=
  [∗ list] sid ∈ sids_all, site_min_tid_lb γ sid tidN.

Lemma min_tid_lb_zero γ :
  ⊢ min_tid_lb γ 0%nat.
Admitted.

Definition mvcc_inv_gc_def γ : iProp Σ :=
  [∗ list] sid ∈ sids_all,
    ∃ (tids : gmap u64 unit) (tidmin : u64),
      site_active_tids_half_auth γ sid tids ∗
      site_min_tid_half_auth γ sid (int.nat tidmin) ∗
      ∀ tid, ⌜tid ∈ (dom tids) -> (int.nat tidmin) ≤ (int.nat tid)⌝.

Lemma mvcc_ghost_gc_init :
  ⊢ |==> ∃ γ, mvcc_inv_gc_def γ ∗
              ([∗ list] sid ∈ sids_all, site_active_tids_half_auth γ sid ∅) ∗
              ([∗ list] sid ∈ sids_all, site_min_tid_half_auth γ sid 0).
Admitted.

Definition mvccN := nroot .@ "mvcc_inv".
Definition mvccNGC := nroot .@ "mvcc_inv_gc".

Theorem active_ge_min γ (tid tidlb : u64) (sid : u64) :
  mvcc_inv_gc_def γ -∗
  active_tid γ tid sid -∗
  min_tid_lb γ (int.nat tidlb) -∗
  ⌜int.Z tidlb ≤ int.Z tid⌝.
Proof.
  iIntros "Hinv Hactive Hlb".
  iDestruct "Hactive" as "[[Htid %Hlookup] _]".
  apply sids_all_lookup in Hlookup.
  apply elem_of_list_lookup_2 in Hlookup.
  iDestruct (big_sepL_elem_of with "Hlb") as "Htidlb"; first done.
  iDestruct (big_sepL_elem_of with "Hinv") as (tids tidmin) "(Htids & Htidmin & %Hle)"; first done.
  (* Obtaining [tidmin ≤ tid]. *)
  iDestruct (site_active_tids_elem_of with "Htids Htid") as "%Helem".
  apply Hle in Helem.
  (* Obtaining [tidlb ≤ tidmin]. *)
  iDestruct (site_min_tid_valid with "Htidmin Htidlb") as "%Hle'".
  iPureIntro.
  apply Z.le_trans with (int.Z tidmin); word.
Qed.

End definitions.

Section mvccinv.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

Definition mvcc_inv_gc γ : iProp Σ :=
  inv mvccNGC (mvcc_inv_gc_def γ).

End mvccinv.
