From Perennial.program_proof Require Import disk_prelude.
From iris.algebra Require Import dfrac_agree.
From iris.algebra.lib Require Import mono_nat mono_list gmap_view.

(* Logical version chain. *)
Local Definition vchainR := mono_listR (leibnizO (option u64)).
Local Definition key_vchainR := gmapR u64 vchainR.
(* GC-related ghost states. *)
Local Definition tidsR := gmap_viewR u64 (leibnizO unit).
Local Definition sid_tidsR := gmapR u64 (dfrac_agreeR (leibnizO (gset u64))).

Class mvcc_ghostG Σ :=
  {
    mvcc_key_vchainG :> inG Σ key_vchainR;
    mvcc_active_tidsG :> inG Σ tidsR;
    mvcc_active_tids_siteG :> inG Σ sid_tidsR;
    mvcc_min_tidG :> inG Σ mono_natR;
  }.

Definition mvcc_ghostΣ :=
  #[
     GFunctor key_vchainR;
     GFunctor tidsR;
     GFunctor sid_tidsR;
     GFunctor mono_natR
   ].

Global Instance subG_mvcc_ghostG {Σ} :
  subG mvcc_ghostΣ Σ → mvcc_ghostG Σ.
Proof. solve_inG. Qed.

Record mvcc_names :=
  {
    mvcc_key_vchain : gname;
    mvcc_active_tids_gn : gname;
    mvcc_active_tids_site_gn: gname;
    mvcc_min_tid_gn : gname
  }.

Section definitions.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

(*
Inductive dbval : Type :=
| Nil : dbval
| Value : u64 -> dbval.
*)

Definition mvccN := nroot .@ "mvcc_inv".

Definition vchain_ptsto γ q (k : u64) (vchain : list (option u64)) : iProp Σ :=
  own γ.(mvcc_key_vchain) {[k := ●ML{# q } (vchain : list (leibnizO (option u64)))]}.

Definition vchain_lb γ (k : u64) (vchain : list (option u64)) : iProp Σ :=
  own γ.(mvcc_key_vchain) {[k := ◯ML (vchain : list (leibnizO (option u64)))]}.

Lemma vchain_witness γ q k vchain :
  vchain_ptsto γ q k vchain -∗ vchain_lb γ k vchain.
Admitted.

Lemma vchain_update {γ k q vchain} vchain' :
  (prefix vchain vchain') → vchain_ptsto γ q k vchain ==∗ vchain_ptsto γ q k vchain'.
Admitted.

(* The following points-to facts are defined in terms of the underlying CC resources. *)
Definition view_ptsto γ (k : u64) (v : option u64) (tid : u64) : iProp Σ :=
  ∃ vchain, vchain_lb γ k vchain ∗ ⌜vchain !! (int.nat tid) = Some v⌝.

Definition mods_token γ (k tid : u64) : iProp Σ :=
  ∃ vchain, vchain_ptsto γ (1/4) k vchain ∗ ⌜length vchain < (int.nat tid)⌝.

Theorem view_ptsto_agree γ (k : u64) (v v' : option u64) (tid : u64) :
  view_ptsto γ k v tid -∗ view_ptsto γ k v' tid -∗ ⌜v = v'⌝.
Admitted.

(* Definitions/theorems about GC-related resources. *)
Definition active_tids_auth γ tids : iProp Σ :=
  own γ.(mvcc_active_tids_gn) (gmap_view_auth (DfracOwn 1) tids).

Definition active_tid γ (tid : u64) : iProp Σ :=
  own γ.(mvcc_active_tids_gn) (gmap_view_frag (V:=leibnizO unit) tid (DfracOwn 1) tt).

Definition active_tids_site γ (sid : u64) tids : iProp Σ :=
  own γ.(mvcc_active_tids_site_gn) {[sid := to_dfrac_agree (DfracOwn (1/2)) tids]}.

Definition min_tid_auth γ tidN : iProp Σ :=
  own γ.(mvcc_min_tid_gn) (●MN tidN).

Definition min_tid_lb γ tidN : iProp Σ :=
  own γ.(mvcc_min_tid_gn) (◯MN tidN).

Theorem active_ge_min γ tid tidlbN :
  active_tid γ tid -∗
  min_tid_lb γ tidlbN -∗
  ⌜(int.nat tid ≥ tidlbN)%nat⌝.
Admitted.

Definition mvcc_invariant γ : iProp Σ :=
  ∃ tidminN tidsactive,
    (* TODO: owning 1/2 of logical version chains. *)
    min_tid_auth γ tidminN ∗
    active_tids_auth γ tidsactive ∗
    (* TODO: tidsactive is the union of tids of each *)
    ⌜∀ tid, tid ∈ (dom (gset u64) tidsactive) -> (int.nat tid ≥ tidminN)%nat⌝.

Definition mvcc_inv γ : iProp Σ :=
  inv mvccN (mvcc_invariant γ).

End definitions.
