From Perennial.program_proof Require Import disk_prelude.
From iris.algebra Require Import dfrac_agree gset.
From iris.algebra.lib Require Import mono_nat gmap_view.

Local Definition key_fixedR := gmapR u64 (dfrac_agreeR (leibnizO nat)).
Local Definition tidsR := gmap_viewR nat (leibnizO unit).
Local Definition sid_tidsR := gmapR u64 (dfrac_agreeR (leibnizO (gset u64))).

Class mvcc_ghostG Σ :=
  {
    (*
    mvcc_ghost_dbmaps :> ghost_mapG Σ (nat * u64) u64;
    mvcc_ghost_key_fixed :> inG Σ key_fixedR;
    *)
    mvcc_active_tidsG :> inG Σ tidsR;
    mvcc_active_tids_siteG :> inG Σ sid_tidsR;
    mvcc_min_tidG :> inG Σ mono_natR;
  }.

Definition mvcc_ghostΣ :=
  #[(*ghost_mapΣ (nat * u64) u64; GFunctor key_fixedR;*)
     GFunctor tidsR;
     GFunctor sid_tidsR;
     GFunctor mono_natR
   ].

Global Instance subG_mvcc_ghostG {Σ} :
  subG mvcc_ghostΣ Σ → mvcc_ghostG Σ.
Proof. solve_inG. Qed.

Record mvcc_names :=
  {
    (*
    mvcc_dbmaps : gname;
    mvcc_fixed : gname;
    *)
    (* XXX *)
    mvcc_active_tids_gn: gname;
    mvcc_active_tids_site_gn: gname;
    mvcc_min_tid_gn : gname
  }.

Section definitions.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

(* Definition tid_sentinel : nat := 18446744073709551615%nat. *)

Definition mvccN := nroot .@ "mvcc_inv".


(* The following points-to facts are defined in terms of the underlying CC resources. *)
Definition view_ptsto (k v : u64) : iProp Σ := True.
Definition mods_token (k : u64) : iProp Σ := True.

Theorem view_ptsto_agree (k v v' : u64) :
  view_ptsto k v -∗ view_ptsto k v' -∗ ⌜v = v'⌝.
Admitted.

Definition active_tids_auth γ tids : iProp Σ :=
  own γ.(mvcc_active_tids_gn) (gmap_view_auth (DfracOwn 1) tids).

Definition active_tid γ (tid : nat) : iProp Σ :=
  own γ.(mvcc_active_tids_gn) (gmap_view_frag (V:=leibnizO unit) tid (DfracOwn 1) tt).

Definition active_tids_site γ (sid : u64) tids : iProp Σ :=
  own γ.(mvcc_active_tids_site_gn) {[sid := to_dfrac_agree (DfracOwn (1/2)) tids]}.

Definition min_tid_auth γ tid : iProp Σ :=
  own γ.(mvcc_min_tid_gn) (●MN tid).

Definition min_tid_lb γ tid : iProp Σ :=
  own γ.(mvcc_min_tid_gn) (◯MN tid).

Theorem active_ge_min γ tid tidlb :
  active_tid γ tid -∗
  min_tid_lb γ tidlb -∗
  ⌜(tid ≥ tidlb)%nat⌝.
Admitted.

(*
Definition fixed_ptsto γ (q : Qp) (key : u64) (fixed : nat) : iProp Σ :=
  own γ.(mvcc_fixed) {[key := to_dfrac_agree (DfracOwn q) (fixed : (leibnizO _))]}.

Definition db_ptsto γ (dq : dfrac) (ts : nat) (key : u64) (val : u64) : iProp Σ :=
  (ts, key) ↪[γ.(mvcc_dbmaps)]{dq} val.
*)

Definition mvcc_invariant γ : iProp Σ :=
  ∃ tidmin tidsactive,
    min_tid_auth γ tidmin ∗
    active_tids_auth γ tidsactive ∗
    (* TODO: tidsactive is the union of tids of each *)
    ⌜∀ tid, tid ∈ (dom (gset nat) tidsactive) -> (tid ≥ tidmin)%nat⌝.
  (*
  ∃ dbmaps,
    ghost_map_auth γ.(mvcc_dbmaps) 1 dbmaps.
  *)

Definition mvcc_inv γ : iProp Σ :=
  inv mvccN (mvcc_invariant γ).

End definitions.
