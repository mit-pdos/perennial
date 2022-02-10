From Perennial.program_proof Require Import disk_prelude.
From iris.base_logic.lib Require Import ghost_map.
From iris.algebra Require Import dfrac_agree.

Local Definition key_fixedR := gmapR u64 (dfrac_agreeR (leibnizO nat)).

Class mvcc_ghostG Σ :=
  {
    (*
    mvcc_ghost_dbmaps :> ghost_mapG Σ (nat * u64) u64;
    mvcc_ghost_key_fixed :> inG Σ key_fixedR;
    *)
    (* XXX: remove this *)
    mvcc_ghost_versG :> ghost_varG Σ (list (u64 * u64 * u64))
  }.

Definition mvcc_ghostΣ := #[(*ghost_mapΣ (nat * u64) u64; GFunctor key_fixedR;*) (* XXX *) ghost_varΣ (list (u64 * u64 * u64))].

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
    tuple_vers_gn : gname
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

(*
Definition fixed_ptsto γ (q : Qp) (key : u64) (fixed : nat) : iProp Σ :=
  own γ.(mvcc_fixed) {[key := to_dfrac_agree (DfracOwn q) (fixed : (leibnizO _))]}.

Definition db_ptsto γ (dq : dfrac) (ts : nat) (key : u64) (val : u64) : iProp Σ :=
  (ts, key) ↪[γ.(mvcc_dbmaps)]{dq} val.

Definition mvcc_invariant γ : iProp Σ :=
  ∃ dbmaps,
    ghost_map_auth γ.(mvcc_dbmaps) 1 dbmaps.

Definition mvcc_inv γ : iProp Σ :=
  inv mvccN (mvcc_invariant γ).
*)

End definitions.
