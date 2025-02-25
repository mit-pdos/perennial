Require Import New.code.go_etcd_io.etcd.client.v3.
Require Import New.generatedproof.go_etcd_io.etcd.client.v3.
Require Import New.proof.proof_prelude.
From Perennial.Helpers Require Import Transitions.

Existing Instance fallback_genPred.
Existing Instances r_mbind r_mret r_fmap.

(* https://etcd.io/docs/v3.6/learning/api/ *)
Module KeyValue.
Record t :=
mk {
    key : list w8;
    create_revision : w64;
    mod_revision : w64;
    version : w64;
    value : list w8;
    lease : w64;
  }.

Global Instance settable : Settable _ :=
  settable! mk < key; create_revision; mod_revision; version; value; lease>.
End KeyValue.

Module EtcdState.
Record t :=
mk {
    revision : w64;
    compact_revision : w64;
    key_values : gmap w64 (gmap (list w8) KeyValue.t);

    (* XXX: Though the docs don't explain or guarantee this, this tracks lease
       IDs that have been given out previously to avoid reusing LeaseIDs. If
       reuse were allowed, it's possible that a lease expires & its keys are
       deleted, then another client creates a lease with the same ID and
       attaches the same keys, after which the first expired client would
       incorrectly see its keys still attached with its leaseid.
     *)
    used_lease_ids : gset w64;
    lease_expiration : gmap w64 (option w64); (* [None] means the lease has been expired. *)
  }.

Global Instance settable : Settable _ :=
  settable! mk < revision; compact_revision; key_values; used_lease_ids; lease_expiration>.
End EtcdState.

(** This covers all transitions of the etcd state that are not tied to a client
   API call, e.g. lease expiration happens "in the background". This will be
   called as a prelude by all the client-facing operations, since it is sound to
   delay running spontaneous transitions until they would actually affect the
   client. This relies on [SpontaneousTransition] being monotonic: if a
   transition can happen at time [t'] with [t' > t], then it must be possible at
   [t] as well. The following lemma confirms this. *)
Definition SingleSpontaneousTransition (time : w64) : transition EtcdState.t () :=
  (* expire some lease *)
  (* XXX: this is a "partial" transition: it is not always possible to expire a
     lease. *)
  lease_id ← suchThat (λ σ l, ∃ exp, σ.(EtcdState.lease_expiration) !! l = Some (Some exp) ∧
                                     uint.nat time > uint.nat exp);
  modify (set EtcdState.lease_expiration <[ lease_id := None ]>)
.

Lemma SingleSpontaneousTransition_monotonic (time time' : w64) σ σ' :
  uint.nat time < uint.nat time' →
  relation.denote (SingleSpontaneousTransition time) σ σ' () →
  relation.denote (SingleSpontaneousTransition time') σ σ' ().
Proof.
  intros Htime Hstep.
  unfold SingleSpontaneousTransition in Hstep |- *.
  simpl in Hstep.
  monad_inv. destruct H as (exp & ? & ?).
  simpl. monad_simpl.
  econstructor.
  {
    constructor.
    eexists _. split; try eassumption. word.
  }
  constructor. done.
Qed.

(** This does a non-deterministic number of spontaneous transitions. *)
Definition SpontaneousTransition (time : w64) : transition EtcdState.t unit :=
  num_steps ← any nat;
  Nat.iter num_steps (λ p, p;; SingleSpontaneousTransition time) (ret ()).

Module LeaseGrantRequest.
Record t :=
mk {
    TTL : w64;
    ID : w64;
  }.
Global Instance settable : Settable _ :=
  settable! mk < TTL; ID>.
End LeaseGrantRequest.

Module LeaseGrantResponse.
Record t :=
mk {
    TTL : w64;
    ID : w64;
  }.
Global Instance settable : Settable _ :=
  settable! mk <TTL; ID>.
End LeaseGrantResponse.

(* time is *)
Definition LeaseGrant (time : w64) (req : LeaseGrantRequest.t) : transition EtcdState.t LeaseGrantResponse.t :=
  SpontaneousTransition time;;
  (* req.TTL is advisory, so it is ignored. *)
  ttl ← any w64;
  lease_id ← (if decide (req.(LeaseGrantRequest.ID) = (W64 0)) then
                suchThat (λ σ lease_id, lease_id ∉ σ.(EtcdState.used_lease_ids))
              else
                (assert (λ σ, req.(LeaseGrantRequest.ID) ∉ σ.(EtcdState.used_lease_ids));;
                 ret req.(LeaseGrantRequest.ID))
    );
  modify (set EtcdState.used_lease_ids (λ old, {[lease_id]} ∪ old)) ;;
  (* XXX: no overflow assumption? *)
  modify (set EtcdState.lease_expiration <[lease_id := Some (word.add time ttl)]>) ;;
  ret (LeaseGrantResponse.mk lease_id ttl).

Module LeaseKeepAliveRequest.
Record t :=
mk {
    ID : w64;
  }.
Global Instance settable : Settable _ :=
  settable! mk < ID>.
End LeaseKeepAliveRequest.

Module LeaseKeepAliveResponse.
Record t :=
mk {
    TTL : w64;
    ID : w64;
  }.
Global Instance settable : Settable _ :=
  settable! mk <TTL; ID>.
End LeaseKeepAliveResponse.

(*
Definition LeaseKeepAlive (time : w64) (req : LeaseKeepAliveRequest.t) :
  transition EtcdState.t LeaseKeepAliveResponse.t :=
  SpontaneousTransition time;;
.
*)
