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
  (* SpontaneousTransition time;; *)
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

Inductive ecomp (E : Type → Type) : Type → Type :=
| Ret {A} (a : A) : ecomp E A
| Effect {A} (e : E A) : ecomp E A
| Bind {A B} (k : A → ecomp E B) (e : ecomp E A) : ecomp E B.

Arguments Ret {_ _} (_).
Arguments Effect {_ _} (_).
Arguments Bind {_ _ _} (_ _).

Instance ecomp_MBind E : MBind (ecomp E) := (@Bind E).
Instance ecomp_MRet E : MRet (ecomp E) := (@Ret E).

Fixpoint denote `{MBind M} `{!MRet M} {E R} (handler : ∀ A (e : E A), M A) (e : ecomp E R) : M R :=
  match e with
  | Ret a => mret a
  | Effect e => (handler _ e)
  | Bind k e =>
      v ← (denote handler e);
      denote handler (k v)
  end.

Inductive etcdE : Type → Type :=
| SuchThat {A} (pred : A → Prop) : etcdE A
| GetState : etcdE EtcdState.t
| SetState (σ' : EtcdState.t) : etcdE unit
| TimeGet : etcdE w64
| Assume (b : Prop) : etcdE unit
| Assert (b : Prop) : etcdE unit.
(* XXX: the assert effect should be interpreted when converting to Iris precondition? *)

Inductive handle_etcdE (t : w64) : ∀ (A : Type) (e : etcdE A), relation.t EtcdState.t A :=
| SuchThat_handle : ∀ {A} σ pred (a : A), pred a → handle_etcdE t _ (SuchThat pred) σ σ a
| GetState_handle : ∀ σ, handle_etcdE t _ (GetState) σ σ σ
| SetState_handle : ∀ σ σ', handle_etcdE t _ (SetState σ') σ σ' ()
| TimeGet_handle : ∀ σ, handle_etcdE t _ TimeGet σ σ t
| Assume_handle : ∀ σ P, P → handle_etcdE t _ (Assume P) σ σ ()
.

Instance relation_mret A : MRet (relation.t A) :=
  λ {A} a, λ σ σ' a', a = a'.

Instance relation_mbind A : MBind (relation.t A) :=
  λ {A B} kmb ma, λ σ σ' b,
    ∃ a σmiddle,
      ma σ σmiddle a ∧
      kmb a σmiddle σ' b.

Definition LeaseGrant2 (req : LeaseGrantRequest.t) : ecomp etcdE LeaseGrantResponse.t :=
  (* req.TTL is advisory, so it is ignored. *)
  ttl ← Effect $ SuchThat (λ (_ : w64), True);
  σ ← Effect GetState;
  lease_id ← (if decide (req.(LeaseGrantRequest.ID) = (W64 0)) then
                Effect $ SuchThat (λ lease_id, lease_id ∉ σ.(EtcdState.used_lease_ids))
              else
                (Effect $ Assume (req.(LeaseGrantRequest.ID) ∉ σ.(EtcdState.used_lease_ids));;
                 mret req.(LeaseGrantRequest.ID)));
  time ← Effect TimeGet;
  let σ := (set EtcdState.used_lease_ids (λ old, {[lease_id]} ∪ old) σ) in
  let σ := (set EtcdState.lease_expiration <[lease_id := Some (word.add time ttl)]> σ) in
  Effect (SetState σ);;
  mret (LeaseGrantResponse.mk lease_id ttl).

Lemma test_equivalence req time :
  ∀ σ σ' resp,
  relation.denote (LeaseGrant time req) σ σ' resp ↔
  denote (handle_etcdE time) (LeaseGrant2 req) σ σ' resp.
Proof.
  intros.
  split.
  {
    intros Hstep.
    simpl in *.
    monad_inv.
    exists x, σ; split; first by constructor.
    exists σ, σ; split; first by constructor.
    destruct decide.
    {
      simpl in *.
      monad_inv.
      exists lease_id, σ; split; first by constructor.
      exists time, σ; split; first by constructor.
      eexists (), _; split; first by constructor.
      constructor.
    }
    {
      simpl in *.
      monad_inv.
      eexists _, σ; split.
      { exists (), σ. split; econstructor. done. }
      exists time, σ; split; first by constructor.
      eexists (), _; split; first by constructor.
      econstructor.
    }
  }
  {
    intros Hstep.
    repeat destruct Hstep as [? Hstep].
    econstructor; first by econstructor.
    simpl in *.
    admit.
  }
Admitted.
