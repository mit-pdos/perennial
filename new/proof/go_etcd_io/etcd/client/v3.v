Require Import New.code.go_etcd_io.etcd.client.v3.
Require Import New.generatedproof.go_etcd_io.etcd.client.v3.
Require Import New.proof.proof_prelude.
From Perennial.Helpers Require Import Transitions.

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

(** Effects for etcd specification. *)
Inductive etcdE : Type → Type :=
| SuchThat {A} (pred : A → Prop) : etcdE A
| GetState : etcdE EtcdState.t
| SetState (σ' : EtcdState.t) : etcdE unit
| GetTime : etcdE w64
| Assume (b : Prop) : etcdE unit
| Assert (b : Prop) : etcdE unit.

(* Establish monadicity of relation.t *)
Instance relation_mret A : MRet (relation.t A) :=
  λ {A} a, λ σ σ' a', a = a' ∧ σ' = σ.

Instance relation_mbind A : MBind (relation.t A) :=
  λ {A B} kmb ma, λ σ σ' b,
    ∃ a σmiddle,
      ma σ σmiddle a ∧
      kmb a σmiddle σ' b.

(* Handle etcd effects as a in the [relation.t EtcdState.t] monad. *)
Definition handle_etcdE (t : w64) (A : Type) (e : etcdE A) : relation.t EtcdState.t A :=
  match e with
  | SuchThat pred => λ σ σ' a, pred a ∧ σ' = σ
  | GetState => λ σ σ' σret, σ' = σ ∧ σret = σ
  | SetState σnew => λ σ σ' _, σ' = σnew
  | GetTime => λ σ σ' tret, tret = t ∧ σ' = σ
  | Assume P => λ σ σ' tret, P ∧ σ = σ'
  | _ => λ σ σ' _, False (* XXX: the assert effect should be interpreted when converting to Iris precondition? *)
  end.

Definition interp {A} (time_of_execution : w64) (e : ecomp etcdE A) : relation.t EtcdState.t A :=
  denote (handle_etcdE time_of_execution) e.

(** This covers all transitions of the etcd state that are not tied to a client
   API call, e.g. lease expiration happens "in the background". This will be
   called as a prelude by all the client-facing operations, since it is sound to
   delay running spontaneous transitions until they would actually affect the
   client. This relies on [SpontaneousTransition] being monotonic: if a
   transition can happen at time [t'] with [t' > t], then it must be possible at
   [t] as well. The following lemma confirms this. *)
Definition SingleSpontaneousTransition : ecomp etcdE () :=
  (* expire some lease *)
  (* XXX: this is a "partial" transition: it is not always possible to expire a
     lease. *)
  time ← Effect GetTime;
  σ ← Effect GetState;
  lease_id ← Effect $ SuchThat (λ l, ∃ exp, σ.(EtcdState.lease_expiration) !! l = Some (Some exp) ∧
                                     uint.nat time > uint.nat exp);
  Effect $ SetState (set EtcdState.lease_expiration <[ lease_id := None ]> σ).

Lemma SingleSpontaneousTransition_monotonic (time time' : w64) σ σ' :
  uint.nat time < uint.nat time' →
  interp time SingleSpontaneousTransition σ σ' () →
  interp time' SingleSpontaneousTransition σ σ' ().
Proof.
  intros Htime Hstep.
  rewrite /SingleSpontaneousTransition in Hstep |- *.
  rewrite /interp /= /mbind /relation_mbind in Hstep.
  destruct Hstep as (? & ? & [-> ->] & Hstep).
  destruct Hstep as (? & ? & [-> ->] & Hstep).
  destruct Hstep as (? & ? & [Hstep ->] & ->).
  destruct Hstep as (? & Hlookup & Hgt).
  repeat econstructor; try done.
  lia.
Qed.

(** This does a non-deterministic number of spontaneous transitions. *)
Definition SpontaneousTransition : ecomp etcdE unit :=
  num_steps ← Effect $ SuchThat (λ (_ : nat), True);
  Nat.iter num_steps (λ p, p;; SingleSpontaneousTransition) (mret ()).

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

Definition LeaseGrant (req : LeaseGrantRequest.t) : ecomp etcdE LeaseGrantResponse.t :=
  (* FIXME: add this back *)
  (* SpontaneousTransition;; *)
  (* req.TTL is advisory, so it is ignored. *)
  ttl ← Effect $ SuchThat (λ _, True);
  σ ← Effect GetState;
  lease_id ← (if decide (req.(LeaseGrantRequest.ID) = (W64 0)) then
                Effect $ SuchThat (λ lease_id, lease_id ∉ σ.(EtcdState.used_lease_ids))
              else
                (Effect $ Assert (req.(LeaseGrantRequest.ID) ∉ σ.(EtcdState.used_lease_ids));;
                 mret req.(LeaseGrantRequest.ID)));
  time ← Effect GetTime;
  let σ := (set EtcdState.used_lease_ids (λ old, {[lease_id]} ∪ old) σ) in
  let σ := (set EtcdState.lease_expiration <[lease_id := Some (word.add time ttl)]> σ) in
  Effect (SetState σ);;
  mret (LeaseGrantResponse.mk lease_id ttl).

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

Definition LeaseKeepAlive (req : LeaseKeepAliveRequest.t) : ecomp etcdE LeaseKeepAliveResponse.t :=
  (* XXX *)
  (* if the lease is expired, returns TTL=0. *)
  (* Q: if the lease expiration time is in the past, is it guaranteed that
     the lease is expired (i.e. its attached keys are now deleted)? Or does a
     failed KeepAlive merely mean a _lack_ of new knowledge of a lower bound on
     lease expiration?
     A comment in v3_server.go says:
    // A expired lease might be pending for revoking or going through
    // quorum to be revoked. To be accurate, renew request must wait for the
    // deletion to complete.
    But the following code actually also returns if the lessor gets demoted, in
    which case the lease expiration time is extended to "forever".
    Q: when refreshing, "extend" is set to 0. Is it possible for `remainingTTL >
    0` when reaching lessor.go:441, resulting in the `Lease` expiry being too
    small?
 *)
  SpontaneousTransition;;
  σ ← Effect $ GetState;
  (* This is conservative. lessor.go looks like it avoids renewing a lease
     if its expiration is in the past, but it's actually possible for it to
     still renew something that would have been considered expired here because
     of leader change, which sets expiry to "forever" before restarting it upon
     promotion. *)
  match σ.(EtcdState.lease_expiration) !! req.(LeaseKeepAliveRequest.ID) with
  | None => mret $ LeaseKeepAliveResponse.mk (W64 0) req.(LeaseKeepAliveRequest.ID)
  | Some _ =>
      ttl ← Effect $ SuchThat (λ _, True);
      mret $ LeaseKeepAliveResponse.mk ttl req.(LeaseKeepAliveRequest.ID)
  end.

Section spec.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Definition Spec Resp := (Resp → iProp Σ) → iProp Σ.

Instance Spec_MRet : MRet Spec :=
  λ {Resp} resp Φ, Φ resp.

Instance Spec_MBind : MBind Spec :=
  λ {RespA RespB} (kmb : RespA → Spec RespB) (ma : Spec RespA) ΦB,
    ma (λ respa, kmb respa ΦB).

Context `{!ghost_varG Σ EtcdState.t}.

(* This is only in grove_ffi. *)
Axiom own_time : w64 → iProp Σ.

Definition handle_etcdE_spec (γ : gname) (A : Type) (e : etcdE A) : Spec A :=
  (match e with
   | GetState => λ Φ, (∃ σ q, ghost_var γ q σ ∗ (ghost_var γ q σ -∗ Φ σ))
   | SetState σ' => λ Φ, (∃ (_σ : EtcdState.t), ghost_var γ 1%Qp _σ ∗ (ghost_var γ 1%Qp σ' -∗ Φ tt))
   | GetTime => λ Φ, (∀ time, own_time time -∗ own_time time ∗ Φ time)
   | Assume P => λ Φ, (⌜ P ⌝ -∗ Φ ())
   | Assert P => λ Φ, (⌜ P ⌝ ∗ Φ ())
   | SuchThat pred => λ Φ, ∀ x, ⌜ pred x ⌝ -∗ Φ x
   end)%I.

Definition GrantSpec req γ := denote (handle_etcdE_spec γ) (LeaseGrant req).
Lemma test req γ :
  ⊢ ∀ Φ,
  (∃ (σ : EtcdState.t), ghost_var γ 1%Qp σ ∗
        (∀ resp (σ' : EtcdState.t), ghost_var γ 1%Qp σ' -∗ Φ resp)) -∗
  GrantSpec req γ Φ.
Proof.
  iIntros (?) "Hupd".
  unfold GrantSpec.
  unfold denote.
  simpl. unfold mbind, mret.
  unfold Spec_MBind, Spec_MRet, handle_etcdE_spec.
  simpl.
  iIntros "* _".
  iDestruct "Hupd" as (?) "[Hv Hupd]".
  repeat iExists _. iFrame.
  iIntros "Hv".
  simpl.
  destruct decide.
  {
    iIntros "* %Hnot".
    iIntros (?) "Htime".
    iFrame "Htime".
    iExists _; iFrame.
    iIntros "Hv".
    iApply "Hupd".
    iFrame.
  }
  {
    simpl.
    iSplitR.
    { admit. } (* need to prove this assert statement. *)
    iIntros (?) "Htime".
    iFrame "Htime".
    iExists _; iFrame.
    iIntros "Hv".
    iApply "Hupd".
    iFrame.
  }
Abort.
End spec.
