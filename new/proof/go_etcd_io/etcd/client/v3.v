Require Import New.code.go_etcd_io.etcd.client.v3.
Require Import New.generatedproof.go_etcd_io.etcd.client.v3.
Require Import New.proof.proof_prelude.
From Perennial.Helpers Require Import Transitions.

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
  }.

Global Instance settable : Settable _ :=
  settable! mk < revision; compact_revision; key_values; used_lease_ids>.
End EtcdState.

Module LeaseGrantRequest.
Record t :=
mk {
    TTL : w64;
    ID : w64;
  }.
Global Instance settable_EtcdState : Settable _ :=
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

Existing Instance fallback_genPred.
Existing Instances r_mbind r_mret r_fmap.

Definition LeaseGrant (req : LeaseGrantRequest.t) : transition EtcdState.t LeaseGrantResponse.t :=
  (* req.TTL is advisory, so it is ignored. *)
  ttl ← suchThat (λ _ _, True);
  lease_id ← (if (word.eqb req.(LeaseGrantRequest.ID) (W64 0)) then
                suchThat (λ σ lease_id, lease_id ∉ σ.(EtcdState.used_lease_ids))
              else
                (assert (λ σ, req.(LeaseGrantRequest.ID) ∉ σ.(EtcdState.used_lease_ids));;
                 ret req.(LeaseGrantRequest.ID))
    );
  modify (set EtcdState.used_lease_ids (λ old, {[lease_id]} ∪ old)) ;;
  ret (LeaseGrantResponse.mk lease_id ttl).
