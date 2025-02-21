Require Import New.code.go_etcd_io.etcd.client.v3.
Require Import New.generatedproof.go_etcd_io.etcd.client.v3.
Require Import New.proof.proof_prelude.

(** Notes about the etcd robustness test model.
 - The real `Lease.Grant()` does not take in a LeaseID, it gets it from the server.
   The model, on the other hand, uses the LeaseID straight from the LeaseGrant
   request (even if the LeaseID were zero, which indicates to the LeaseGrant RPC
   that the lessor should choose an ID).
*)

Module EtcdState.
Record t :=
mk {
    Revision : w64;
    CompactRevision : w64;
    KeyValues : gmap string (string * w64);
    KeyLeases : gmap string w64;
    Leases : gmap w64 (w64 * gset string);
  }.

Global Instance settable_EtcdState : Settable _ :=
  settable! EtcdState.mk < Revision; CompactRevision; KeyValues; KeyLeases; Leases >.
End EtcdState.


Definition is_Grant (leaseid) (s s' : EtcdState.t) : Prop :=
  let leaase := LeaseId
.


Module RangeRequest.
Record t :=
mk {
    Revision : w64;
    Start : go_string;
    End : go_string;
    Limit : w64;
  }.
End RangeRequest.

Definition get_range (start end : go_string) (limit : w64) (s : EtcdState.t) : Prop :=
.

Definition range_operation (request : RangeRequest.t) (s s' : EtcdState.t) : Prop :=
  if decide (request.(RangeRequest.Revision) = 0 ∨
             request.(RangeRequest.Revision) = s.(EtcdState.Revision))
  then
    True
  else if decide (request.(RangeRequest.Revision) > s.(EtcdState.Revision)) then
         True
       else
         True
.
