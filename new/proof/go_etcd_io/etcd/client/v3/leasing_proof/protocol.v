Require Import New.proof.proof_prelude.

Require Import New.proof.go_etcd_io.etcd.client.v3.

(* To simplify the proof for now, assuming that all keys are managed by
   leasingKV clients (i.e. the whole map is subject to the following
   protocol).

   The key being modified by `Put` must not have prefix `pfx`.
 *)

Section protocol.

Context {W : Type} {W_eq_dec : EqDecision W} {W_countable : Countable W}.

Inductive leasedEntryInner :=
| EntryValid (response : RangeResponse.t)
| EntryUpdating (waitc : W).

Record leasedEntry :=
{
  leased_rev : Z;
  leased_entry : leasedEntryInner;
}.

Record cache_state :=
  {
    entries : gmap go_string leasedEntry;
    waitc_map : gmap W bool;
  }.

Global Instance settable_cache_state : Settable cache_state :=
  settable! Build_cache_state < entries; waitc_map >.

Record server_state :=
  {
    kvs : gmap go_string go_string;
    lease_revs : gmap go_string Z; (* revision number *)
  }.

Global Instance settable_server_state : Settable server_state :=
  settable! Build_server_state < kvs ; lease_revs >.

Context `{!invGS Σ}.
Definition own_server_inv (σ : server_state) : iProp Σ.
Admitted.

Definition own_cache_inv (σ : cache_state) : iProp Σ.
Admitted.

Definition own_Locked (w : W) (rev : Z) : iProp Σ.
Admitted.

Context (c c' : cache_state).
Context (s s' : server_state).

Definition step_Lock (key : go_string) (w : W) (rev : Z) : Prop :=
  ∃ le,
  c.(entries) !! key = Some le ∧
  c.(waitc_map) !! w = None ∧
  rev = le.(leased_rev) ∧
  c' = c <| waitc_map := <[ w := false ]> c.(waitc_map) |>
         <| entries :=  <[key := {| leased_rev := rev; leased_entry := EntryUpdating w |} ]> c.(entries) |>.

Lemma take_step_Lock (key : go_string) w rev :
  step_Lock key w rev →
  own_cache_inv c ==∗
  own_cache_inv c' ∗
  own_Locked w rev.
Proof.
Admitted.

Definition step_Commit_Put (rev : Z) (put_req : PutRequest.t) : Prop :=
  (default 0 (s.(lease_revs) !! put_req.(PutRequest.key))) < rev + 1 ∧
  s'.(kvs) = <[ put_req.(PutRequest.key) := put_req.(PutRequest.value)]> s.(kvs).

(* FIXME: requires linearization update. *)
Lemma take_step_Commit_Put rev put_req :
  step_Commit_Put rev put_req →
  own_server_inv s ==∗
  own_server_inv s'.
Proof.
Admitted.

Definition step_Evict (key : go_string) : Prop :=
  c' = c <| waitc_map := c.(waitc_map) |> <| entries :=  delete key c.(entries) |>.

Lemma take_step_Evict key w rev :
  step_Evict key →
  own_Locked w rev -∗
  own_cache_inv c ==∗
  own_cache_inv c' ∗ own_Locked w rev.
Proof.
Admitted.


(* Q: what happens when the KV operation is committed? Really, that should be
   part of the inv too I guess. *)

End protocol.
