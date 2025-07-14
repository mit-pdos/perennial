Require Import New.proof.proof_prelude.

Require Import New.proof.go_etcd_io.etcd.client.v3.

(* To simplify the proof for now, assuming that all keys are managed by
   leasingKV clients (i.e. the whole map is subject to the following
   protocol).

   The key being modified by `Put` must not have prefix `pfx`.
 *)

Section protocol.

Context {W : Type} {W_eq_dec : EqDecision W} {W_countable : Countable W}.

Record Response :=
  {
    resp_value : go_string;
    resp_mod_rev : w64;
  }.

(* FIXME: this is the wrong abstraction. Even when the entry is being updated,
   it might be concurrently read as long as the `waitc` the reader saw at the
   beginning closes. *)
Inductive LeasedEntryInner :=
| entry_valid (resp : option Response)
| entry_updating (waitc : W).

Record LeasedEntry :=
  {
    leased_rev : Z;
    leased_entry : LeasedEntryInner;
  }.

Record ServerNames :=
  {

  }.

Record CacheNames :=
  {

  }.

Record CacheState :=
  {
    entries : gmap go_string LeasedEntry;
    waitc_map : gmap W bool;
  }.

Global Instance settable_CacheState : Settable CacheState :=
  settable! Build_CacheState < entries; waitc_map >.

Context `{!invGS Σ}.

Definition own_server_inv (γs : ServerNames) (s : EtcdState.t) : iProp Σ.
Admitted.

Definition own_cache_inv (γc : CacheNames) (c : CacheState) : iProp Σ.
Admitted.

Definition own_Locked (w : W) (rev : Z) : iProp Σ.
Admitted.

Context (c c' : CacheState).
Context (s s' : EtcdState.t).
Context (γc : CacheNames) (γs : ServerNames).

Definition step_Lock (key : go_string) (w : W) (rev : Z) : Prop :=
  ∃ le,
  c.(entries) !! key = Some le ∧
  c.(waitc_map) !! w = None ∧
  rev = le.(leased_rev) ∧
  c' = c <| waitc_map := <[ w := false ]> c.(waitc_map) |>
         <| entries :=  <[key := {| leased_rev := rev; leased_entry := entry_updating w |} ]> c.(entries) |>.

Lemma take_step_Lock (key : go_string) w rev :
  step_Lock key w rev →
  own_cache_inv γc c ==∗
  own_cache_inv γc c' ∗
  own_Locked w rev.
Proof.
Admitted.

Definition step_Commit_Put (rev : Z) (put_req : PutRequest.t) resp : Prop :=
  interp (handle_etcdE 0) (Put put_req) s s' (inr resp).

Definition own_Put_committed (resp : PutResponse.t) : iProp Σ.
Admitted.

(* FIXME: requires linearization update. *)
Lemma take_step_Commit_Put {w} rev put_req resp :
  step_Commit_Put rev put_req resp →
  own_Locked w rev -∗
  own_server_inv γs s ==∗
  own_server_inv γs s' ∗
  own_Put_committed resp.
Proof.
Admitted.

Definition step_Evict (key : go_string) : Prop :=
  c' = c <| waitc_map := c.(waitc_map) |> <| entries :=  delete key c.(entries) |>.

Lemma take_step_Evict key w rev :
  step_Evict key →
  own_Locked w rev -∗
  own_cache_inv γc c ==∗
  own_cache_inv γc c' ∗ own_Locked w rev.
Proof.
Admitted.

(*
Definition step_Update key val resp :
  ∃ le,
  s.(entries) !! key = le ∧
  le.(entry) *)
(* FIXME: need to update the value even if there's a new waitc, but the sum type
   doesn't have a way of storing both a value and a waitc. *)

End protocol.
