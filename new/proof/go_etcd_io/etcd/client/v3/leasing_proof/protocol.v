Require Import New.proof.proof_prelude.

Require Import New.proof.go_etcd_io.etcd.client.v3.

(* NOTE(bug): the original leasingkv does not correctly check for lease expiration
   when handling a Get(). *)

(* NOTE(bug): Concurrent delete and puts with the same leasingKV are not handled
   properly (permanent cache inconsistency).
   `TestLeasingConcurrentPutDelete`
   https://github.com/upamanyus/etcd/commit/174a964e806707b9fde186ade4b12be61967e9ea

   When Delete and Put run concurrently, if the server executes Put before
   Delete, but the cache processes the Delete response before the Put response,
   the leaseCache ends up caching the value written by the (out-of-date) Put in
   the cached key-value map. A future Get() operation on that leasing client
   then would incorrectly return a value for the key, when in reality the key is
   deleted on the server.

   This came up trying to understand the strange code written in
   leaseCache.Update(): if the current cached response for a key is "Not in KV
   map", Update() unconditionally records the (previously-Put) value,
   but then conditionally updates the ModRevision. Instead, it should probably
   check if (cacheResp.Header.Revision < respHeader.Revision), and only then
   update the cache. That's more like what leaseCache.Delete does.

   Solution: always use the response header revision number to decide whether to
   overwrite the currently cached value.
 *)

(* NOTE(bug): Concurrent Puts result in the version number temporarily being
  incorrect. The client increments Version number every time a `leaseCache.Update`
  happens, so if there were two concurrent Puts, there will be two increments.
  However, it is possible that the Put with a higher ModRevision is incorporated
  into the cache first, in which case its version number will temporarily be
  `oldVer + 1` and will only become the correct value `oldVer + 2` after the
  `leaseCache.Update` is called for the other Put.
  Solution: use `prev_kv` to deduce the current version number.
 *)

(* NOTE(bug): pretty sure Txns don't work correctly w.r.t concurrent Gets
   because they don't use waitc. Didn't set up a failing test case to confirm
   this. Just deleted the Txn implementation and tests. *)


(* NOTE(bug): Concurrent Get and Put on the same leasingKV can result in the Get
   returning stale information if the Put RPC doesn't get a response from the
   server, because it would evict the leaseEntry from the entries and close waitc.
   The Get() call would just read whatever was in the cache before. This could
   probably be triggered if the key got evicted during a Put() for other reasons
   too (e.g. a different client causing it to get revoked).
  `TestLeasingConcurrentPutGet`
   https://github.com/upamanyus/etcd/commit/e11ce2ae7d90f482814ff1a1f851179d36ff419f
   Possible solution: if key gets evicted from our cache somehow while doing the
   Put, then signal to any outstanding Get() call that the key is not cached.
*)

(* NOTE(bug): Two concurrent Puts can result in the cache being marked as "ok to
   read" even though one of the Puts is still in progress. Can try to create a
   failing test by getting Puts to linearize in the opposite order of their
   waitcs.
   Possible solution: get waitcs for all pending Puts for the key, and wait for them all
   to successfully finish before reading the cached value and returning.
 *)

(* NOTE(bug): Puts are not at-most-once. If the first Put RPC's response from
   the server is dropped, then the client will just make another Put RPC. So,
   e.g., the version number can increase by an arbitrary amount.
   Possible solution: distinguish a PutRPC error from a "Txn Succeeded == false" response.
*)

(* To simplify the proof for now, assuming that all keys are managed by
   leasingKV clients (i.e. the whole map is subject to the following
   protocol).

   The key being modified by `Put` must not have prefix `pfx`.
 *)

(*
Section protocol.

Context {W : Type} {W_eq_dec : EqDecision W} {W_countable : Countable W}.

Record LeasedValue :=
  {
    lv_rev : Z;
    lv_val : option go_string
  }.

Record LeasedEntry :=
  {
    le_lease_rev: Z;
    le_value : LeasedValue;
    le_waitc : W;
  }.

Global Instance settable_LeasedEntry : Settable LeasedEntry :=
  settable! Build_LeasedEntry < le_lease_rev; le_value; le_waitc >.

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
Proof. Admitted.

Definition own_cache_inv (γc : CacheNames) (c : CacheState) : iProp Σ.
Proof. Admitted.

Definition own_Locked (w : W) : iProp Σ.
Proof. Admitted.

Definition own_CanPut (w : W) (rev : Z) : iProp Σ.
Proof. Admitted.

Context (c c' : CacheState).
Context (s s' : EtcdState.t).
Context (γc : CacheNames) (γs : ServerNames).

Definition step_Lock (key : go_string) (w : W) (rev : Z) : Prop :=
  ∃ le,
  c.(entries) !! key = Some le ∧
  c.(waitc_map) !! w = None ∧
  rev = le.(le_lease_rev) ∧
  c' = c <| waitc_map := <[ w := false ]> c.(waitc_map) |>
         <| entries :=  <[key := le <| le_waitc := w |> ]> c.(entries) |>.

Lemma take_step_Lock (key : go_string) w rev :
  step_Lock key w rev →
  own_cache_inv γc c ==∗
  own_cache_inv γc c' ∗
  own_Locked w ∗
  own_Update rev.
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

Definition is_newer_response (lv : LeasedValue) (resp_rev : Z) : Prop :=
  lv.(lv_rev) ≤ resp_rev.

Definition step_Update key val resp_rev : Prop :=
  ∃ le,
  c.(entries) !! key = Some le ∧
  is_newer_response le.(le_value) resp_rev ∧
  c' = c <| entries := <[ key := le <| le_value := {| lv_rev := resp_rev; lv_val := val |} |> ]> c.(entries) |>.

Lemma take_step_Update key val resp_rev w rev :
  step_Update key val resp_rev →
  own_Locked w rev -∗
  own_cache_inv γs c ==∗
  own_cache_inv γs c'.

Definition close :

End protocol. *)
