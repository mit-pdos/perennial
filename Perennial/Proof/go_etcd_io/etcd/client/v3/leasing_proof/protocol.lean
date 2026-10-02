/-
Port of `new/proof/go_etcd_io/etcd/client/v3/leasing_proof/protocol.v`.

The Rocq file consists of notes about bugs found in the leasing KV client and
a protocol sketch that is entirely commented out; there is nothing to port
beyond the imports and the notes.

* NOTE(bug): the original leasingkv does not correctly check for lease
  expiration when handling a Get().
* NOTE(bug): Concurrent delete and puts with the same leasingKV are not handled
  properly (permanent cache inconsistency), `TestLeasingConcurrentPutDelete`,
  https://github.com/upamanyus/etcd/commit/174a964e806707b9fde186ade4b12be61967e9ea.
  Solution: always use the response header revision number to decide whether
  to overwrite the currently cached value.
* NOTE(bug): Concurrent Puts result in the version number temporarily being
  incorrect. Solution: use `prev_kv` to deduce the current version number.
* NOTE(bug): Txns don't work correctly w.r.t concurrent Gets because they don't
  use waitc (the Txn implementation and tests were deleted).
* NOTE(bug): Concurrent Get and Put on the same leasingKV can result in the Get
  returning stale information if the Put RPC doesn't get a response from the
  server, `TestLeasingConcurrentPutGet`,
  https://github.com/upamanyus/etcd/commit/e11ce2ae7d90f482814ff1a1f851179d36ff419f.
* NOTE(bug): Two concurrent Puts can result in the cache being marked as "ok to
  read" even though one of the Puts is still in progress.
* NOTE(bug): Puts are not at-most-once.
* NOTE(bug?): Get checks for lease validity first, then it checks for ongoing
  Puts and waits for them to be finished. However, it is possible that the
  session that's ready is a *new* session.

To simplify the proof for now (Rocq), all keys are assumed to be managed by
leasingKV clients; the key being modified by `Put` must not have prefix `pfx`.
-/
import Perennial.Proof.ProofPrelude
import Perennial.Proof.go_etcd_io.etcd.client.v3
