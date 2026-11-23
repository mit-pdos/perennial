# `WithCancel` over any `isContext` parent keeps the parent's Done proposition

- **Date:** 2026-11-15. **Branch:** `ctx-withcancel-parent-done`, off `lean` at `ddc0f0acc`
  (commits `cbccb8321`, `2d8857406`). Tier 3 only: proofs and proved specs, no trusted-base change.
- **Asked by:** etcd-grove (k8s 7f-5a: `wc.ctx = WithCancel(WithRequireLeader(ctx))`, whose closed
  Done channel must witness the watch's cancellation).

## The change

`wp_WithCancel_any` gave the child of a general `isContext` parent the Done proposition `True`.
`isContext` now states two more things of a context `c` described by `s`:

- `"#HParentCC"`: the `*cancelCtx` `p` that `parentCancelCtx(c)` finds comes as
  `isCancelCtxOf p γp Pp` with `□ (□ Pp -∗ s.PDone)`. Go's `parentCancelCtx` returns `p` only when
  `p.done` is `c`'s Done channel (`pdone == done`). So `p`'s cancellation closes `c`'s channel, and
  what `p.cancel` needs (`□ Pp`) must give what `c`'s closing promises (`□ s.PDone`).
- `"#HErrDone"`: once `c` is done, `Err()` also gives `□ s.PDone`. A child that `propagateCancel`
  cancels at once (its parent already done) needs this. In the branch where the parent's channel is
  `closedchan` there is no other source: `closedchanN` is inside `nroot`, so the broadcast and
  `closedchan` invariants cannot be opened together. `"#HErr"` already promised `□ s.PDone` for every
  non-nil error at `cl ≠ Done`.

New results: `wp_WithCancel_ctx`, `wp_propagateCancel_ctx`, `childCancelSpec_mono`. The third case of
`context.cancelCtx.propagateCancel.spec` becomes `childCancelSpec s.PDone k`, which generalizes
`childCancelSpec True k`. `wp_WithCancel_any` and `wp_propagateCancel_any` keep their statements as
corollaries.

## What the stronger `isContext` claims of contexts made outside Perennial (axiom audit)

Every context the model makes satisfies the new clauses by proof: a `*cancelCtx` with `Pp = s.PDone`,
whose `err` cell already holds `□ P`; a `*timerCtx` with `s.PDone = True`; and `isContext_weaken`.
Perennial has no axiom, `assume` or `sorry` that mentions `isContext`. A downstream axiom that
*produces* `isContext`, as a post or in a positive position of a nested triple, now claims the two
clauses too.

The audit covered etcd-grove at `fa4909047e`: every axiom of `Proof/`, `Spec/`, `TrustedCode/`,
`RaftWitness/`, `PorcupineDag/`, with its `.spec` resolved, and every predicate whose definition
mentions `isContext`, followed through definitions. It found these producers, falling into three
kinds.

1. **Transfers over a delegating wrapper.** Each states
   `isContext ctx cd ⊢ isContext ctx' { cd with Values := vs }`: same Done proposition, same Done
   channel.
   - `metadata.AppendToOutgoingContext`;
   - `context.WithValue` (etcd's keys);
   - `traceutil.Tracer.Start` (the tracer's `ContextWithSpan`, a `context.WithValue`).

   In Go, `ctx'` is a `*valueCtx` around `ctx`. `Done`, `Err` and `Deadline` are promoted from the
   embedded `Context`. `Value(&cancelCtxKey)` delegates to `ctx` through `value`. So
   `parentCancelCtx(ctx')` reads the same channel and finds the same `p`, and `ctx'.Err()` is
   `ctx.Err()`. Both new clauses for `ctx'` are `ctx`'s, at the same `cd.PDone`: **true**.

   `WithRequireLeader.spec` (T5-e) states its parts as WP transfers that hold for any
   postcondition, for `Done`, `Err`, `Value(&cancelCtxKey)`, `Deadline` and `parentCancelCtx`.
   `WithRequireLeader.isContext_of_post` is a *proved* theorem that builds `isContext` from them. It
   builds unchanged against this branch, so the axiom claims nothing new.

2. **Done proposition `True`.**
   - `context.WithCancelTodo`;
   - `context.WithCancelValCtx`;
   - `WithRequireLeader`'s background branch (`WithCancel` of its result).

   At `PDone = True` the new clauses are `□ (□ Pp -∗ True)` and `□ True`: **trivially true**.

3. **Existential descriptor.** Each claims `∃ cd, isContext ctx cd`.
   - `context.WithTimeoutBackgroundMd` (`∃ cd`);
   - grpc's server run and stream contexts, through `grpc.model.acceptRun` and
     `acceptRunConns` (`grpcAccepted`: `∃ ci cd, isContext ci cd ∗ …`, unary and stream; also
     `srvRawStreamIs`);
   - the client stream's `Context()`, through `grpc.ClientConn.NewStream` (`cliStreamIs … cd'` with
     `cd'` existential).

   The old `isContext` at any `cd` gives the new one at `{ cd with PDone := True }`: weaken, then the
   new clauses are trivial. So each existential claim is **still true**. The other fields (deadline,
   values) are unchanged.

Every other occurrence is a premise (consumed, so a stronger `isContext` only makes the assumption
harder to meet):
- `metadata.FromOutgoingContext`, `rate.Limiter.Wait`, `EtcdServer.leaseTimeToLive`;
- the `ctxOk` callers (`withVersion`, `waitRetryBackoff`, `tracing.Start`, `ClientConn.Invoke`'s
  `grpcInvokerOk`);
- the prometheus interceptors (`srvInterceptorOk`, `srvStreamInterceptorOk`, which pass the same
  `ci cd` on);
- the server bundles (`isServerReqM`, …: `isContext` only in the preconditions of their nested
  triples).

**Result: clean.** No trust-boundary axiom becomes false. None with a non-trivial Done proposition
claims more than its wrapped context already gave.

Downstream proof changes for the pin bump: 2 files in etcd-grove (`SrvCtxWeak.lean`'s
`srvCtxWeak_of_isContext`, and one intro pattern in `cancellableContext__Err.lean`). All 56 modules
that mention the changed parts build with them (closure 4828 jobs).
