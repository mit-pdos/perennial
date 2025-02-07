Require Import New.code.context.
Require Import New.generatedproof.context.
Require Import New.proof.proof_prelude.

Require Import Perennial.Helpers.CountableTactics.
Section definitions.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.

(* FIXME: prove this and put it in golang directory. *)
Instance interface_countable : Countable interface.t.
Admitted.

(* spec-level state of a Context is:
   Values : gmap
 *)
Record state :=
  {
    Values : gmap interface.t interface.t;
    (* FIXME: *)
    (* Deadline : time.Time.t  *)
    Deadline : option w64;
    Done: chan.t;
  }.
(*
From the docs for `WithCancel`:
 The returned context's Done channel is closed when the returned cancel function
 is called or when the parent context's Done channel is closed, whichever happens
 first.

From Context.Done() docs:
 The close of the Done channel may happen asynchronously,
 after the cancel function returns.

So, cannot prove that calling `cancel` actually causes anything to happen; that
would be a liveness property. But should be able to do the converse.

Should be able to prove that if the returned context's Done channel is closed,
then (cancel was run) ∨ (chan.is_closed ctx.Done).

Perhaps there should be a "done" predicate associated with channels? A thing
that must be true before a chan can be closed.

{{{ True }}}
  WithCancel(ctx)
{{{
  RET (#ctx, #cancel);
}}}

*)

End definitions.
