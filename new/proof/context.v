Require Import New.code.context.
Require Import New.generatedproof.context.
Require Import New.proof.proof_prelude.

Require Import Perennial.Helpers.CountableTactics.

Section chan.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Axiom own_chan :
  ∀ `{!IntoVal V} (c : chan.t) (buf : list V) (unbuf_entry : option V) (closed : bool), iProp Σ.

End chan.

Module Context_state.
Section defn.
Context `{ffi_syntax}.
(* FIXME: prove this and put it in golang directory. *)
Instance interface_countable : Countable interface.t.
Admitted.

Record t :=
  mk
    {
      Values : gmap interface.t interface.t;
      (* FIXME: *)
      (* Deadline : time.Time.t  *)
      Deadline : option w64;
      Done: chan.t;
    }.
End defn.
End Context_state.

Section definitions.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!goGlobalsGS Σ}.

#[global]
Program Instance : IsPkgInit context :=
  ltac2:(build_pkg_init ()).
Final Obligation. Proof. apply _. Qed.

Import Context_state.
Definition is_Context (c : interface.t) (s : Context_state.t) : iProp Σ :=
  "#HDeadline" ∷
    {{{ True }}}
      interface.get #"Deadline" #c #()
    {{{ RET (#(default (W64 0) s.(Deadline)),
             #(match s.(Deadline) with | None => false | _ => true end));
        True
    }}} ∗
  "#HDone" ∷
    {{{ True }}}
      interface.get #"Done" #c #()
    {{{ RET #s.(Done); True }}}.

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
then (cancel was run) ∨ (chan.is_closed ctx.Done). *)

Lemma wp_WithCancel N (ctx : interface.t) :
  {{{ True }}}
    func_call #context #"WithCancel" #ctx
  {{{
        ctx' ctx_state (cancel : func.t), RET (#ctx', #cancel);
        is_Context ctx' ctx_state ∗
        inv N (∃ closed, own_chan ctx_state.(Done) ([] : list unit) None closed)
  }}}.
Proof.
Admitted.

End definitions.
