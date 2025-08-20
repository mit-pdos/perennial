Require Import New.code.context.
Require Export New.generatedproof.context.
Require Import New.proof.proof_prelude.
Require Import New.proof.chan.
Require Import New.proof.sync.atomic New.proof.sync.

Require Import Perennial.Helpers.CountableTactics.

Class contextG Σ :=
  {
    closeable_inG :: closeable_chanG Σ
  }.

(* Context logical descriptor. *)
Module Context_desc.
Section defn.
Context `{ffi_syntax}.
(* Context `{hG: heapGS Σ, !ffi_semantics _ _}. *)
Context `{PROP : Type}.
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
      PDone: PROP;
    }.
Global Instance eta : Settable _ :=
  settable! mk <Values; Deadline; Done; PDone>.
End defn.
End Context_desc.

Section definitions.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.
Context `{contextG Σ}.

#[global] Instance : IsPkgInit time := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf time := build_get_is_pkg_init.

#[global] Instance : IsPkgInit reflectlite := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf reflectlite := build_get_is_pkg_init.

#[global] Instance : IsPkgInit errors := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf errors := build_get_is_pkg_init.

#[global] Instance : IsPkgInit context := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf context := build_get_is_pkg_init.

Import Context_desc.
Definition is_Context (c : interface.t) (s : Context_desc.t) : iProp Σ :=
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
    {{{ RET #s.(Done); True }}} ∗
  "#HErr" ∷
    (∀ cl,
    {{{ own_closeable_chan s.(Done) s.(PDone) cl }}}
      interface.get #"Err" #c #()
    {{{ err, RET #err;
        match cl with
        | closeable.Closed => ⌜ err ≠ interface.nil ⌝
        | _ => if decide (err = interface.nil) then own_closeable_chan s.(Done) s.(PDone) cl
              else own_closeable_chan s.(Done) s.(PDone) closeable.Closed
        end
    }}}) ∗
  "#HDone_ch" ∷ own_closeable_chan s.(Done) s.(PDone) closeable.Unknown.

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

Lemma wp_WithCancel PDone' (ctx : interface.t) ctx_desc :
  {{{
        is_Context ctx ctx_desc
  }}}
    @! context.WithCancel #ctx
  {{{
        ctx' done' (cancel : func.t), RET (#ctx', #cancel);
        {{{ PDone' }}} #cancel #() {{{ RET #(); True }}} ∗
        is_Context ctx' (ctx_desc <| PDone := ctx_desc.(PDone) ∨ PDone' |> <|Done := done'|> )
  }}}.
Proof.
Admitted.

End definitions.
