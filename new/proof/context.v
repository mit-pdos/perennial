From New Require Import code.context.
From New Require Export generatedproof.context.
From New Require Import proof.proof_prelude.
From New.proof Require Import sync.atomic sync time errors.
(* make sure to use these specs *)
From New.proof Require Import chan.

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
Record t :=
  mk
    {
      Values : gmap interface.t interface.t;
      Deadline : option time.Time.t;
      Done: chan.t;
      PDone: PROP;
    }.
Global Instance eta : Settable _ :=
  settable! mk <Values; Deadline; Done; PDone>.
End defn.
End Context_desc.

Section wps.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.
Context `{contextG Σ}.

#[global] Instance : IsPkgInit context := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf context := build_get_is_pkg_init_wf.

Import Context_desc.
Definition is_Context (c : interface.t) (s : Context_desc.t) : iProp Σ :=
  "%Hnotnil" ∷ ⌜ c ≠ interface.nil ⌝ ∗
  "#HDeadline" ∷
    {{{ True }}}
      interface.get #"Deadline" #c #()
    {{{ RET (#(default (default_val time.Time.t) s.(Deadline)),
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
#[global] Typeclasses Opaque is_Context.
#[global] Opaque is_Context.

#[global] Transparent is_Context.
#[global] Typeclasses Transparent is_Context.

Lemma wp_propagateCancel (c : loc) (parent : context.Context.t) parent_desc
  (child : context.canceler.t) :
  {{{
        is_pkg_init context ∗
        "Hparent" ∷ is_Context parent parent_desc ∗
        "Hc" ∷ c ↦ (default_val context.cancelCtx.t)
  }}}
    c @ (ptrT.id context.cancelCtx.id) @ "propagateCancel" #parent #child
  {{{
        RET #(); True
  }}}.
Proof.
  wp_start. iNamed "Hpre". (* wp_auto.
  iNamed "Hparent".
  wp_apply "HDone".
  rewrite bool_decide_decide. case_decide.
  { wp_auto. by iApply "HΦ". }
  wp_auto.
  wp_apply (wp_chan_select_nonblocking [True]%I).
  { done. }
  iSplit.
  {
    simpl. iSplit; last done.
    iExists unit, _, _.
    iApply own_closeable_chan_nonblocking_receive.
    { iFrame "#". }
    simpl.
    iClear "HDone_ch". iSplit. 2:{ iIntros "_". done. } iIntros "#HDone_ch".
    wp_auto. wp_apply "HErr". { iFrame "#". } iIntros "% %Herr". wp_auto.
  (* TODO: interesting pattern with interfaces. In a slightly more general form
     than it appears here:
     Package A defines an interface type `IT`. Package B defines a private type
     `b` that implements the interface. It defines some functions that take an
     `IT` and cast it into a `b`. The interface representation predicate would,
     in that case, have to contain the representation predicate for b inside it.
     One could coordinate this by having a a ghost resource track the per-type
     repr predicate, and conversion to an interface requires knowledge of tha
     typeId's predicate. This would be unfortunate for all the cases that have a
     trivial predicate.

     In this particular proof, the definition of `is_Context` can include
     special cases for the types defined within this pacakge. The more general
     thing would be needed if a higher-level package defined a new private
     implementation of `Context` and relied on type casting.
   *)
   *)
Abort.

Lemma wp_withCancel PDone' (ctx : interface.t) ctx_desc :
  {{{
        is_pkg_init context ∗ is_Context ctx ctx_desc
  }}}
    @! context.withCancel #ctx
  {{{
        ctx' done' (cancel : func.t), RET (#ctx', #cancel);
        {{{ PDone' }}} #cancel #() {{{ RET #(); True }}} ∗
        is_Context ctx' (ctx_desc <| PDone := ctx_desc.(PDone) ∨ PDone' |> <|Done := done'|> )
  }}}.
Proof.
Abort.

Lemma wp_WithCancel PDone' (ctx : interface.t) ctx_desc :
  {{{
        is_pkg_init context ∗ is_Context ctx ctx_desc
  }}}
    @! context.WithCancel #ctx
  {{{
        ctx' done' (cancel : func.t), RET (#ctx', #cancel);
        {{{ PDone' }}} #cancel #() {{{ RET #(); True }}} ∗
        is_Context ctx' (ctx_desc <| PDone := ctx_desc.(PDone) ∨ PDone' |> <|Done := done'|> )
  }}}.
Proof.
Admitted.

Lemma wp_WithDeadlineCause (parent: interface.t) parent_desc (d : time.Time.t) (cause : error.t):
  {{{
        is_pkg_init context ∗ is_Context parent parent_desc
  }}}
    @! context.WithDeadlineCause #parent #d #cause
  {{{
        ctx' done' (cancel : func.t), RET (#ctx', #cancel);
        {{{ True }}} #cancel #() {{{ RET #(); True }}} ∗
        is_Context ctx' (parent_desc <| Deadline := Some d |> <| PDone := True |> <|Done := done'|>)
  }}}.
Proof.
Admitted.

Lemma wp_WithDeadline (parent: interface.t) parent_desc (d : time.Time.t) :
  {{{
        is_pkg_init context ∗ is_Context parent parent_desc
  }}}
    @! context.WithDeadline #parent #d
  {{{
        ctx' done' (cancel : func.t), RET (#ctx', #cancel);
        {{{ True }}} #cancel #() {{{ RET #(); True }}} ∗
        is_Context ctx' (parent_desc <| Deadline := Some d |> <| PDone := True |> <|Done := done'|>)
  }}}.
Proof.
Admitted.

Lemma wp_WithTimeout (parent: interface.t) parent_desc (timeout : time.Duration.t) :
  {{{
        is_pkg_init context ∗ is_Context parent parent_desc
  }}}
    @! context.WithTimeout #parent #timeout
  {{{
        ctx' done' (cancel : func.t) d, RET (#ctx', #cancel);
        {{{ True }}} #cancel #() {{{ RET #(); True }}} ∗
        is_Context ctx' (parent_desc <| Deadline := Some d |> <| PDone := True |> <|Done := done'|>)
  }}}.
Proof.
Admitted.

End wps.
