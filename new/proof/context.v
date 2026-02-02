From New Require Import code.context.
From New Require Export generatedproof.context.
From New Require Import proof.proof_prelude.
From New.proof Require Import sync.atomic sync time errors.
From New.proof Require Import chan_proof.closeable.

Require Import Perennial.Helpers.CountableTactics.

Class contextG Σ :=
  {
    #[local] context_closeableG :: closeable_chanG Σ;
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
      Done_gn : chan_names;
      PDone: PROP;
    }.
Global Instance eta : Settable _ :=
  settable! mk <Values; Deadline; Done; Done_gn; PDone>.
End defn.
End Context_desc.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : context.Assumptions}.
Context `{!contextG Σ}.

#[global] Instance : IsPkgInit (iProp Σ) context := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) context := build_get_is_pkg_init_wf.

Import Context_desc.
Definition is_Context (c : interface.t_ok) (s : Context_desc.t) : iProp Σ :=
  "#HDeadline" ∷
    {{{ True }}}
      #(methods c.(interface.ty) "Deadline" c.(interface.v)) #()
    {{{ RET (#(default (zero_val time.Time.t) s.(Deadline)),
             #(match s.(Deadline) with | None => false | _ => true end));
        True
    }}} ∗
  "#HDone" ∷
    {{{ True }}}
      #(methods c.(interface.ty) "Done" c.(interface.v)) #()
    {{{ RET #s.(Done); True }}} ∗
  "#HErr" ∷
    (∀ cl,
    {{{ own_closeable_chan s.(Done) s.(Done_gn) s.(PDone) cl }}}
      #(methods c.(interface.ty) "Err" c.(interface.v)) #()
    {{{ err, RET #err;
        match cl with
        | closeable.Closed => ⌜ err ≠ interface.nil ⌝
        | _ => if decide (err = interface.nil) then own_closeable_chan s.(Done) s.(Done_gn) s.(PDone) cl
              else own_closeable_chan s.(Done) s.(Done_gn) s.(PDone) closeable.Closed
        end
    }}}) ∗
  "#HDone_ch" ∷ own_closeable_chan s.(Done) s.(Done_gn) s.(PDone) closeable.Unknown.
#[global] Typeclasses Opaque is_Context.
#[global] Opaque is_Context.

#[global] Transparent is_Context.
#[global] Typeclasses Transparent is_Context.

Lemma wp_Cause ctx ctx_desc :
  {{{
        is_pkg_init context ∗
        "#Hctx" ∷ is_Context ctx ctx_desc
  }}}
    @! context.Cause #(interface.ok ctx)
  {{{ (err : interface.t), RET #err; True }}}.
Proof.
  wp_start. iNamed "Hpre".
  wp_auto.
  (* Context.Value spec *)
Admitted.

Lemma wp_parentCancelCtx parent parent_desc :
  {{{
        is_pkg_init context ∗
        "#Hctx" ∷ is_Context parent parent_desc
  }}}
    @! context.parentCancelCtx #(interface.ok parent)
  {{{
        ctx (ok : bool), RET (#ctx, #ok);
        if ok then
          ∃ (c : context.cancelCtx.t),
            ctx ↦ c
        else ⌜ ctx = null ⌝
  }}}.
Proof.
Admitted.

Lemma wp_propagateCancel (c : loc) parent parent_desc child :
  {{{
        is_pkg_init context ∗
        "Hparent" ∷ is_Context parent parent_desc ∗
        "Hc" ∷ c ↦ (zero_val context.cancelCtx.t)
  }}}
    c @! (go.PointerType context.cancelCtx) @! "propagateCancel" #(interface.ok parent) #(interface.ok child)
  {{{
        RET #(); True
  }}}.
Proof.
  wp_start. iNamed "Hpre". wp_auto.
  iNamed "Hparent".
  wp_apply "HDone".
  rewrite bool_decide_decide. case_decide.
  { wp_auto. by iApply "HΦ". }
  wp_auto.
  wp_apply (chan.wp_select_nonblocking_alt [True]%I with "[] [-]").
  2: iNamedAccu.
  { (* case: done channel closed*)
    simpl. iSplit; last done.
    repeat iExists _. iSplitR; first done. iFrame "#".
    iSplitR; first admit. (* absorb is_chan into au? *)
    iApply (own_closeable_chan_nonblocking_receive with "[$]").
    iSplit.
    2:{ iIntros. done. }
    iIntros "#Hclosed".
    iNamed 1.
    wp_auto. wp_apply ("HErr" with "[$Hclosed]") as "% %HparentErr".
    wp_apply (wp_Cause with "[$]") as "% _".
    (* TODO spec for canceler. *)
    admit.
  }
  iNamed 1. iIntros "_".
  wp_auto.
  wp_apply (wp_parentCancelCtx with "[$]") as "* Hp".
  wp_if_destruct.
  { (* parent is or derives from a *cancelCtx *)
    (* TODO invariant for cancelCtx *)
    admit.
  }
  destruct go.type_set_contains eqn:Hafter.
  {
    wp_auto.
    (* XXX: mutex seems unnecessary here, because this is never called
       concurrently with other methods on `c`. *)
    (* TODO: afterFuncer spec *)
    admit.
  }
  wp_auto.
  (* TODO: pkg invariant owns `goroutines` global variable. *)
Admitted.

Lemma wp_withCancel PDone' ctx ctx_desc :
  {{{
        is_pkg_init context ∗ is_Context ctx ctx_desc
  }}}
    @! context.withCancel #(interface.ok ctx)
  {{{
        ctx' done' (cancel : func.t), RET (#ctx', #cancel);
        {{{ PDone' }}} #cancel #() {{{ RET #(); True }}} ∗
        is_Context ctx' (ctx_desc <| PDone := ctx_desc.(PDone) ∨ PDone' |> <|Done := done'|> )
  }}}.
Proof.
Abort.

Lemma wp_WithCancel PDone' ctx ctx_desc :
  {{{
        is_pkg_init context ∗ is_Context ctx ctx_desc
  }}}
    @! context.WithCancel #(interface.ok ctx)
  {{{
        ctx' done' (cancel : func.t), RET (#ctx', #cancel);
        {{{ PDone' }}} #cancel #() {{{ RET #(); True }}} ∗
        is_Context ctx' (ctx_desc <| PDone := ctx_desc.(PDone) ∨ PDone' |> <|Done := done'|> )
  }}}.
Proof.
Admitted.

Lemma wp_WithDeadlineCause parent parent_desc (d : time.Time.t) (cause : error.t):
  {{{
        is_pkg_init context ∗ is_Context parent parent_desc
  }}}
    @! context.WithDeadlineCause #(interface.ok parent) #d #cause
  {{{
        ctx' done' (cancel : func.t), RET (#ctx', #cancel);
        {{{ True }}} #cancel #() {{{ RET #(); True }}} ∗
        is_Context ctx' (parent_desc <| Deadline := Some d |> <| PDone := True |> <|Done := done'|>)
  }}}.
Proof.
Admitted.

Lemma wp_WithDeadline parent parent_desc (d : time.Time.t) :
  {{{
        is_pkg_init context ∗ is_Context parent parent_desc
  }}}
    @! context.WithDeadline #(interface.ok parent) #d
  {{{
        ctx' done' (cancel : func.t), RET (#ctx', #cancel);
        {{{ True }}} #cancel #() {{{ RET #(); True }}} ∗
        is_Context ctx' (parent_desc <| Deadline := Some d |> <| PDone := True |> <|Done := done'|>)
  }}}.
Proof.
Admitted.

Lemma wp_WithTimeout parent parent_desc (timeout : time.Duration.t) :
  {{{
        is_pkg_init context ∗ is_Context parent parent_desc
  }}}
    @! context.WithTimeout #(interface.ok parent) #timeout
  {{{
        ctx' done' (cancel : func.t) d, RET (#ctx', #cancel);
        {{{ True }}} #cancel #() {{{ RET #(); True }}} ∗
        is_Context ctx' (parent_desc <| Deadline := Some d |> <| PDone := True |> <|Done := done'|>)
  }}}.
Proof.
Admitted.

End wps.
