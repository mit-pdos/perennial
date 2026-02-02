Require Export New.generatedproof.errors.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : errors.Assumptions}.
Local Set Default Proof Using "All".

#[global] Instance : IsPkgInit (iProp Σ) errors := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) errors := build_get_is_pkg_init_wf.

Definition is_unwrappable (err : error.t) : iProp Σ :=
  □(match err with
    | interface.nil => True
    | interface.ok ii =>
        if decide (method_set ii.(interface.ty) !! "Unwrap"%go = Some $ go.Signature [] false [go.error]) then
          ({{{ True }}}
             #(methods ii.(interface.ty) "Unwrap" ii.(interface.v)) #()
           {{{ err, RET #(interface.ok err); True }}})%I
        else True%I
    end).

Lemma wp_Unwrap (err : error.t) :
  {{{ is_unwrappable err }}}
    @! errors.Unwrap #err
  {{{ (err' : error.t), RET #err'; True }}}.
Proof.
  wp_start as "#Hunwrap". wp_auto. destruct err; simpl.
  2:{ (* err is nil *) wp_auto. wp_end. }
  destruct go.type_set_contains eqn:Hhas_unwrap.
  - (* err has an Unwrap function *)
    rewrite /go.type_set_contains go.is_underlying /= in Hhas_unwrap.
    rewrite andb_true_r in Hhas_unwrap. rewrite bool_decide_eq_true in Hhas_unwrap.
    rewrite decide_True //. wp_auto. wp_apply "Hunwrap" as "% _". wp_end.
  - wp_auto. wp_end.
Qed.

End wps.
