Require Export New.generatedproof.errors.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : errors.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

#[global] Instance : IsPkgInit (iProp Σ) errors := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) errors := build_get_is_pkg_init_wf.

Lemma wp_initialize' get_is_pkg_init :
  get_is_pkg_init_prop errors get_is_pkg_init →
  {{{ own_initializing get_is_pkg_init }}}
    errors.initialize' #()
  {{{ RET #(); own_initializing get_is_pkg_init ∗ is_pkg_init errors }}}.
Proof.
  intros Hinit. wp_start as "Hown".
  wp_apply (wp_package_init with "[$Hown] HΦ").
  { destruct Hinit as (-> & ?); done. }
  iIntros "Hown". wp_auto.
Admitted.

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

Lemma wp_New (msg : go_string) :
  {{{ is_pkg_init errors }}}
    @! errors.New #msg
  {{{ (err : interface.t_ok), RET #(interface.ok err); True }}}.
Proof.
  wp_start. wp_auto. wp_alloc x as "Hx". wp_auto. wp_end.
Qed.

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

Lemma wp_AsType (err : error.t) `[!ZeroVal T'] `[!TypedPointsto T'] `[!IntoValTyped T' T] :
  {{{ True }}}
    #(functions errors.AsType [T]) #err
  {{{ (e : T') (found : bool), RET (#e, #found); True }}}.
Proof.
  wp_start as "#Hunwrap".
  wp_auto. destruct err; wp_auto.
  2:{ wp_end. }
  wp_func_call. wp_call.
  wp_alloc ret2 as "ret2". wp_auto.
  wp_alloc ret1 as "ret1". wp_auto.
  wp_for.
Admitted.

End wps.
