From New.proof Require Import proof_prelude.

From New.proof Require Import sync.atomic strings fmt sync time
  chan_proof.closeable.
From New.generatedproof.github_com.goose_lang.goose.testdata.examples.channel
  Require Import etcd_session.

From New.proof.github_com.goose_lang.goose.model.channel Require Import idioms.
Import bag.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : etcd_session.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

#[global] Instance : IsPkgInit (iProp Σ) etcd_session := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) etcd_session := build_get_is_pkg_init_wf.

Lemma wp_initialize' get_is_pkg_init :
  get_is_pkg_init_prop etcd_session get_is_pkg_init →
  {{{ own_initializing get_is_pkg_init }}}
    etcd_session.initialize' #()
  {{{ RET #(); own_initializing get_is_pkg_init ∗ is_pkg_init etcd_session }}}.
Proof.
  intros Hinit. wp_start as "Hown".
  wp_apply (wp_package_init with "[$Hown] HΦ").
  { destruct Hinit as (-> & ?). reflexivity. }
  iIntros "Hown". wp_auto.
  wp_apply wp_GlobalAlloc as "?".
  wp_apply wp_GlobalAlloc as "?".
  wp_apply (primitive.wp_initialize' with "[$Hown]") as "(Hown & #?)".
  { naive_solver. }
  wp_apply (time.wp_initialize' with "[$Hown]") as "(Hown & #?)".
  { naive_solver. }
  wp_apply (sync.wp_initialize' with "[$Hown]") as "(Hown & #?)".
  { naive_solver. }
  wp_apply (errors.wp_initialize' with "[$Hown]") as "(Hown & #?)".
  { naive_solver. }

  wp_apply chan.wp_make1 as "* (? & % & ?)".
  iEval (rewrite is_pkg_init_unfold /=). iFrame "∗#". done.
Qed.

Record etcd_session_names :=
  {
  }.

Lemma wp_newSession :
  {{{ is_pkg_init etcd_session }}}
    @! etcd_session.newSession #()
  {{{ (err : error.t), RET #err; True }}}.
Proof.
  wp_start. wp_apply primitive.wp_RandomUint64 as "% _". wp_if_destruct.
  { wp_apply errors.wp_New as "% _". wp_end. }
  { wp_end. }
Qed.

End wps.
