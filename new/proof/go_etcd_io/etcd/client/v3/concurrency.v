Require Import New.code.go_etcd_io.etcd.client.v3.concurrency.
Require Import New.generatedproof.go_etcd_io.etcd.client.v3.concurrency.
Require Import New.proof.proof_prelude.
Require Import New.proof.go_etcd_io.etcd.client.v3.
From New.proof Require Import context sync.
From New.proof Require Export chan.

Ltac2 Set wp_apply_auto_default := Ltac2.Init.false.

Class concurrencyG Σ :=
  {
    donecG :: closeable_chanG Σ ;
    (* context_inG :: contextG Σ; *)
    clientv3_inG :: clientv3G Σ;
  }.

Section proof.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.

Context `{!globalsGS Σ} {go_ctx : GoContext}.
Context `{concurrencyG Σ}.

(* FIXME: move these *)
Local Notation deps_math := (ltac2:(build_pkg_init_deps 'math) : iProp Σ) (only parsing).
#[global] Program Instance : IsPkgInit math :=
  {|
    is_pkg_init_def := True;
    is_pkg_init_deps := deps_math;
  |}.

Local Notation deps_zapcore := (ltac2:(build_pkg_init_deps 'zapcore) : iProp Σ) (only parsing).
#[global] Program Instance : IsPkgInit zapcore :=
  {|
    is_pkg_init_def := True;
    is_pkg_init_deps := deps_zapcore;
  |}.

Local Notation deps_zap := (ltac2:(build_pkg_init_deps 'zap) : iProp Σ) (only parsing).
#[global] Program Instance : IsPkgInit zap :=
  {|
    is_pkg_init_def := True;
    is_pkg_init_deps := deps_zap;
  |}.

Local Notation deps_time := (ltac2:(build_pkg_init_deps 'time) : iProp Σ) (only parsing).
#[global] Program Instance : IsPkgInit time :=
  {|
    is_pkg_init_def := True;
    is_pkg_init_deps := deps_time;
  |}.

Local Notation deps_strings := (ltac2:(build_pkg_init_deps 'strings) : iProp Σ) (only parsing).
#[global] Program Instance : IsPkgInit strings :=
  {|
    is_pkg_init_def := True;
    is_pkg_init_deps := deps_strings;
  |}.

Local Notation deps_fmt := (ltac2:(build_pkg_init_deps 'fmt) : iProp Σ) (only parsing).
#[global] Program Instance : IsPkgInit fmt :=
  {|
    is_pkg_init_def := True;
    is_pkg_init_deps := deps_fmt;
  |}.

Local Notation deps_errors := (ltac2:(build_pkg_init_deps 'errors) : iProp Σ) (only parsing).
#[global] Program Instance : IsPkgInit errors :=
  {|
    is_pkg_init_def := True;
    is_pkg_init_deps := deps_errors;
  |}.

Local Notation deps_concurrency := (ltac2:(build_pkg_init_deps 'concurrency) : iProp Σ) (only parsing).
#[global] Program Instance : IsPkgInit concurrency :=
  {|
    is_pkg_init_def := True;
    is_pkg_init_deps := deps_concurrency;
  |}.

Definition is_Session (s : loc) γ (lease : clientv3.LeaseID.t) : iProp Σ :=
  ∃ cl donec,
  "#client" ∷ s ↦s[concurrency.Session :: "client"]□ cl ∗
  "#id" ∷ s ↦s[concurrency.Session :: "id"]□ lease ∗
  "#Hclient" ∷ is_Client cl γ ∗
  "#Hlease" ∷ is_etcd_lease γ lease ∗
  "#donec" ∷ s ↦s[concurrency.Session :: "donec"]□ donec ∗
  (* One can keep calling receive, and the only thing they might get back is a
     "closed" value. *)
  "#Hdonec" ∷ own_closeable_chan donec True closeable.Unknown.

#[global] Opaque is_Session.
#[local] Transparent is_Session.
#[global] Instance is_Session_pers s γ lease : Persistent (is_Session s γ lease) := _.

Lemma wp_NewSession (client : loc) γetcd :
  {{{
        is_pkg_init concurrency ∗
        "#His_client" ∷ is_Client client γetcd
  }}}
    @! concurrency.NewSession #client #slice.nil
  {{{ s err, RET (#s, #err);
      if decide (err = interface.nil) then
        ∃ lease, is_Session s γetcd lease
      else
        True
  }}}.
Proof.
  wp_start. iNamed "Hpre".
  wp_auto.
  wp_apply (wp_Client__GetLogger with "[$]") as "% _". wp_auto.
  wp_apply (wp_Client__Ctx with "[$]") as "% % #Hcontext". wp_auto.
  wp_alloc ops as "Hops".
  wp_auto.
  (* only consider nil options *)
  wp_apply wp_slice_for_range.
  { instantiate (1:=[] : list concurrency.SessionOption.t ). instantiate (1:=DfracOwn 1).
    Unshelve. all: try apply _.
    iApply own_slice_nil. }
  iEval simpl.
  iIntros "_".

  wp_auto.
  wp_apply (wp_Client__Grant with "[$]") as "* [Hresp Hl]". wp_auto.
  destruct bool_decide eqn:Herr.
  2:{ (* got an error; early return *)
    wp_auto.
    iApply "HΦ".
    rewrite bool_decide_eq_false in Herr.
    destruct decide; done.
  }
  (* no error from Grant() call *)
  rewrite bool_decide_eq_true in Herr. subst.
  wp_auto.
  rewrite decide_True //.
  iClear "err". clear err_ptr.
  iDestruct "Hl" as "#Hlease0".
  wp_apply (wp_WithCancel True) as "* (Hcancel & Hctx)".
  { iFrame "#". }
  wp_auto.

  wp_apply (wp_Client__KeepAlive with "[$]") as "* #Hkch".
  wp_auto. rewrite bool_decide_decide. destruct decide.
  2:{ (* error *)
    wp_auto. wp_apply "Hcancel". wp_auto. iApply "HΦ".
    rewrite decide_False //.
  }
  iDestruct "Hkch" as "#[Hkch #Hkrecv]".
  wp_auto.
  rewrite bool_decide_decide. destruct decide.
  {
    (* NOTE: if `clientv3.lessor.KeepAlive` returns `nil` for its error, it is guaranteed to
       return a non-nil chan, so this case is impossible. *)
    iDestruct (is_chan_not_nil with "Hkch") as %hbad.
    done.
  }
  wp_auto.
  wp_apply (wp_chan_make (V:=())) as "* Hdonec".
  wp_auto.
  rename s into ctx_desc.
  wp_alloc s as "Hs".
  wp_auto.
  iPersist "cancel donec keepAlive".
  iMod (alloc_closeable_chan True with "Hdonec") as "Hdonec_open"; [done..|].
  iDestruct (own_closeable_chan_Unknown with "[$]") as "#?".
  rewrite -wp_fupd.
  wp_apply (wp_fork with "[Hdonec_open Hcancel]").
  {
    wp_auto. wp_apply wp_with_defer as "%defer defer".
    simpl subst.
    wp_auto.
    wp_for_chan.
    iAssert _ with "Hkrecv" as "Hkrecv1".
    iMod "Hkrecv1" as "(% & ? & Hkrecv1)".
    iFrame. iModIntro. iNext.
    destruct decide.
    {
      iIntros "?".
      iMod ("Hkrecv1" with "[$]") as "_".
      iModIntro.
      wp_auto.
      wp_apply (wp_closeable_chan_close with "[$Hdonec_open]") as "_".
      { iFrame "#". done. }
      wp_auto. wp_apply "Hcancel". wp_auto.
      done.
    }
    {
      iIntros "?".
      iMod ("Hkrecv1" with "[$]") as "_".
      iModIntro.
      iMod "Hkrecv" as "(% & $ & Hkrecv)".
      iModIntro. iNext.
      iIntros "* _ ?".
      iMod ("Hkrecv" with "[$]") as "_".
      iModIntro.
      wp_auto.
      wp_for_chan_post.
      iFrame.
    }
  }
  iDestruct (struct_fields_split with "Hs") as "hs".
  simpl. iClear "Hctx". iNamed "hs".
  iPersist "Hclient Hid Hdonec".
  wp_auto. iModIntro.
  iApply "HΦ".
  rewrite decide_True //.
  iFrame "#".
Qed.

Lemma wp_Session__Lease s γ lease :
  {{{ is_pkg_init concurrency ∗ is_Session s γ lease }}}
    s @ (ptrT.id concurrency.Session.id) @ "Lease" #()
  {{{ RET #lease; True }}}.
Proof.
  wp_start. iNamed "Hpre". wp_auto. by iApply "HΦ".
Qed.

Lemma wp_Session__Done s γ lease :
  {{{ is_pkg_init concurrency ∗ is_Session s γ lease }}}
    s @ (ptrT.id concurrency.Session.id) @ "Done" #()
  {{{ ch, RET #ch; own_closeable_chan ch True closeable.Unknown }}}.
Proof.
  wp_start. iNamed "Hpre". wp_auto. by iApply "HΦ".
Qed.

End proof.
