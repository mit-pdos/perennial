Require Import New.code.go_etcd_io.etcd.client.v3.concurrency.
Require Import New.generatedproof.go_etcd_io.etcd.client.v3.concurrency.
Require Import New.proof.proof_prelude.
Require Import New.proof.go_etcd_io.etcd.client.v3.
From New.proof Require Import context sync time math errors fmt chan_proof.closeable.

Ltac2 Set wp_apply_auto_default := Ltac2.Init.false.

Section proof.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : concurrency.Assumptions}.
Collection W := sem + package_sem.
Local Set Default Proof Using "W".

#[global] Instance : IsPkgInit (iProp Σ) zapcore := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) zapcore := build_get_is_pkg_init_wf.
Context `{concurrencyG Σ}.

(* FIXME: move these *)
#[global] Instance : IsPkgInit (iProp Σ) zapcore := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) zapcore := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit (iProp Σ) zap := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) zap := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit (iProp Σ) strings := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) strings := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit (iProp Σ) concurrency := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) concurrency := build_get_is_pkg_init_wf.

Definition is_Session (s : loc) γ (lease : clientv3.LeaseID.t) : iProp Σ :=
  ∃ cl donec γdonec,
  "#client" ∷ s.[concurrency.Session.t, "client"] ↦□ cl ∗
  "#id" ∷ s.[concurrency.Session.t, "id"] ↦□ lease ∗
  "#Hclient" ∷ is_Client cl γ ∗
  "#Hlease" ∷ is_etcd_lease γ lease ∗
  "#donec" ∷ s.[concurrency.Session.t, "donec"] ↦□ donec ∗
  (* One can keep calling receive, and the only thing they might get back is a
     "closed" value. *)
  "#Hdonec" ∷ own_closeable_chan donec γdonec True closeable.Unknown.

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
  wp_for "i".
  (* TODO: wp_method_call seems to be broken here *)
  (*
  wp_if_destruct; [word|].
  wp_apply (wp_Client__Grant with "[$]") as "* [Hresp Hl]". wp_auto.
  destruct err.
  { (* got an error; early return *)
    wp_auto.
    iApply "HΦ".
    destruct decide; done.
  }
  (* no error from Grant() call *)
  wp_auto.
  rewrite decide_True //.
  iDestruct "Hl" as "#Hlease0".
  wp_apply (wp_WithCancel True) as "* (Hcancel & Hctx)".
  { iFrame "#". }
  wp_auto.

  wp_apply (wp_Client__KeepAlive with "[$]") as "* #Hkch".
  wp_auto. destruct err.
  { (* error *)
    wp_auto. wp_apply "Hcancel". wp_auto. iApply "HΦ".
    rewrite decide_False //. rewrite decide_False //.
  }
  rewrite decide_True //.
  wp_auto.
  iDestruct "Hkch" as (γkch) "#[Hkch #Hkrecv]".
  rewrite bool_decide_decide. destruct decide.
  {
    (* NOTE: if `clientv3.lessor.KeepAlive` returns `nil` for its error, it is guaranteed to
       return a non-nil chan, so this case is impossible. *)
    iDestruct (is_chan_not_null with "Hkch") as %hbad.
    done.
  }
  wp_auto.
  wp_apply chan.wp_make1 as "* (Hdonec_is & % & Hdonec)".
  wp_auto.
  rename s into ctx_desc.
  wp_alloc s as "Hs".
  wp_auto.
  iPersist "cancel donec keepAlive".
  iMod (alloc_closeable_chan True with "[$] [$]") as "Hdonec_open".
  iDestruct (own_closeable_chan_Unknown with "[$]") as "#?".
  rewrite -wp_fupd.
  wp_apply (wp_fork with "[Hdonec_open Hcancel]").
  {
    wp_auto. wp_apply wp_with_defer as "%defer defer".
    simpl subst.
    wp_auto.
    wp_for.
    wp_apply chan.wp_receive.
    { iFrame "#". }
    iIntros "_". iApply "Hkrecv". iIntros "*". wp_auto.
    wp_if_destruct.
    { wp_for_post. iFrame. }
    wp_for_post.
    wp_apply (wp_closeable_chan_close with "[$Hdonec_open]") as "_".
    { iFrame "#". done. }
    wp_auto. wp_apply "Hcancel". wp_auto.
    done.
  }
  iClear "Hctx". iStructNamedPrefix "Hs" "H". simpl.
  iPersist "Hclient Hid Hdonec".
  wp_auto. iModIntro.
  iApply "HΦ".
  rewrite decide_True //.
  iFrame "#".
Qed.
*)
Admitted.

Lemma wp_Session__Lease s γ lease :
  {{{ is_pkg_init concurrency ∗ is_Session s γ lease }}}
    s @! (go.PointerType concurrency.Session) @! "Lease" #()
  {{{ RET #lease; True }}}.
Proof.
  wp_start. iNamed "Hpre". wp_auto. wp_end.
Qed.

Lemma wp_Session__Done s γ lease :
  {{{ is_pkg_init concurrency ∗ is_Session s γ lease }}}
    s @! (go.PointerType concurrency.Session) @! "Done" #()
  {{{ ch γch, RET #ch; own_closeable_chan ch γch True closeable.Unknown }}}.
Proof.
  wp_start. iNamed "Hpre". wp_auto. wp_end.
Qed.

End proof.
