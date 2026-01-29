Require Import New.code.go_etcd_io.etcd.client.v3.concurrency.
Require Import New.generatedproof.go_etcd_io.etcd.client.v3.concurrency.
Require Import New.proof.proof_prelude.
Require Import New.proof.go_etcd_io.etcd.client.v3.
From New.proof Require Import context sync time math errors fmt.

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
#[global] Instance : IsPkgInit zapcore := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf zapcore := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit zap := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf zap := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit strings := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf strings := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit concurrency := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf concurrency := build_get_is_pkg_init_wf.

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
  wp_for "i".
  wp_if_destruct; [word|].
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
