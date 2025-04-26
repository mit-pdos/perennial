Require Import New.code.go_etcd_io.etcd.client.v3.concurrency.
Require Import New.generatedproof.go_etcd_io.etcd.client.v3.concurrency.
Require Import New.proof.proof_prelude.
Require Import New.proof.go_etcd_io.etcd.client.v3.
From New.proof Require Import context sync.
From New.proof Require Export chan.

Class concurrencyG Σ :=
  {
    donecG :: closeable_chanG Σ ;
    context_inG :: contextG Σ
  }.

Section proof.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.

Context `{!concurrency.GlobalAddrs}.
Context `{!goGlobalsGS Σ}.
Context `{concurrencyG Σ}.

(* FIXME: move these *)
Program Instance : IsPkgInit math :=
  ltac2:(build_pkg_init ()).

Program Instance : IsPkgInit zapcore :=
  ltac2:(build_pkg_init ()).

Program Instance : IsPkgInit zap :=
  ltac2:(build_pkg_init ()).

Program Instance : IsPkgInit time :=
  ltac2:(build_pkg_init ()).

Program Instance : IsPkgInit strings :=
  ltac2:(build_pkg_init ()).

Program Instance : IsPkgInit fmt :=
  ltac2:(build_pkg_init ()).

Program Instance : IsPkgInit errors :=
  ltac2:(build_pkg_init ()).

#[global]
Program Instance : IsPkgInit concurrency :=
  ltac2:(build_pkg_init ()).

Definition is_Session (s : loc) γ (lease : clientv3.LeaseID.t) : iProp Σ :=
  ∃ cl donec,
  "#client" ∷ s ↦s[concurrency.Session :: "client"]□ cl ∗
  "#id" ∷ s ↦s[concurrency.Session :: "id"]□ lease ∗
  "#Hclient" ∷ is_Client cl γ ∗
  "#Hlease" ∷ is_etcd_lease γ lease ∗
  "#donec" ∷ s ↦s[concurrency.Session :: "donec"]□ donec ∗
  (* One can keep calling receive, and the only thing they might get back is a
     "closed" value. *)
  "#Hdonec" ∷ is_closeable_chan donec True.

#[global] Opaque is_Session.
#[local] Transparent is_Session.
#[global] Instance is_Session_pers s γ lease : Persistent (is_Session s γ lease) := _.

Lemma wp_NewSession (client : loc) γetcd :
  {{{
        is_pkg_init concurrency ∗
        "#His_client" ∷ is_Client client γetcd
  }}}
    concurrency @ "NewSession" #client #slice.nil
  {{{ s err, RET (#s, #err);
      if decide (err = interface.nil) then
        ∃ lease, is_Session s γetcd lease
      else
        True
  }}}.
Proof.
  wp_start. iNamed "Hpre".
  wp_auto.
  wp_apply (wp_Client__GetLogger with "[$]") as "% _".
  wp_apply (wp_Client__Ctx with "[$]") as "% _".
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
  wp_apply (wp_Client__Grant with "[$]") as "* [Hresp Hl]".
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
  wp_apply wp_WithCancel as "* (Hctx & Hcancel & Hchan)".

  wp_apply (wp_Client__KeepAlive with "[$]") as "* #Hkch".
  rewrite bool_decide_decide. destruct decide.
  2:{ (* error *)
    wp_auto. wp_apply "Hcancel". iApply "HΦ".
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
  iDestruct (own_chan_is_chan with "Hdonec") as "#Hdonec_is".
  wp_alloc s as "Hs".
  wp_auto.
  iPersist "cancel donec keepAlive".
  iMod (alloc_closeable_chan True with "Hdonec_is Hdonec") as (γch) "[#Hdonec_closeable Hdonec_tok]"; [done..|].
  rewrite -wp_fupd.
  wp_apply (wp_fork with "[Hdonec_tok Hcancel]").
  {
    wp_apply wp_with_defer as "%defer defer".
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
      wp_apply (wp_closeable_chan_close with "[$Hdonec_tok]").
      { iFrame "#". done. }
      wp_apply "Hcancel".
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
  iModIntro.
  iApply "HΦ".
  rewrite decide_True //.
  iFrame "#".
Qed.

Lemma wp_Session__Lease s γ lease :
  {{{ is_pkg_init concurrency ∗ is_Session s γ lease }}}
    s @ concurrency @ "Session'ptr" @ "Lease" #()
  {{{ RET #lease; True }}}.
Proof.
  wp_start. iNamed "Hpre". wp_auto. by iApply "HΦ".
Qed.

Lemma wp_Session__Done s γ lease :
  {{{ is_pkg_init concurrency ∗ is_Session s γ lease }}}
    s @ concurrency @ "Session'ptr" @ "Done" #()
  {{{ ch, RET #ch; is_closeable_chan ch True }}}.
Proof.
  wp_start. iNamed "Hpre". wp_auto. by iApply "HΦ".
Qed.

End proof.
