Require Import New.code.go_etcd_io.etcd.client.v3.concurrency.
Require Import New.generatedproof.go_etcd_io.etcd.client.v3.concurrency.
Require Import New.proof.proof_prelude.
Require Import New.proof.go_etcd_io.etcd.client.v3.
From New.proof Require Import context sync.

Section proof.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.

Context `{!concurrency.GlobalAddrs}.
Context `{!goGlobalsGS Σ}.

(* FIXME: move these *)
Program Instance : IsPkgInit math :=
  ltac2:(build_pkg_init ()).
Final Obligation. Proof. apply _. Qed.

Program Instance : IsPkgInit zapcore :=
  ltac2:(build_pkg_init ()).
Final Obligation. Proof. apply _. Qed.

Program Instance : IsPkgInit zap :=
  ltac2:(build_pkg_init ()).
Final Obligation. Proof. apply _. Qed.

Program Instance : IsPkgInit time :=
  ltac2:(build_pkg_init ()).
Final Obligation. Proof. apply _. Qed.

Program Instance : IsPkgInit strings :=
  ltac2:(build_pkg_init ()).
Final Obligation. Proof. apply _. Qed.

Program Instance : IsPkgInit fmt :=
  ltac2:(build_pkg_init ()).
Final Obligation. Proof. apply _. Qed.

Program Instance : IsPkgInit errors :=
  ltac2:(build_pkg_init ()).
Final Obligation. Proof. apply _. Qed.

#[global]
Program Instance : IsPkgInit concurrency :=
  ltac2:(build_pkg_init ()).
Final Obligation. Proof. apply _. Qed.

Definition is_Session (s : loc) : iProp Σ :=
  True.

Lemma wp_NewSession (client : loc) γetcd :
  {{{
        is_pkg_init concurrency ∗
        "#His_client" ∷ is_Client client γetcd
  }}}
    func_call #concurrency #"NewSession" #client #slice.nil
  {{{ s err, RET (#s, #err);
      if decide (err = interface.nil) then
        True
      else
        is_Session s
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
  wp_auto.
  rewrite bool_decide_decide. destruct decide.
  {
    wp_auto. wp_apply "Hcancel". iApply "HΦ".
    rewrite decide_False //.
    (* FIXME: in this case, the code can return nil error and also a nil
       `*Session`; can this actually happen? There are cases higher level in
       etcd assuming that (err = nil → session ≠ nil).
       So is the `keepAlive == nil` Check redundant? *)
    admit.
  }
  wp_auto.
  ltac2:(wp_bind_apply ()).
  (* FIXME: goose should translate the capacity argument. *)
  (* iApply (wp_chan_make (t:=structT []) (V:=())). *)

Admitted.

End proof.
