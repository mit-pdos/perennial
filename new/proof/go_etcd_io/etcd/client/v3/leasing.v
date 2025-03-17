Require Import New.code.go_etcd_io.etcd.client.v3.leasing.
Require Import New.generatedproof.go_etcd_io.etcd.client.v3.leasing.
Require Import New.generatedproof.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.
Require Import New.proof.proof_prelude.
From New.proof Require Import context sync.

Require Import New.proof.go_etcd_io.etcd.client.v3.concurrency.
Require Import New.proof.go_etcd_io.etcd.client.v3.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.

(* FIXME: come up with a plan for global addrs of imported packages. *)
Context `{!concurrency.GlobalAddrs}.
Context `{!rpctypes.GlobalAddrs}.
Context `{!leasing.GlobalAddrs}.
Context `{!goGlobalsGS Σ}.

(* FIXME: move these *)
Program Instance : IsPkgInit bytes :=
  ltac2:(build_pkg_init ()).
Final Obligation. Proof. apply _. Qed.

Program Instance : IsPkgInit status.status :=
  ltac2:(build_pkg_init ()).
Final Obligation. Proof. apply _. Qed.

Program Instance : IsPkgInit codes :=
  ltac2:(build_pkg_init ()).
Final Obligation. Proof. apply _. Qed.

Program Instance : IsPkgInit rpctypes :=
  ltac2:(build_pkg_init ()).
Final Obligation. Proof. apply _. Qed.

Program Instance : IsPkgInit errors :=
  ltac2:(build_pkg_init ()).
Final Obligation. Proof. apply _. Qed.

Program Instance : IsPkgInit time :=
  ltac2:(build_pkg_init ()).
Final Obligation. Proof. apply _. Qed.

Program Instance : IsPkgInit strings :=
  ltac2:(build_pkg_init ()).
Final Obligation. Proof. apply _. Qed.

#[global]
Program Instance : IsPkgInit leasing :=
  ltac2:(build_pkg_init ()).
Final Obligation. Proof. apply _. Qed.

Lemma wp_NewKV cl γetcd (pfx : go_string) opts_sl :
  {{{
      is_pkg_init leasing ∗
      "#Hcl" ∷ is_Client cl γetcd ∗
      "Hopts_sl"  ∷ opts_sl ↦* ([] : list concurrency.SessionOption.t)
  }}}
    func_call #leasing #"NewKV" #cl #pfx #opts_sl
  {{{ RET #(); True }}}.
Proof.
  wp_start. iNamed "Hpre".
  wp_auto.
  wp_apply (wp_Client__Ctx with "[$]") as "% _".
  iDestruct (is_Client_to_pub with "[$]") as "#Hclient_pub".
  iNamed "Hclient_pub".
  wp_apply (wp_WithCancel with "[$]").
  iIntros "* #(Hctx' & Hcancel_spec & Hctx_done)".
  wp_auto.
  wp_apply wp_map_make as "%revokes Hrevokes".
  { done. }
  wp_apply wp_chan_make as "* ?".
  wp_alloc lkv as "Hlkv".
  wp_auto.
  iDestruct (struct_fields_split with "Hlkv") as "Hl".
  iEval (simpl) in "Hl".
  iRename "Hcl" into "#Hcl_in".
  iNamed "Hl".
  wp_apply wp_WaitGroup__Add.
  (* FIXME: go from zero value for [WaitGroup] to `is_WaitGroup`. *)
Admitted.

End proof.
