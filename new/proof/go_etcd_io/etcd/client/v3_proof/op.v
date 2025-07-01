From New.proof.go_etcd_io.etcd.client.v3_proof Require Import base definitions.

#[local] Transparent is_pkg_init_clientv3.

(* abstraction of an etcd [Op] *)
Module Op.
Inductive t :=
| Get (req : RangeRequest.t)
| Put (req : PutRequest.t)
| DeleteRange (req : DeleteRangeRequest.t)
| Txn (req : TxnRequest.t)
.
End Op.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!goGlobalsGS Σ}.
Context `{!clientv3G Σ}.
Context `{!etcdserverpb.GlobalAddrs}.
Implicit Types (γ : clientv3_names).

Axiom is_Op : ∀ (op : clientv3.Op.t) (o : Op.t), iProp Σ.

#[global] Instance is_Op_persistent op o : Persistent (is_Op op o).
Admitted.

(* NOTE: for simplicity, this only supports empty opts list. *)
Lemma wp_OpGet key :
  {{{ is_pkg_init clientv3 }}}
    clientv3 @ "OpGet" #key #slice.nil
  {{{
      op, RET #op;
      is_Op op (Op.Get (RangeRequest.default <|RangeRequest.key := key|>))
  }}}.
Proof.
  wp_start. wp_auto.
Admitted.

Lemma wp_Op__applyOpts (op : loc) :
  {{{ is_pkg_init clientv3 }}}
    op@clientv3@"Op'ptr"@"applyOpts" #slice.nil
  {{{ RET #(); True }}}.
Proof.
  wp_start. wp_auto. wp_apply wp_slice_for_range.
  { iApply (own_slice_nil DfracDiscarded). }
  simpl. iIntros "_". wp_auto. iApply "HΦ". done.
  Unshelve.
  all: try tc_solve.
Qed.

Axiom admit_ax : false.

Lemma wp_OpPut key v :
  {{{ is_pkg_init clientv3 }}}
    clientv3@"OpPut" #key #v #slice.nil
  {{{ op, RET #op;
      (∀ op_ptr,
         op_ptr ↦ op ==∗
         is_Op op (Op.Put (PutRequest.default <| PutRequest.key := key |> <| PutRequest.value := v |>))
      )
  }}}.
Proof.
  wp_start. wp_auto.
  wp_apply wp_StringToBytes.
  iIntros "%key_sl key_sl".
  wp_auto.
  wp_apply wp_StringToBytes.
  iIntros "%val_sl val_sl".
  time wp_auto. wp_apply wp_Op__applyOpts. time wp_auto. (* 73 seconds *)
  rewrite !bool_decide_decide.
  rewrite !(decide_True (P:=slice.nil = slice.nil)) //=.
  time wp_auto. (* 70 seconds *)
  iApply "HΦ".
  destruct admit_ax.
Time Qed.
(* 6.51 *)

(* FIXME: very slow proof, though [Qed] isn't too bad *)

End wps.
