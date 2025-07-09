From New.proof.go_etcd_io.etcd.client.v3_proof Require Import base definitions.

#[local] Transparent is_pkg_init_clientv3.

Ltac2 Set wp_apply_auto_default := Ltac2.Init.false.

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

Local Definition is_Op_RangeRequest (op : clientv3.Op.t) (req : RangeRequest.t) : iProp Σ :=
  "%Ht" ∷ ⌜ op.(clientv3.Op.t') = W64 1 ⌝ ∗
  "#key" ∷ op.(clientv3.Op.key') ↦*□ req.(RangeRequest.key) ∗
  "#end" ∷ op.(clientv3.Op.end') ↦*□ req.(RangeRequest.range_end) ∗
  "%Hlimit" ∷ ⌜ op.(clientv3.Op.limit') = req.(RangeRequest.limit) ⌝ ∗
  "%Hsort" ∷
    op.(clientv3.Op.sort') ↦□
         (clientv3.SortOption.mk
            (W64 (sint.Z req.(RangeRequest.sort_target))) (W64 (sint.Z req.(RangeRequest.sort_order)))) ∗
  "%Hserializable" ∷ ⌜ op.(clientv3.Op.serializable') = req.(RangeRequest.serializable) ⌝ ∗
  "%HkeysOnly" ∷ ⌜ op.(clientv3.Op.keysOnly') = req.(RangeRequest.keys_only) ⌝ ∗
  "%HcountOnly" ∷ ⌜ op.(clientv3.Op.countOnly') = req.(RangeRequest.count_only) ⌝ ∗
  "%HminModRev" ∷ ⌜ op.(clientv3.Op.minModRev') = req.(RangeRequest.min_mod_revision) ⌝ ∗
  "%HmaxModRev" ∷ ⌜ op.(clientv3.Op.maxModRev') = req.(RangeRequest.max_mod_revision) ⌝ ∗
  "%HminCreateRev" ∷ ⌜ op.(clientv3.Op.minCreateRev') = req.(RangeRequest.min_create_revision) ⌝ ∗
  "%HmaxCreateRev" ∷ ⌜ op.(clientv3.Op.maxCreateRev') = req.(RangeRequest.max_create_revision) ⌝.

Local Definition is_Op_PutRequest (op : clientv3.Op.t) (req : PutRequest.t) : iProp Σ :=
  "%Ht" ∷ ⌜ op.(clientv3.Op.t') = W64 2 ⌝ ∗
  "#key" ∷ op.(clientv3.Op.key') ↦*□ req.(PutRequest.key) ∗
  "#value" ∷ op.(clientv3.Op.val') ↦*□ req.(PutRequest.value) ∗
  "%Hlease" ∷ ⌜ op.(clientv3.Op.leaseID') = req.(PutRequest.lease) ⌝ ∗
  "%HprevKV" ∷ ⌜ op.(clientv3.Op.prevKV') = req.(PutRequest.prev_kv) ⌝ ∗
  "%Hignore_value" ∷ ⌜ op.(clientv3.Op.ignoreValue') = req.(PutRequest.ignore_value) ⌝ ∗
  "%Hignore_lease" ∷ ⌜ op.(clientv3.Op.ignoreLease') = req.(PutRequest.ignore_lease) ⌝.

Definition is_Op (op : clientv3.Op.t) (o : Op.t) : iProp Σ :=
  match o with
  | Op.Get req => is_Op_RangeRequest op req
  | Op.Put req => is_Op_PutRequest op req
  | _ => False
  end.
#[global] Opaque is_Op.
#[local] Transparent is_Op.

#[global] Instance is_Op_persistent op o : Persistent (is_Op op o).
Proof. destruct o; try apply _. Qed.

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

Lemma wp_OpPut key v :
  {{{ is_pkg_init clientv3 }}}
    clientv3@"OpPut" #key #v #slice.nil
  {{{ op, RET #op;
      is_Op op (Op.Put (PutRequest.default <| PutRequest.key := key |> <| PutRequest.value := v |>))
  }}}.
Proof.
  wp_start. wp_auto.
  wp_apply wp_StringToBytes. iIntros "%key_sl key_sl". wp_auto.
  wp_apply wp_StringToBytes. iIntros "%val_sl val_sl". wp_auto.
  wp_apply wp_Op__applyOpts. wp_auto.
  rewrite !bool_decide_decide.
  rewrite !(decide_True (P:=slice.nil = slice.nil)) //=.
  iPersist "val_sl key_sl".
  wp_auto.
  iApply "HΦ". iClear "ret".
  iFrame "∗#%". simpl.
  iPureIntro. done.
Qed.

Lemma wp_Op__KeyBytes op req :
  {{{ is_pkg_init clientv3 ∗ is_Op op (Op.Put req) }}}
    op@clientv3@"Op"@"KeyBytes" #()
  {{{ key_sl, RET #key_sl; key_sl ↦*□ req.(PutRequest.key) }}}.
Proof.
  wp_start. wp_auto. iApply "HΦ". iNamed "Hpre". iFrame "#".
Qed.

End wps.
