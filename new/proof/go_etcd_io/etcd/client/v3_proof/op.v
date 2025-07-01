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

Local Ltac setter etaT proj :=
  lazymatch etaT with
  | context[proj] => idtac
  | _ => fail 1 proj "is not a field"
  end;
  let set :=
      (match eval pattern proj in etaT with
       | ?setter _ => constr:(fun f => setter (fun r => f (proj r)))
       end) in
  exact set.
Local Ltac get_setter T proj :=
  match constr:(mkT T _) with
  | mkT _ ?updateable =>
    let updateable := (eval hnf in updateable) in
    match updateable with
    | {| mkT := ?mk |} =>
      setter mk proj
    end
  end.
Local Ltac SetterWfInstance_t :=
  match goal with
  | |- @SetterWf ?T _ ?A =>
    unshelve notypeclasses refine (Build_SetterWf _ _ _);
    [ get_setter T A |
      let r := fresh in
      intros ? r; destruct r; reflexivity |
      let f := fresh in
      let r := fresh in
      intros f r; destruct r; cbv [RecordSet.set]; cbn; congruence ]
  end.

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
  wp_start.
  wp_alloc_auto. progress wp_pures.
  wp_alloc_auto. progress wp_pures.
  wp_alloc_auto. progress wp_pures.
  wp_alloc_auto. progress wp_pures.
  wp_load. wp_apply wp_StringToBytes.
  iIntros "%key_sl key_sl". progress wp_pures.
  wp_load. wp_apply wp_StringToBytes.
  iIntros "%val_sl val_sl". progress wp_pures.
  rewrite -!default_val_eq_zero_val. progress wp_pures.
  wp_store. progress wp_pures. wp_load. progress wp_pures.
  wp_apply wp_Op__applyOpts. progress wp_pures.
  wp_bind.

  Time eapply (tac_wp_load_ty []);
    [ eapply points_to_access_struct_field_ref; tc_solve|
      iAssumptionCore |
      ltac2:(ectx_simpl ())]; simpl.
  Unshelve.
  2:{
    unshelve notypeclasses refine (Build_SetterWf _ _ _).
    { get_setter clientv3.Op.t clientv3.Op.end'.  }
    { let r := fresh in
      intros ? r; destruct r; reflexivity. }
    {
      let f := fresh in
      let r := fresh in
      intros f r; destruct r.
      simpl. intros ?.
      cbv [RecordSet.set].
      cbn. Time congruence.
      (* Takes 72.858s *)
Admitted.
(*
    }


    SetterWfInstance_t.
    SetterWf
    tc_solve.
    (* FIXME: this is what's *really* slow *)
  }
  Undo 1.
  Set Typeclasses Debug.
  Time eapply (tac_wp_load_ty []);
    [ ltac2:(tc_solve_many ()) |
      iAssumptionCore |
      ltac2:(ectx_simpl ())]; simpl.
  Unset Typeclasses Debug.
  wp_auto.
  rewrite !bool_decide_decide.
  rewrite !(decide_True (P:=slice.nil = slice.nil)) //=.
  wp_pures.
  Ltac fast_wp_load :=
    wp_bind;
    eapply (tac_wp_load_ty []);
    [ eapply points_to_access_struct_field_ref; tc_solve|
      iAssumptionCore |
      ltac2:(ectx_simpl ())]; simpl.

  wp_bind.
  eapply (tac_wp_load_ty []).

    { unshelve eapply points_to_access_struct_field_ref; try tc_solve.
      Search SetterWf.
    }
    { iAssumptionCore. }
    ltac2:(ectx_simpl ()); simpl.
  Unshelve.

  fast_wp_load. wp_pures).
  wp_load. wp_pures.
  iApply "HΦ".
  destruct admit_ax.
Time Qed.
(* 6.51 *) *)

(* FIXME: very slow proof, though [Qed] isn't too bad *)

End wps.
