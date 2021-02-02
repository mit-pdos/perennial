From iris.proofmode Require Import coq_tactics reduction.
From Perennial.goose_lang.lib Require Import struct.struct.
From Perennial.goose_lang Require Import lifting proofmode.
From Perennial.goose_lang Require Import wpc_proofmode.
Set Default Proof Using "Type".

Tactic Notation "wpc_loadField" :=
  lazymatch goal with
  | |- envs_entails _ (wpc _ _ _ _ _ _) =>
    wpc_bind (struct.loadF _ _ (Val _));
    lazymatch goal with
    | |- envs_entails ?env (wpc _ _ _
                                (App (Val (struct.loadF ?d ?fname))
                                     (Val (LitV (LitLoc ?l)))) _ _) =>
      match env with
      | context[Esnoc _ ?i (l ↦[d :: fname] _)%I] =>
        wpc_frame_go i base.Right [i]; [idtac]
      | _ => wpc_frame_go "" base.Right (@nil ident); [idtac]
      | _ => fail 1 "wpc_loadField: could not frame automatically"
      end;
      wp_loadField;
      iNamed 1
    | _ => fail 1 "wpc_loadField: could not bind a struct.loadF"
    end
  | _ => fail 1 "wpc_loadField: not a wpc"
  end.

Tactic Notation "wpc_storeField" :=
  wpc_bind (struct.storeF _ _ _ _);
  wpc_frame;
  wp_storeField;
  iNamed 1.


Tactic Notation "wpc_wpapply" open_constr(lem) :=
iPoseProofCore lem as false (fun H =>
  lazymatch goal with
  | |- envs_entails _ (wpc ?s ?k ?E1 ?e ?Q ?Qc) =>
    reshape_expr e ltac:(fun K e' =>
      wpc_bind_core K; (wpc_frame; iApplyHyp H; try iNext; try wp_expr_simpl; solve_bi_true))
  | _ => fail "wpc_wpapply: not a wpc"
  end
    ).
