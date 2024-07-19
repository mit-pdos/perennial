From iris.proofmode Require Import coq_tactics reduction.
From Perennial.goose_lang Require Import proofmode.
From Perennial.Helpers Require Import NamedProps.

From Perennial.goose_lang Require Import struct.struct.

Set Default Proof Using "Type".

Ltac wp_start :=
  lazymatch goal with
  | |- envs_entails _ _ => fail "already in a proofmode goal"
  | _ => idtac
  end;
  iIntros (Φ) "Hpre HΦ";
  lazymatch goal with
  | |- context[Esnoc _ (INamed "HΦ") (▷ ?Q)%I] =>
    set (post:=Q)
  end;
  lazymatch iTypeOf "Hpre" with
  | Some (_, named _ _ ∗ _)%I => iNamed "Hpre"
  | Some (_, named _ _)%I => iNamed "Hpre"
  | _ => idtac
  end;
  wp_rec; wp_pures.

Ltac wp_auto :=
  repeat first [
      wp_load
    | wp_store
    | wp_loadField
    | wp_storeField
    | wp_pures
  ].

(* TODO: these tactics are in proofmode.v but don't actually parse; adding them
here and adding (at level 0) fixes this for some reason. *)
Tactic Notation (at level 0) "wp_apply" open_constr(lem) "as" constr(pat) :=
  wp_apply lem; last (iIntros pat); wp_auto.
Tactic Notation (at level 0) "wp_apply" open_constr(lem) "as" "(" simple_intropattern(x1) ")"
    constr(pat) :=
  wp_apply lem; last (iIntros ( x1 ) pat); wp_auto.
Tactic Notation (at level 0) "wp_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) ")" constr(pat) :=
  wp_apply lem; last (iIntros ( x1 x2 ) pat); wp_auto.
Tactic Notation (at level 0) "wp_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) ")" constr(pat) :=
  wp_apply lem; last (iIntros ( x1 x2 x3 ) pat); wp_auto.
