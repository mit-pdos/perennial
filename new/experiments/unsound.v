From New.code Require Import github_com.mit_pdos.gokv.lockservice.
From New.proof Require Import grove_prelude.

(* Takes a WP goal as input, and gives the next proof goal as output *)
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
Import Ltac2.Message.

Ltac2 mutable dbg := print.
Ltac2 mutable dbg_constr c := print (of_constr c).

Ltac2 simpl_flags := {
    Std.rStrength := Std.Norm;
  Std.rBeta := true;
  Std.rMatch := true;
  Std.rFix := true;
  Std.rCofix := true;
  Std.rZeta := true;
  Std.rDelta := true ;
  Std.rConst := []
}.

Ltac2 rec expr_step e : constr :=
  lazy_match! e with
  | Rec ?f ?x ?e =>
      dbg (of_string "reached Rec");
      '(Val $ RecV $f $x $e)
  | App (Val (RecV ?f ?x ?e)) (Val ?v2) =>
      dbg (of_string "reached App (RecV ...) v");
      dbg_constr e;
      (* FIXME: try to keep identifier for function name *)
      let e' := constr:(subst' $x $v2 (subst' $f #() $e)) in
      Control.time (Some "simpl took: ") (fun () => Std.eval_simpl simpl_flags None e')
      (* XXX: simplifying [subst']; should try implementing this directly in
         Ltac2, as it takes up nearly all the time. *)
  | App (?e1) (Val ?v)  =>
      dbg (of_string "reached App e v");
      let e1 := expr_step '$e1 in
      '(App $e1 (Val $v))
  | App ?e1 ?e2 =>
      dbg (of_string "reached App e e");
      let e2new := expr_step '$e2 in
      dbg_constr e2new;
      '(App $e1 $e2new)
  end
.

Ltac2 rec expr_steps e : constr :=
  Control.plus
    (fun () => expr_steps (expr_step e))
    (fun ex => print (of_string "no more steps due to: "); print (of_exn ex); e)
.

Context `{!heapGS Σ}.
Lemma wp_LockClerk__Lock (ck : loc) key R :
  {{{
       True
  }}}
    LockClerk__Lock #ck #(str key)
  {{{
       RET #(); R
  }}}
.
Proof.
  iIntros (?) "? HΦ".
  wp_rec.
  (* time wp_pures. (* ~50-70ms *) *)
  Proof Mode "Ltac2".
  Ltac2 Set dbg := (fun _ => ()).
  Ltac2 Set dbg_constr := (fun _ => ()).
  Time match! goal with
  | [ |- envs_entails ?Δ (wp ?s ?et ?e ?Φ)] =>
      let e' := (expr_steps e) in
      enough (envs_entails $Δ (wp $s $et $e' $Φ)) by admit
  end.
  (* 5ms for simpl (which can likely be reduced), 6ms total. *)
  Proof Mode "Classic".
  wp_alloc ck_ptr as "?".
  wp_alloc k as "?".
  wp_pures.
Admitted.
