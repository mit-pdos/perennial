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

Ltac2 full_simpl (x : constr) : constr :=
  Std.eval_simpl simpl_flags None x.

Ltac2 subst_step x v e : constr :=
  lazy_match! x with
  | BAnon => e
  | BNamed ?x' =>
      let rec go_subst e : constr :=
        lazy_match! e with
        | @Val grove_op _ => e
        | Var ?x'' => if (Constr.equal x'' x') then '(Val $v) else e
        | Rec ?f ?x'' ?e' =>
            if Bool.or (Constr.equal x'' x) (Constr.equal f x) then e
            else let e' := go_subst e' in '(Rec $f $x'' $e')
        | App ?e1 ?e2 => let e1 := go_subst e1 in
                        let e2 := go_subst e2 in
                        '(App $e1 $e2)
        | UnOp ?op ?e =>
            let e := go_subst e in
            '(UnOp $op $e)
        | BinOp ?op ?e1 ?e2 =>
            let e1 := go_subst e1 in
            let e2 := go_subst e2 in
            '(BinOp $op $e1 $e2)
        | _ => constr:(subst' $x $v $e)
                       (* | _ => Control.throw (Tactic_failure None) *)
        end in
      go_subst e
  end
.

Ltac2 rec expr_step e : constr :=
  lazy_match! e with
  | Rec ?f ?x ?e =>
      dbg (of_string "reached Rec");
      '(Val $ RecV $f $x $e)
  | App (Val (RecV ?f ?x ?e)) (Val ?v2) =>
      dbg (of_string "reached App (RecV ...) v");
      dbg_constr e;
      (* FIXME: try to keep identifier for function name *)
      subst_step x v2 (subst_step f '(@LitV grove_op LitUnit) e)
      (* subst_step x v2 e (subst_step f '#() e) *)
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
    (fun ex => dbg (of_string "no more steps due to: "); print (of_exn ex); e)
.

(*
  let "c" := (f a)
  (App () (App f a))

  Could come up with the "head" expression and the
 *)

(*
  Given the expression and , come up with a new expression as well as
 *)

Ltac2 wp_pures_fast () :=
  match! goal with
  | [ |- envs_entails ?Δ (wp ?s ?et ?e ?Φ)] =>
      let e' := (expr_steps e) in
      enough (envs_entails $Δ (wp $s $et $e' $Φ)) by admit
  end.

Ltac2 Notation "wp_pures_fast" := wp_pures_fast ().

Section proof.
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
  (* Time (wp_rec; wp_pures). *) (* 80-100ms *)
  Proof Mode "Ltac2".
  Ltac2 Set dbg := (fun _ => ()).
  Ltac2 Set dbg_constr := (fun _ => ()).
  Time unfold LockClerk__Lock; wp_pures_fast. (* 2ms *)
  Proof Mode "Classic".
  wp_alloc ck_ptr as "?".
  wp_alloc k as "?".
  wp_pures.
Admitted.

End proof.
