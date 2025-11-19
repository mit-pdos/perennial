(*
   This file is part of Actris (https://gitlab.mpi-sws.org/iris/actris).

   Copyright (c) Actris developers and contributors.
   Distributed under the terms of the BSD 3-Clause License; see
   https://gitlab.mpi-sws.org/iris/actris/-/blob/master/LICENSE
   for the full license text.
*)
From iris.algebra Require Import cofe_solver.

(** Version of the cofe_solver for a parametrized functor. Generalize and move
to Iris. *)
Record solution_2 (F : ofe → oFunctor) := Solution2 {
  solution_2_car : ∀ An `{!Cofe An} A `{!Cofe A}, ofe;
  solution_2_cofe `{!Cofe An, !Cofe A} : Cofe (solution_2_car An A);
  solution_2_iso `{!Cofe An, !Cofe A} :>
    ofe_iso (oFunctor_apply (F A) (solution_2_car A An)) (solution_2_car An A);
}.
Arguments solution_2_car {F}.
Global Existing Instance solution_2_cofe.

Section cofe_solver_2.
  Context (F : ofe → oFunctor).
  Context `{Fcontr : !∀ T, oFunctorContractive (F T)}.
  Context `{Fcofe : !∀ `{!Cofe T, !Cofe Bn, !Cofe B}, Cofe (oFunctor_car (F T) Bn B)}.
  Context `{Finh : !∀ `{!Cofe T, !Cofe Bn, !Cofe B}, Inhabited (oFunctor_car (F T) Bn B)}.
  Notation map := (oFunctor_map (F _)).

  Definition F_2 (An : ofe) `{!Cofe An} (A : ofe) `{!Cofe A} : oFunctor :=
    oFunctor_oFunctor_compose (F A) (F An).

  Definition T_result `{!Cofe An, !Cofe A} : solution (F_2 An A) := solver.result _.
  Definition T (An : ofe) `{!Cofe An} (A : ofe) `{!Cofe A} : ofe :=
    T_result (An:=An) (A:=A).
  Instance T_cofe `{!Cofe An, !Cofe A} : Cofe (T An A) := _.
  Instance T_inhabited `{!Cofe An, !Cofe A} : Inhabited (T An A) :=
    populate (ofe_iso_1 T_result inhabitant).

  Definition T_iso_fun_aux `{!Cofe An, !Cofe A}
      (rec : prodO (oFunctor_apply (F An) (T An A) -n> T A An)
                   (T A An -n> oFunctor_apply (F An) (T An A))) :
      prodO (oFunctor_apply (F A) (T A An) -n> T An A)
            (T An A -n> oFunctor_apply (F A) (T A An)) :=
    (ofe_iso_1 T_result ◎ map (rec.1,rec.2), map (rec.2,rec.1) ◎ ofe_iso_2 T_result).
  Instance T_iso_aux_fun_contractive `{!Cofe An, !Cofe A} :
    Contractive (T_iso_fun_aux (An:=An) (A:=A)).
  Proof. solve_contractive. Qed.

  Definition T_iso_fun_aux_2 `{!Cofe An, !Cofe A}
      (rec : prodO (oFunctor_apply (F A) (T A An) -n> T An A)
                   (T An A -n> oFunctor_apply (F A) (T A An))) :
      prodO (oFunctor_apply (F A) (T A An) -n> T An A)
            (T An A -n> oFunctor_apply (F A) (T A An)) :=
    T_iso_fun_aux (T_iso_fun_aux rec).
  Instance T_iso_fun_aux_2_contractive `{!Cofe An, !Cofe A} :
    Contractive (T_iso_fun_aux_2 (An:=An) (A:=A)).
  Proof.
    intros n rec1 rec2 Hrec. rewrite /T_iso_fun_aux_2.
    f_equiv. by apply T_iso_aux_fun_contractive.
  Qed.

  Definition T_iso_fun `{!Cofe An, !Cofe A} :
      prodO (oFunctor_apply (F A) (T A An) -n> T An A)
            (T An A -n> oFunctor_apply (F A) (T A An)) :=
    fixpoint T_iso_fun_aux_2.
  Definition T_iso_fun_unfold_1 `{!Cofe An, !Cofe A} y :
    T_iso_fun (An:=An) (A:=A).1 y ≡ (T_iso_fun_aux (T_iso_fun_aux T_iso_fun)).1 y.
  Proof. apply (fixpoint_unfold T_iso_fun_aux_2). Qed.
  Definition T_iso_fun_unfold_2 `{!Cofe An, !Cofe A} y :
    T_iso_fun (An:=An) (A:=A).2 y ≡ (T_iso_fun_aux (T_iso_fun_aux T_iso_fun)).2 y.
  Proof. apply (fixpoint_unfold T_iso_fun_aux_2). Qed.

  Lemma result_2 : solution_2 F.
  Proof using Fcontr Fcofe Finh.
    apply (Solution2 F T _)=> An Hcn A Hc.
    apply (OfeIso (T_iso_fun.1) (T_iso_fun.2)).
    - intros y. apply equiv_dist=> n. revert An Hcn A Hc y.
      induction (lt_wf n) as [n _ IH]; intros An ? A ? y.
      rewrite T_iso_fun_unfold_1 T_iso_fun_unfold_2 /=.
      rewrite -{2}(ofe_iso_12 T_result y). f_equiv.
      rewrite -(oFunctor_map_id (F _) (ofe_iso_2 T_result y))
              -!oFunctor_map_compose.
      f_equiv; apply Fcontr; dist_later_intro as n' Hn'; split=> x /=;
        rewrite ofe_iso_21 -{2}(oFunctor_map_id (F _) x)
          -!oFunctor_map_compose; do 2 f_equiv; split=> z /=; auto.
    - intros y. apply equiv_dist=> n. revert An Hcn A Hc y.
      induction (lt_wf n) as [n _ IH]; intros An ? A ? y.
      rewrite T_iso_fun_unfold_1 T_iso_fun_unfold_2 /= ofe_iso_21.
      rewrite -(oFunctor_map_id (F _) y) -!oFunctor_map_compose.
      f_equiv; apply Fcontr; dist_later_intro as n' Hn'; split=> x /=;
        rewrite -{2}(ofe_iso_12 T_result x); f_equiv;
        rewrite -{2}(oFunctor_map_id (F _) (ofe_iso_2 T_result x))
                -!oFunctor_map_compose;
        do 2 f_equiv; split=> z /=; auto.
  Qed.
End cofe_solver_2.
