From stdpp Require Import countable finite.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

(* FIXME: https://gitlab.mpi-sws.org/iris/stdpp/-/merge_requests/424 *)
Global Remove Hints finite_countable : typeclass_instances.

Module ltac2_tactics.
Inductive Simple :=
  one | two | three.

Inductive Nested :=
  first | second (t : Simple) | third (v : Simple) (x : nat).

Inductive Recursive :=
  base_cons (t : Nested) | recur_cons (r : Recursive).

Record R :=
  {
    Field1 : Z;
    Field2 : Z;
  }.

Import Constr.Unsafe.
Ltac2 countable_inj (t : constr) : constr :=
  let (ind, inst) := match kind t with
                          | Ind ind inst => (ind, inst)
                          | _ => Control.zero (Tactic_failure (Some (Message.of_string "expected input to be an inductive type")))
                          end in

  let ncons := (Ind.nconstructors (Ind.data ind)) in

  (* Wraps [args] into a term like [inl (inl ... (inr $args))] as needed for the
     ith constructor out of the ncons constructors for t. *)
  let make_sum_cons i args : constr :=
    let rec make_sum_cons_aux n i  (args : constr) : constr :=
      if (Int.gt i n) then
        Control.zero (Tactic_failure (Some (Message.of_string "countable_inj: internal error, expected i <= n")))
      else ();
      if (Int.equal i n) then
        if (Int.gt i 0) then make (App open_constr:(inr) (Array.make 1 args))
        else args
      else make (App open_constr:(inl) (Array.make 1 (make_sum_cons_aux (Int.sub n 1) i args)))
    in
    make_sum_cons_aux (Int.sub ncons 1) i args
  in

  (* Returns a list of the types for the ith constructor's arguments. *)
  let constructor_arg_types i : constr list :=
    let cons_name := make (Constructor (Ind.get_constructor (Ind.data ind) i) inst) in
    let rec loop c :=
      (match (kind c) with
       | Prod b c => (Constr.Binder.type b) :: loop c
       | _ => []
       end) in
    loop (Constr.type cons_name)
  in

  let mk_pair a b : constr := make (App open_constr:(pair) (Array.of_list [a; b])) in

  let mk_ident (s : string) (i : int)  : ident option :=
    Ident.of_string (Message.to_string (Message.concat (Message.of_string s) (Message.of_int i)))
  in

  let cases :=
    Array.init ncons
      (fun i =>
         let arg_types := constructor_arg_types i in
         let nargs := List.length arg_types in
         let case_output :=
           make_sum_cons i
             (List.fold_lefti (fun j args _ => mk_pair args (make (Rel (Int.sub nargs j))))
                constr:(tt) arg_types) in
         let case_fun :=
           List.fold_lefti (fun j e t => make (Lambda (Constr.Binder.make (mk_ident "x" (Int.sub nargs j)) t) e)) case_output arg_types
         in
         case_fun
      )
  in
  make
    (Lambda (Constr.Binder.make (Ident.of_string "x") t)
       (make (Case
                (case ind)
                (make (Lambda (Constr.Binder.make None t) open_constr:(_)), Constr.Binder.Relevant)
                NoInvert
                (make (Rel 1))
                cases
       ))
    )
.

Definition R_inj := ltac2:(Control.refine (fun () => countable_inj constr:(R))).
Definition Simple_inj := ltac2:(Control.refine (fun () => countable_inj constr:(Simple))).
Definition Nested_inj := ltac2:(Control.refine (fun () => countable_inj constr:(Nested))).
Definition Recursive_inj := ltac2:(Control.refine (fun () => countable_inj constr:(Recursive))).

End ltac2_tactics.

Local Ltac count t_rec :=
  let rec go num f :=
      (let t := type of f in
       let t := eval cbv beta in t in
           lazymatch t with
           | nat -> _ => go constr:(S num) constr:(f num)
           | _ => f
           end) in
  go constr:(0%nat) constr:(t_rec (fun _ => nat)).

Local Ltac match_n num :=
  lazymatch num with
  | 0%nat => uconstr:(fun (n:nat) => _)
  | _ => let num' := (eval cbv in (Nat.pred num)) in
        let match_n' := match_n num' in
        uconstr:(fun (n:nat) => match n with
                       | O => _
                       | S n' => match_n' n'
                       end)
  end.

Ltac solve_countable rec num :=
  let inj := count rec in
  let dec := match_n num in
  unshelve (refine (inj_countable' inj dec _); intros []; reflexivity);
  constructor.


Module tests.
  Inductive Three :=
    one | two | three.

  Instance Three_eq_dec : EqDecision Three.
  Proof.
    solve_decision.
  Qed.

  Instance Three_countable : Countable Three.
  Proof.
    solve_countable Three_rec 3.
  Qed.

  Definition Three_countable' : Countable Three.
  Proof.
    solve_countable Three_rec 5.
  Qed.
End tests.
