From stdpp Require Import countable.

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
