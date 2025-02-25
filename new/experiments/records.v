From stdpp Require Import strings.
From Ltac2 Require Import Ltac2.

Set Primitive Projections.
Module foo.
Record t :=
mk {
    field1 : nat;
    field2 : string;
  }.

End foo.

Import Constr.Unsafe.
Print Ltac2 Signatures.
Ltac2 get (x : constr) (field_name : string) :=
  let (ind, inst) :=
    match kind (Constr.type x) with
    | Ind ind inst => ind, inst
    | _ => Control.zero (Tactic_failure (Some (Message.of_string "could not get type of term")))
                       (* FIXME: better error *)
    end in
  let field_names :=
    let cons_name := make (Constructor (Ind.get_constructor (Ind.data ind) 0) inst) in
    let rec loop c :=
      (match (kind c) with
       | Prod b c => Option.map Ident.to_string (Constr.Binder.name b) :: loop c
       | _ => []
       end) in
    loop (Constr.type cons_name)
  in
  let i := List.fold_lefti (fun i v f => if Option.equal String.equal f (Some field_name) then Some i else v)
    None field_names in
  let i := match i with
           | None => Control.backtrack_tactic_failure "could not find field"
           | Some i => i
           end
  in
  let proj := Array.get (Option.get (Ind.get_projections (Ind.data ind))) i in
  make (Constant (Option.get (Proj.to_constant proj)) inst)
.

Section test.
Variable (x : foo.t).
Ltac2 Eval (get constr:(x) "field1").
Ltac2 Eval (get constr:(x) "field2").
End test.
