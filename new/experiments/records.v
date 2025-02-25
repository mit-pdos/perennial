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

Import Printf.
Ltac2 record_field_resolve (x : constr) (field_name : string) :=
  let ty := (Constr.type x) in
  let (ind, inst) :=
    match kind ty with
    | Ind ind inst => ind, inst
    | _ => Control.zero
            (Tactic_failure (Some (fprintf "record_field_resolve: could not get type of: %t" x)))
    end in

  let projs :=
    match (Ind.get_projections (Ind.data ind)) with
    | Some projs => projs
    | _ => Control.zero
            (Tactic_failure (Some (fprintf "record_field_resolve: type is not a primitive record: %t" ty)))
    end in

  let field_names :=
    let cons_name := make (Constructor (Ind.get_constructor (Ind.data ind) 0) inst) in
    let rec loop c :=
      (match (kind c) with
       | Prod b c => Option.map Ident.to_string (Constr.Binder.name b) :: loop c
       | _ => []
       end) in
    loop (Constr.type cons_name) in

  let i := List.fold_lefti (fun i v f => if Option.equal String.equal f (Some field_name) then Some i else v)
    None field_names in

  let i :=
    match i with
    | Some i => i
    | _ => Control.zero
               (Tactic_failure (Some (fprintf "record_field_resolve: could not find field %s in type %t" field_name ty)))
    end in
  let proj_const :=
    match Proj.to_constant (Array.get projs i) with
    | Some proj => proj
    | _ => Control.zero (Tactic_failure (Some (fprintf "record_field_resolve: could not get projection %i of %t" i ty)))
    end in
  make (Constant proj_const inst).

Section test.
Variable (x : foo.t).
Ltac2 Eval (record_field_resolve constr:(x) "field1").
Ltac2 Eval (record_field_resolve constr:(x) "field2").
Fail Ltac2 Eval (record_field_resolve constr:(x) "field3").
Fail Ltac2 Eval (record_field_resolve constr:(O) "field1").
Fail Ltac2 Eval (record_field_resolve open_constr:(_) "field1").
End test.
