From Perennial.goose_lang Require Import notation.
From Perennial.new_goose_lang Require Export typing.
From Perennial.new_goose_lang.lib Require Import typed_mem.impl.

(** * Struct library

    Access field offsets within pairs by name rather than using Fst and Snd. *)

Set Default Proof Using "Type".
Set Implicit Arguments.

Section goose_lang.
Context `{ffi_sem: ffi_semantics}.

Definition descriptor := list (string * go_type).
Definition mkStruct (fs: list (string * go_type)): descriptor := fs.

Class descriptor_wf (d:descriptor) : Set :=
  { descriptor_NoDup: NoDup d.*1; }.

Definition option_descriptor_wf (d:descriptor) : option (descriptor_wf d).
  destruct (decide (NoDup d.*1)); [ apply Some | apply None ].
  constructor; auto.
Defined.

Definition proj_descriptor_wf (d:descriptor) :=
  match option_descriptor_wf d as mwf return match mwf with
                                             | Some _ => descriptor_wf d
                                             | None => True
                                             end  with
  | Some pf => pf
  | None => I
  end.

Implicit Types (d:descriptor).
Infix "=?" := (String.eqb).

Fixpoint getField d (f0: string) : val :=
  match d with
  | [] => λ: <>, #()
  | (f,_)::fs => if f =? f0
               then (λ: "v", Fst (Var "v"))%V
               else (λ: "v", getField fs f0 (Snd (Var "v")))%V
  end.

(* FIXME: what does _f mean? Want better name. *)
Fixpoint getField_f d f0: val -> val :=
  λ v, match d with
       | [] => #()
       | (f,_)::fs =>
         match v with
         | PairV v1 v2 => if f =? f0 then v1 else getField_f fs f0 v2
         | _ => #()
         end
       end.

Fixpoint setField_f d f0 fv: val -> val :=
  λ v, match d with
       | [] => v
       | (f,_)::fs =>
         match v with
         | PairV v1 v2 =>
           if f =? f0
           then PairV fv v2
           else PairV v1 (setField_f fs f0 fv v2)
         | _ => v
         end
       end.

Fixpoint assocl_lookup {A} (field_vals: list (string * A)) (f0: string) : option A :=
  match field_vals with
  | [] => None
  | (f, v)::fs => if f =? f0 then Some v else assocl_lookup fs f0
  end.

Fixpoint build_struct_val d (field_vals: list (string*expr)): option expr :=
  let lookup_f := assocl_lookup field_vals in
  match d with
  | [] => Some (Val #())
  | (f,ft)::fs =>
    let e := default (Val (zero_val ft)) (lookup_f f) in
    match build_struct_val fs field_vals with
    | Some e' => Some (e, e')%E
    | None => None
    end
  end.

Definition buildStruct d (fvs: list (string*expr)) : expr :=
  match build_struct_val d fvs with
  | Some v => v
  | None => LitV LitUnit
  end.

Fixpoint buildStruct_f d (field_vals: list (string*val)): val :=
  let lookup_f := assocl_lookup field_vals in
  match d with
  | [] => (#())
  | (f,ft)::fs =>
    let e := default (zero_val ft) (lookup_f f) in
    let e' := buildStruct_f fs field_vals in
    (e, e')%V
  end.

Fixpoint field_offset d f0 : (Z * go_type) :=
  match d with
  | [] => (-1, ptrT)
  | (f,t)::fs => if f =? f0 then (0, t)
               else match field_offset fs f0 with
                    | (off, t') => ((go_type_size t) + off, t')
                    end
  end.

Definition fieldType (d:descriptor) (f:string): go_type :=
  match field_offset d f with
  | (_, t) => t
  end.

(** structFieldRef gives a function that takes a location and constant pointer
arithmetic on it (which is pre-computed based on the field and descriptor). *)
Definition structFieldRef d f0: val :=
  λ: "p", BinOp (OffsetOp (field_offset d f0).1) (Var "p") #1
.

Definition structFieldRef_f d f0 l: loc :=
  l +ₗ (field_offset d f0).1
.

Definition structFieldTy_f d f0 : go_type :=
  (field_offset d f0).2
.

End goose_lang.

#[global]
Hint Extern 3 (descriptor_wf ?d) => exact (proj_descriptor_wf d) : typeclass_instances.

Module struct.
  Notation decl := mkStruct.
  Notation wf := descriptor_wf.

  Notation mk := buildStruct.
  Notation mk_f := buildStruct_f.
  Notation get := getField.
  Notation fieldRef := structFieldRef.
  Notation fieldRef_f := structFieldRef_f.

  Notation fieldTy := structFieldTy_f.
End struct.

Declare Scope struct_scope.
Notation "f :: t" := (@pair string go_type f%string t) : struct_scope.
Notation "f ::= v" := (@pair string val f%string v%V) (at level 60) : val_scope.
Notation "f ::= v" := (@pair string expr f%string v%E) (at level 60) : expr_scope.
Delimit Scope struct_scope with struct.
Arguments mkStruct _%struct_scope.

(* TODO: we'll again need to unfold these to prove theorems about them, but
for typechecking they should be opaque *)
Global Opaque structFieldRef.
