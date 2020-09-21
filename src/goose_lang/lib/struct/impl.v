From Perennial.goose_lang Require Import notation.
From Perennial.goose_lang Require Import typing.
From Perennial.goose_lang.lib Require Import typed_mem.impl.

(** * Struct library

    Access field offsets within pairs by name rather than using Fst and Snd. *)

Set Default Proof Using "Type".
Set Implicit Arguments.

Section goose_lang.
Context `{ffi_sem: ext_semantics}.
Context {ext_ty: ext_types ext}.

Definition descriptor := list (string*ty).
Definition mkStruct (fs: list (string*ty)): descriptor := fs.

Class descriptor_wf (d:descriptor) :=
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
  | (f,_)::fs => match lookup_f f with
           | Some e => match build_struct_val fs field_vals with
                      | Some e' => Some (e, e')%E
                      | None => None
                      end
           | None => None
           end
  end.

Definition buildStruct d (fvs: list (string*expr)) : expr :=
  match build_struct_val d fvs with
  | Some v => v
  | None => LitV LitUnit
  end.

Fixpoint build_struct_f d (field_vals: list (string*expr)): option val :=
  let lookup_f := assocl_lookup field_vals in
  match d with
  | [] => Some (#())
  | (f,_)::fs => match lookup_f f with
           | Some (Val e) => match build_struct_f fs field_vals with
                      | Some e' => Some (e, e')%V
                      | None => None
                      end
           | _ => None
           end
  end.

Definition buildStruct_f d (fvs: list (string*expr)) : val :=
  match build_struct_f d fvs with
  | Some v => v
  | None => LitV LitUnit
  end.

Fixpoint structTy d : ty :=
  match d with
  | [] => unitT
  | (_,t)::fs => prodT t (structTy fs)
  end.

Definition structRefTy (d:descriptor) : ty :=
  structRefT (flatten_ty (structTy d)).

Definition allocStruct (d:descriptor) : val :=
  λ: "v", ref_to (structTy d) (Var "v").

Definition allocStructLit (d:descriptor) (fvs: list (string*expr)) : expr :=
  match build_struct_val d fvs with
  | Some v => allocStruct d v
  | None => LitV LitUnit
  end.

Definition loadStruct (d:descriptor) : val := load_ty (structTy d).

Fixpoint field_offset d f0 : option (Z * ty) :=
  match d with
  | [] => None
  | (f,t)::fs => if f =? f0 then Some (0, t)
               else match field_offset fs f0 with
                    | Some (off, t') => Some (ty_size t + off, t')
                    | None => None
                    end
  end.

Definition fieldType (d:descriptor) (f:string): ty :=
  match field_offset d f with
  | Some (_, t) => t
  | None => unitT
  end.

(** structFieldRef gives a function that takes a location and constant pointer
arithmetic on it (which is pre-computed based on the field and descriptor). *)
Definition structFieldRef d f0: val :=
  match field_offset d f0 with
  | Some (off, t) => λ: "p", BinOp (OffsetOp off) (Var "p") #1
  | None => λ: <>, #()
  end.

Definition loadField (d:descriptor) (f:string) : val :=
  match field_offset d f with
  | Some (off, t) => λ: "p", load_ty t (BinOp (OffsetOp off) (Var "p") #1)
  | None => λ: <>, #()
  end.

Definition storeStruct (d: descriptor) : val :=
  λ: "p" "v", store_ty (structTy d) (Var "p", Var "v").

Definition storeField d f : val :=
  match field_offset d f with
  | Some (off, t) => λ: "p" "x", (BinOp (OffsetOp off) (Var "p") #1) <-[t] (Var "x")
  | None => λ: <> <>, #()
  end.

Local Open Scope heap_types.

Theorem load_struct_ref_hasTy Γ l t ts :
  Γ ⊢ l : structRefT (t::ts) ->
  Γ ⊢ !l : t.
Proof.
  apply load_hasTy.
Qed.

End goose_lang.

Hint Extern 3 (descriptor_wf ?d) => exact (proj_descriptor_wf d) : typeclass_instances.

Module struct.
  Notation decl := mkStruct.
  Notation wf := descriptor_wf.

  Notation t := structTy.
  Notation ptrT := structRefTy.

  Notation mk := buildStruct.
  Notation mk_f := buildStruct_f.
  Notation new := allocStructLit.
  Notation alloc := allocStruct.
  Notation get := getField.
  Notation fieldRef := structFieldRef.
  Notation load := loadStruct.
  Notation loadF := loadField.
  Notation store := storeStruct.
  Notation storeF := storeField.
End struct.

Declare Scope struct_scope.
Notation "f :: t" := (@pair string ty f%string t%ht) : struct_scope.
Notation "f ::= v" := (@pair string expr f%string v%E) (at level 60) : expr_scope.
Delimit Scope struct_scope with struct.
Arguments mkStruct {ext ext_ty} _%struct_scope.

(* TODO: we'll again need to unfold these to prove theorems about them, but
for typechecking they should be opaque *)
Global Opaque allocStruct structFieldRef loadStruct loadField storeStruct storeField.
