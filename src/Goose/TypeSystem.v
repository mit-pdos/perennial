From Classes Require Import EqualDec.

From Perennial Require Import Spec.Proc.
From Perennial Require Import Spec.InjectOp.
From Perennial Require Import GoLayer.

Import EqualDecNotation.

Inductive GoTy : Type :=
| uint64Ty
| byteTy
| voidTy
| structTy (desc:structDesc)
| pair (tyL tyR:GoTy)
with structDesc : Type :=
| emptyStruct
| fieldCons (name: string) (ty:GoTy) (s:structDesc)
.

(* TODO: I believe we need to make a mutual induction principle to support
   induction over types *)

Section GoModel.
  Context {model:GoModel}.

  Fixpoint rep (ty:GoTy) : Type :=
    match ty with
    | uint64Ty => uint64
    | byteTy => byte
    | voidTy => unit
    | structTy desc => structRep desc
    | pair tyL tyR => rep tyL * rep tyR
    end
  with structRep (desc:structDesc) : Type :=
         match desc with
         | emptyStruct => unit
         | fieldCons _ ty s => rep ty * structRep s
         end
  .

  Fixpoint getFieldRep (name0:string) (desc:structDesc) : Type :=
    match desc with
    | emptyStruct => unit
    | fieldCons name ty s =>
      if name == name0
      then rep ty
      else getFieldRep name0 s
    end.

  Fixpoint getField (name0:string) {desc:structDesc} (x:rep (structTy desc)) {struct desc} :
    getFieldRep name0 desc.
  Proof.
    destruct desc; simpl in *.
    - exact tt.
    - destruct (name == name0).
      + exact (fst x).
      + exact (getField name0 desc (snd x)).
  Defined.

End GoModel.

Module Example.
  Definition TwoInts :=
    (* TODO: it's annoying to have to write descriptors here; maybe we should
    make "uint64" and "byte" refer to their type codes within Goose code, so we
    always wrap types with "rep ty" *)
    structTy (fieldCons "x" uint64Ty
                        (fieldCons "y" uint64Ty
                                   emptyStruct)).

  Definition getting_x_from_twoInts {model:GoModel} (s:rep TwoInts) : rep uint64Ty :=
    (* such dependent types, wow *)
    getField "x" s.

End Example.

Module Arrow.
  Record ty :=
    mk { args: list GoTy;
         ret: GoTy; }.
End Arrow.

Fixpoint funcType {model:GoModel} (args: list GoTy) (retType: Type) : Type :=
  match args with
  | nil => retType
  | cons ty args => rep ty -> funcType args retType
  end.

Definition func {model:GoModel} (ty:Arrow.ty) : Type :=
  funcType ty.(Arrow.args) (proc GoLayer.Op (rep ty.(Arrow.ret))).

Module Example2.
  Import Coq.Lists.List.ListNotations.
  Local Open Scope list.
  Definition get_x_func {model:GoModel} : func (Arrow.mk [Example.TwoInts] uint64Ty) :=
    fun s => Ret (getField "x" s).
End Example2.
