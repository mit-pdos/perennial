From Perennial.goose_lang Require Import lang notation.

Class val_types :=
  { ext_tys : Type; }.

Section val_types.
  Context {val_tys : val_types}.
  Inductive go_type :=
  (* Boolean *)
  | boolT

  (* Numeric, except float and impl-specific sized objects *)
  | uint8T
  | uint16T
  | uint32T
  | uint64T
  | int8T
  | int16T
  | int32T
  | int64T

  | stringT
  (* | arrayT (len : nat) (elem : go_type) *)
  | sliceT (elem : go_type)
  | structT (decls : list (string * go_type)) (* What if this were a gmap? *)
  | ptrT (* Untyped pointer *)
  | funcT
  | interfaceT
  | mapT (key : go_type) (elem : go_type)
  | chanT (elem : go_type)
  .

  Definition byteT := uint8T.

  Context `{ffi_syntax}.
  Fixpoint go_type_type (t : go_type) : Type :=
    match t with
    | boolT => bool

    (* Numeric types, excluding float and impl-specific sized objects *)
    | uint8T => w8
    | uint16T => w8 (* FIXME: W16 *)
    | uint32T => w32
    | uint64T => w64
    | int8T => w8
    | int16T => w8 (* FIXME: W16 *)
    | int32T => w32
    | int64T => w64

    | stringT => string
    (* | arrayT len elem => array.t (list ) *)
    | sliceT elem => (loc * Z * Z)
    | structT decls => fold_right (λ '(f_name, f_t) typ, prod (go_type_type f_t) typ) unit decls
    | ptrT => loc
    | funcT => val
    | interfaceT => (loc * string * gmap string val)
    | mapT key elem => (loc * go_type_type elem)
    | chanT elem => loc
    end
  .

  (*
  Print fold_right.
  Lemma x (zv : { d & go_type_type $ structT d } ) ft f_name :
    (go_type_type (structT (projT1 zv)) * go_type_type ft)%type =
    go_type_type (structT ((f_name, ft) :: projT1 zv)).
  Proof.
    simpl.
    clear.

    unfold foldl at 2.
    simpl.
    reflexivity.
  Qed. *)

  Definition foldr_def := foldr.
  (* Program Definition fold_right := unseal (_:seal (@foldr)). Obligation 1. by eexists. Qed. *)
  Definition go_nil := null.
  #[program] Fixpoint zero_val (t : go_type) : (go_type_type t) :=
    match t with
    | boolT => false

    (* Numeric types, excluding float and impl-specific sized objects *)
    | uint8T => (W8 0)
    | uint16T => (W8 0)
    | uint32T => (W32 0)
    | uint64T => (W64 0)
    | int8T => (W8 0)
    | int16T => (W8 0)
    | int32T => (W32 0)
    | int64T => (W64 0)

    | stringT => ""
    (* | arrayT len elem => array.t (list ) *)
    | sliceT elem => (null, -1, -1) (* FIXME: nil *)
    | structT decls =>
        projT2 (@fold_right { d & go_type_type $ structT d } (string * go_type)
                  (λ '(f_name, ft) zv, existT ((f_name, ft) :: (projT1 zv)) (pair (zero_val ft) (projT2 zv)))
                  (existT nil tt : { d & go_type_type $ structT d }) decls)

        (* projT2 (foldl (λ zv '(f_name, ft), existT ((f_name, ft) :: (projT1 zv)) (pair (projT2 zv) (zero_val ft)))
                      (existT nil tt : { d & go_type_type $ structT d }) decls) *)
    | ptrT => null
    | funcT => #go_nil
    | interfaceT => (null, "", ∅)
    | mapT key elem => (go_nil, zero_val elem)
    | chanT elem => go_nil
    end
  .
  Obligation 1.
  intros.
  subst.
  induction decls as [|x decls]; [done|].
  {
    destruct x.
    simpl.
    f_equal.
    done.
  }
  Abort.

End val_types.
