From Perennial.goose_lang Require Import lang notation.

Section val_types.
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
  | ptrT (* Untyped pointer; convenient to support recursion in structs *)
  | funcT
  | interfaceT
  | mapT (key elem : go_type)
  | chanT (elem : go_type).

  Definition byteT := uint8T.

  Context `{ffi_syntax}.
  Definition nil : val := #null.
  Definition slice_nil : val := (nil, nil, nil).
  Definition interface_nil : val := (nil, nil, nil).
  Fixpoint zero_val (t : go_type) : val :=
    match t with
    | boolT => #false

    (* Numeric, except float and impl-specific sized objects *)
    | uint8T => #(W8 0)
    | uint16T => nil
    | uint32T => #(W32 0)
    | uint64T => #(W64 0)
    | int8T => #(W8 0)
    | int16T => nil
    | int32T => #(W32 0)
    | int64T => #(W64 0)

    | stringT => #(str "")
    (* | arrayT (len : nat) (elem : go_type) *)
    | sliceT _ => slice_nil
    | structT decls => fold_right PairV #() (fmap (zero_val ∘ snd) decls)
    | ptrT => nil
    | funcT => nil
    | interfaceT => interface_nil
    | mapT _ _ => nil
    | chanT _ => nil
    end.
End val_types.

Fixpoint go_type_size_def (t : go_type) : nat :=
  match t with
  | structT d =>
      (fix go_type_size_struct d : nat :=
        match d with
        | [] => O
        | (_,t) :: d => (go_type_size_def t + go_type_size_struct d)%nat
        end
      ) d
  | sliceT e => 3
  | interfaceT => 3
  | _ => 1
  end.
Program Definition go_type_size := unseal (_:seal (@go_type_size_def)). Obligation 1. by eexists. Qed.
Definition go_type_size_unseal : go_type_size = _ := seal_eq _.

Reserved Notation "l +ₗ[ t ] z" (at level 50, left associativity, format "l  +ₗ[ t ]  z").
Notation "l +ₗ[ t ] z" := (l +ₗ go_type_size t * z) : stdpp_scope .
Notation "e1 +ₗ[ t ] e2" := (BinOp (OffsetOp (go_type_size t)) e1%E e2%E) : expr_scope .

Section go_lang.
  Context `{ffi_syntax}.
  Local Coercion Var' (s:string): expr := Var s.

  (** allocation with a type annotation *)
  Definition ref_ty_def (t : go_type) : val := λ: "v", ref (Var "v").
  Program Definition ref_ty := unseal (_:seal (@ref_ty_def)). Obligation 1. by eexists. Qed.
  Definition ref_ty_unseal : ref_ty = _ := seal_eq _.

  Fixpoint load_ty_def (t : go_type) : val :=
    match t with
    | structT d =>
        (fix load_ty_struct d : val :=
          match d with
          | [] => (λ: <>, #())%V
          | (_,t) :: d => (λ: "l", (load_ty_def t "l", load_ty_struct d ("l" +ₗ[t] #1)))%V
          end) d
    | sliceT e => (λ: "l", (!("l" +ₗ #0), !("l" +ₗ #1), !("l" +ₗ #2)))%V
    | interfaceT => (λ: "l", (!("l" +ₗ #0), !("l" +ₗ #1), !("l" +ₗ #2)))%V
    | _ => (λ: "l", !(Var "l"))%V
    end.
  Program Definition load_ty := unseal (_:seal (@load_ty_def)). Obligation 1. by eexists. Qed.
  Definition load_ty_unseal : load_ty = _ := seal_eq _.

  Fixpoint store_ty_def (t : go_type): val :=
    match t with
    | structT d =>
        (fix store_struct d : val :=
          match d with
          | [] => (λ: <>, #())%V
          | (f,t) :: d => (λ: "pv", let: "p" := Fst "pv" in
                                  let: "v" := Snd "pv" in
                                  store_ty_def t ("p", Fst "v");;
                                  store_struct d (BinOp (OffsetOp (go_type_size t))
                                                        "p" #1, Snd "v"))%V
          end) d
    | sliceT e => (λ: "pv", let: "p" := Fst "pv" in
                           let: "v" := Snd "pv" in
                           let: (("a", "b"), "c") := "v" in
                           "p" +ₗ #0 <- "a" ;;
                           "p" +ₗ #1 <- "b" ;;
                           "p" +ₗ #2 <- "c")%V
    | interfaceT => (λ: "pv", let: "p" := Fst "pv" in
                             let: "v" := Snd "pv" in
                             let: (("a", "b"), "c") := "v" in
                             "p" +ₗ #0 <- "a" ;;
                             "p" +ₗ #1 <- "b" ;;
                             "p" +ₗ #2 <- "c")%V
    | _ => (λ: "pv", Fst "pv" <- Snd "pv")%V
    end.
  Program Definition store_ty := unseal (_:seal (@store_ty_def)). Obligation 1. by eexists. Qed.
  Definition store_ty_unseal : store_ty = _ := seal_eq _.

End go_lang.

Reserved Notation "![ t ] e" (at level 9, right associativity, format "![ t ]  e").
Notation "![ t ] e" := (load_ty t e%E) : expr_scope.
(* NOTE: in code we want to supply arbitrary expressions, so we have the usual
   notation, but the specs should be in terms of value pairs, so we have a
   similar notation in the value-scope (even though this is an expression and
   not a value)

   See the HeapLang documentation in Iris for par, which has a similar
   trick. *)
(* FIXME: these notations are a little messed up; they get unfolded where they shouldn't, etc. *)
Reserved Notation "e1 <-[ t ] e2" (at level 80, format "e1  <-[ t ]  e2").
Notation "e1 <-[ t ] e2" := (store_ty t (Pair e1%E e2%E)) : expr_scope.
Notation "v1 <-[ t ] v2" := (store_ty t (PairV v1%V v2%V)) : val_scope.

(** * Struct library
    Access field offsets within pairs by name rather than using Fst and Snd. *)

Module struct.
Section goose_lang.
Context `{ffi_sem: ffi_semantics}.

Definition descriptor := list (string * go_type).
Implicit Types (d:descriptor).
Infix "=?" := (String.eqb).

Fixpoint get_field_def d (f0: string) : val :=
  match d with
  | [] => λ: <>, #()
  | (f,_)::fs => if f =? f0
               then (λ: "v", Fst (Var "v"))%V
               else (λ: "v", get_field_def fs f0 (Snd (Var "v")))%V
  end.
Program Definition get_field := unseal (_:seal (@get_field_def)). Obligation 1. by eexists. Qed.
Definition get_field_unseal : get_field = _ := seal_eq _.

(* FIXME: what does _f mean? Want better name. *)
Fixpoint get_field_f d f0: val -> val :=
  λ v, match d with
       | [] => #()
       | (f,_)::fs =>
         match v with
         | PairV v1 v2 => if f =? f0 then v1 else get_field_f fs f0 v2
         | _ => #()
         end
       end.

Fixpoint set_field_f d f0 fv: val -> val :=
  λ v, match d with
       | [] => v
       | (f,_)::fs =>
         match v with
         | PairV v1 v2 =>
           if f =? f0
           then PairV fv v2
           else PairV v1 (set_field_f fs f0 fv v2)
         | _ => v
         end
       end.

Fixpoint assocl_lookup {A} (field_vals: list (string * A)) (f0: string) : option A :=
  match field_vals with
  | [] => None
  | (f, v)::fs => if f =? f0 then Some v else assocl_lookup fs f0
  end.

(* XXX: this is not sealed because symbolic execution will require first
   stepping through all the exprs. Would be better to implement this using a
   gooselang function that takes in a list.
 *)
Fixpoint build_struct d (field_vals: list (string*expr)) : expr :=
  let lookup_f := assocl_lookup field_vals in
  match d with
  | [] => (Val #())
  | (f,ft)::fs => let e := default (Val (zero_val ft)) (lookup_f f) in
                (e, build_struct fs field_vals)
  end.

Fixpoint build_struct_f d (field_vals: list (string*val)): val :=
  let lookup_f := assocl_lookup field_vals in
  match d with
  | [] => (#())
  | (f,ft)::fs =>
    let e := default (zero_val ft) (lookup_f f) in
    let e' := build_struct_f fs field_vals in
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
(** structFieldRef gives a function that takes a location and constant pointer
arithmetic on it (which is pre-computed based on the field and descriptor). *)
Definition field_ref d f0: val :=
  λ: "p", BinOp (OffsetOp (field_offset d f0).1) (Var "p") #1
.

Definition field_ref_f d f0 l: loc :=
  l +ₗ (field_offset d f0).1
.

Definition field_ty_f d f0 : go_type :=
  (field_offset d f0).2
.

End goose_lang.
End struct.

Declare Scope struct_scope.
Notation "f :: t" := (@pair string go_type f%string t) : struct_scope.
Notation "f ::= v" := (@pair string val f%string v%V) (at level 60) : val_scope.
Notation "f ::= v" := (@pair string expr f%string v%E) (at level 60) : expr_scope.
Delimit Scope struct_scope with struct.
