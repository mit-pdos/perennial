From Perennial.goose_lang Require Export notation typing.
From Perennial.goose_lang.lib Require Import map.impl.

Reserved Notation "![ t ] e"
         (at level 9, right associativity, format "![ t ]  e").
Reserved Notation "e1 <-[ t ] e2"
         (at level 80, format "e1  <-[ t ]  e2").

Section goose_lang.
  Context {ext} {ext_ty: ext_types ext}.

  (** allocation with a type annotation *)
  Definition ref_to (t:ty): val := λ: "v", ref (Var "v").
  Definition ref_zero (t:ty): val := λ: <>, ref (zero_val t).

  Fixpoint load_ty t: val :=
    match t with
    | prodT t1 t2 => λ: "l", (load_ty t1 (Var "l"), load_ty t2 (Var "l" +ₗ[t1] #1))
    | baseT unitBT => λ: <>, #()
    | _ => λ: "l", !(Var "l")
    end.

  Fixpoint store_ty t: val :=
    match t with
    | prodT t1 t2 => λ: "pv",
                    let: "p" := Fst (Var "pv") in
                    let: "v" := Snd (Var "pv") in
                    store_ty t1 (Var "p", Fst (Var "v"));;
                    store_ty t2 (Var "p" +ₗ[t1] #1, Snd (Var "v"))
    | baseT unitBT => λ: <>, #()
    | _ => λ: "pv", Fst (Var "pv") <- Snd (Var "pv")
    end.

  Fixpoint store_ty' t: val :=
    match t with
    | prodT t1 t2 => λ: "p" "v",
                    store_ty' t1 (Var "p") (Fst (Var "v"));;
                    store_ty' t2 (Var "p" +ₗ[t1] #1) (Snd (Var "v"))
    | baseT unitBT => λ: <> <>, #()
    | _ => λ: "p" "v", Var "p" <- Var "v"
    end.

  (* approximate types for closed values, as obligatons for using load_ty and
  store_ty *)

  Inductive lit_ty : base_lit -> ty -> Prop :=
  | int_ty x : lit_ty (LitInt x) uint64T
  | int32_ty x : lit_ty (LitInt32 x) uint32T
  | int8_ty x : lit_ty (LitByte x) byteT
  | bool_ty x : lit_ty (LitBool x) boolT
  | string_ty x : lit_ty (LitString x) stringT
  | unit_ty : lit_ty LitUnit unitT
  | loc_array_ty x t : lit_ty (LitLoc x) (arrayT t)
  | loc_struct_ty x ts : lit_ty (LitLoc x) (structRefT ts)
  .

  Inductive val_ty : val -> ty -> Prop :=
  | base_ty l t : lit_ty l t -> val_ty (LitV l) t
  | val_ty_pair v1 t1 v2 t2 : val_ty v1 t1 ->
                              val_ty v2 t2 ->
                              val_ty (PairV v1 v2) (prodT t1 t2)
  | sum_ty_l v1 t1 t2 : val_ty v1 t1 ->
                        val_ty (InjLV v1) (sumT t1 t2)
  | sum_ty_r v2 t1 t2 : val_ty v2 t2 ->
                        val_ty (InjRV v2) (sumT t1 t2)
  | map_def_ty v t : val_ty v t ->
                     val_ty (MapNilV v) (mapValT t)
  | map_cons_ty k v mv' t : val_ty mv' (mapValT t) ->
                            val_ty k uint64T ->
                            val_ty v t ->
                            val_ty (InjRV (k, v, mv')%V) (mapValT t)
  | rec_ty f x e t1 t2 : val_ty (RecV f x e) (arrowT t1 t2)
  .

  Ltac invc H := inversion H; subst; clear H.

  (* Prove that this is a sensible definition *)

  Theorem zero_val_ty' t : has_zero t -> val_ty (zero_val t) t.
  Proof.
    induction t; simpl; intros; intuition eauto using val_ty, lit_ty.
    destruct t; eauto using val_ty, lit_ty.
  Qed.

  Theorem val_ty_len {v t} :
    val_ty v t ->
    length (flatten_struct v) = Z.to_nat (ty_size t).
  Proof.
    induction 1; simpl; rewrite -> ?app_length in *; auto.
    - invc H; eauto.
    - pose proof (ty_size_ge_0 t1).
      pose proof (ty_size_ge_0 t2).
      lia.
  Qed.

  Theorem val_ty_flatten_length v t :
    val_ty v t ->
    length (flatten_struct v) = length (flatten_ty t).
  Proof.
    induction 1; simpl; auto.
    - invc H; eauto.
    - rewrite ?app_length.
      lia.
  Qed.

End goose_lang.

Ltac val_ty :=
  lazymatch goal with
  | [ H: val_ty ?v ?t |- val_ty ?v ?t ] => exact H
  | |- val_ty _ _ => first [ by auto with val_ty nocore | solve [ repeat constructor ] ]
  | _ => fail "not a val_ty goal"
  end.

Hint Resolve zero_val_ty' : val_ty.

Hint Extern 2 (val_ty _ _) => val_ty : core.

Notation "![ t ] e" := (load_ty t e%E) : expr_scope.
(* NOTE: in code we want to supply arbitrary expressions, so we have the usual
   notation, but the specs should be in terms of value pairs, so we have a
   similar notation in the value-scope (even though this is an expression and
   not a value)

   See the heap_lang documentation in Iris for par, which has a similar
   trick. *)
Notation "e1 <-[ t ] e2" := (store_ty t (Pair e1%E e2%E)) : expr_scope.
Notation "v1 <-[ t ] v2" := (store_ty t (PairV v1%V v2%V)) : val_scope.
