(* Trusted stuff that's conceptually part of the GooseLang semantics. E.g.
   assumptions about valid GoContext and definition of zero values via
   IntoVal. *)

From Perennial.goose_lang Require Export lang.
From Perennial Require Export base.

#[warning="-uniform-inheritance"]
Global Coercion GoInstruction : go_op >-> val.

Global Notation "()" := tt : val_scope.
Global Opaque into_val.

Global Notation "# x" := (into_val x%go).
Global Notation "#" := into_val (at level 0).

(* Shortcircuit Boolean connectives *)
Global Notation "e1 && e2" :=
  (If e1%E e2%E #false) (only parsing) : expr_scope.
Global Notation "e1 || e2" :=
  (If e1%E #true e2%E) (only parsing) : expr_scope.

(* Notation for signed comparisons *)
Global Notation int_lt e1 e2 := (BinOp SignedLtOp e1%E e2%E).
Global Notation int_leq e1 e2 := (BinOp SignedLeOp e1%E e2%E).
Global Notation int_gt e1 e2 := (BinOp SignedLeOp e2%E e1%E).
Global Notation int_geq e1 e2 := (BinOp SignedLeOp e2%E e1%E).

Module go.
Section defs.
Context {ext : ffi_syntax}.
(** This semantics considers several Go types to be [primitive] in the sense
    that they are modeled as taking a single heap location. Predeclared types
    and in their own file. *)
Inductive is_primitive : go.type → Prop :=
| is_primitive_pointer t : is_primitive (go.PointerType t)
| is_primitive_function sig : is_primitive (go.FunctionType sig)
| is_primitive_interface elems : is_primitive (go.InterfaceType elems)
| is_primitive_slice elem : is_primitive (go.SliceType elem)
| is_primitive_map kt vt : is_primitive (go.MapType kt vt)
| is_primitive_channel dir t : is_primitive (go.ChannelType dir t).

Inductive is_primitive_zero_val : go.type → ∀ {V} `{!IntoVal V}, V → Prop :=
| is_primitive_zero_val_pointer t : is_primitive_zero_val (go.PointerType t) null
| is_primitive_zero_val_function t : is_primitive_zero_val (go.FunctionType t) func.nil
(* | is_primitive_interface elems : is_primitive (go.InterfaceType elems) *)
| is_primitive_zero_val_slice elem : is_primitive_zero_val (go.SliceType elem) slice.nil
| is_primitive_zero_val_map kt vt : is_primitive_zero_val (go.MapType kt vt) null
| is_primitive_zero_val_channel dir t : is_primitive_zero_val (go.ChannelType dir t) null.

(** [go.CoreSemantics] defines the basics of when a GoContext is valid,
    excluding predeclared types (including primitives), slice, map, and
    channels, each of which is in their own file.

    The rules prefixed with [_] should not be used in any program proofs. *)
Class CoreSemantics {go_ctx : GoContext} :=
{
  alloc_underlying t : alloc t = alloc (to_underlying t);
  alloc_primitive t {V} (v : V) `{!IntoVal V} (H : is_primitive_zero_val t v) :
    alloc t = (λ: <>, ref #v)%V;

  alloc_struct fds :
    alloc (go.StructType fds) =
    (λ: <>,
        let: "l" := GoPrealloc #() in
        foldl (λ alloc_so_far fd,
                 alloc_so_far ;;
                 let (field_name, field_type) := match fd with
                                                 | go.FieldDecl n t => pair n t
                                                 | go.EmbeddedField n t => pair n t
                                                 end in
                let field_addr := StructFieldRef (go.StructType fds) field_name "l" in
                let: "l_field" := GoAlloc field_type #() in
                if: ("l_field" ≠ field_addr) then AngelicExit #()
                else #()
          ) #() fds ;;
        "l")%V;
  alloc_array n elem : alloc (go.ArrayType n elem) = alloc (go.ArrayType n elem); (* TODO *)

  load_underlying t : load t = load (to_underlying t);
  load_primitive t (H : is_primitive t) : load t = (λ: "l", ! "l")%V;
  load_struct fds :
    load (go.StructType fds) =
    (λ: "l",
       foldl (λ struct_so_far fd,
                let (field_name, field_type) := match fd with
                                                | go.FieldDecl n t => pair n t
                                                | go.EmbeddedField n t => pair n t
                                                end in
                let field_addr := StructFieldRef (go.StructType fds) field_name "l" in
                let field_val := GoLoad field_type field_addr in
                StructFieldSet field_name (struct_so_far, field_val)
         ) (StructV ∅) fds)%V;
  load_array n elem_type :
    load (go.ArrayType n elem_type) =
    if decide (¬(0 ≤ n < 2^63-1)) then
      (λ: "l", AngelicExit #())%V
        (* the compiler guarantees that any compiled code does not have an array this size *)
    else
      (λ: "l",
         (rec: "recur" "n" :=
            if: "n" = #(W64 0) then (ArrayV [])
            else let: "array_so_far" := "recur" ("n" - #(W64 1)) in
                 let: "elem_addr" := IndexRef (go.ArrayType n elem_type) ("l", "n" - #(W64 1)) in
                 let: "elem_val" := GoLoad elem_type "elem_addr" in
                 ArrayAppend ("array_so_far", "elem_val")
         ) #(W64 n))%V;

  store_underlying t : store t = store (to_underlying t);
  store_primitive t (H : is_primitive t) : store t = (λ: "l" "v", "l" <- "v")%V;
  store_struct fds :
    store (go.StructType fds) =
    (λ: "l" "v",
       foldl (λ store_so_far fd,
                store_so_far;;
                let (field_name, field_type) := match fd with
                                                | go.FieldDecl n t => pair n t
                                                | go.EmbeddedField n t => pair n t
                                                end in
                let field_addr := StructFieldRef (go.StructType fds) field_name "l" in
                let field_val := StructFieldGet field_name "v" in
                GoStore field_type (field_addr, field_val)
         ) (StructV ∅) fds)%V;
  store_array n elem_type :
    store (go.ArrayType n elem_type) =
    (λ: "l" "v",
       foldl (λ str_so_far j,
                str_so_far;;
                let elem_addr := IndexRef (go.ArrayType n elem_type) ("l", #(W64 j)) in
                let elem_val := Index (go.ArrayType n elem_type) ("v", #(W64 n)) in
                GoStore elem_type (elem_addr, elem_val))
             (ArrayV []) (seqZ 0 n)
    )%V;

  struct_field_ref_underlying t : struct_field_ref t = struct_field_ref (to_underlying t);

  index_ref_underlying t : index_ref t = index_ref (to_underlying t);
  index_ref_array n elem_type i l :
    index_ref (go.ArrayType n elem_type) i #l = #(array_index_ref elem_type i l);

  index_underlying t : index t = index (to_underlying t);
  index_array n elem_type i l v (Hinrange : l !! (Z.to_nat i) = Some v):
    index (go.ArrayType n elem_type) i (ArrayV l) = (Val v);

  array_index_ref_add t i j l :
    array_index_ref t (i + j) l = array_index_ref t j (array_index_ref t i l);

  method_interface t m (H : is_interface_type t = true) :
    #(methods t m) = (InterfaceGet m);
}.

End defs.
End go.

Notation "@! func" :=
  #(functions func []) (at level 1, no associativity, format "@! func") : expr_scope.

Notation "![ t ] e" := (GoInstruction (GoLoad t) e%E)
                         (at level 9, right associativity, format "![ t ]  e") : expr_scope.
Notation "e1 <-[ t ] e2" := (GoInstruction (GoStore t) (Pair e1%E e2%E))
                             (at level 80, format "e1  <-[ t ]  e2") : expr_scope.
