(* Trusted stuff that's conceptually part of the GooseLang semantics. E.g.
   assumptions about valid GoContext and definition of zero values via
   IntoVal. *)

From Perennial.goose_lang Require Export lang.
From Perennial Require Export base.

Definition slice_index_ref `{GoContext} (elem_type : go.type) (i : Z) (s : slice.t) : loc :=
  array_index_ref elem_type i s.(slice.ptr).

Global Notation "()" := tt : val_scope.
Global Opaque into_val.

(* Shortcircuit Boolean connectives *)
Notation "e1 && e2" :=
  (If e1%E e2%E #false) (only parsing) : expr_scope.
Notation "e1 || e2" :=
  (If e1%E #true e2%E) (only parsing) : expr_scope.

Global Notation "# x" := (into_val x%go).
Global Notation "#" := into_val (at level 0).

(* built-in functions *)
Definition append : go_string := "append".
Definition cap : go_string := "cap".
Definition clear : go_string := "clear".
Definition close : go_string := "close".
Definition copy : go_string := "copy".
Definition delete : go_string := "delete".
Definition len : go_string := "len".
Definition make3 : go_string := "make3".
Definition make2 : go_string := "make2".
Definition make1 : go_string := "make1".
Definition min : go_string := "min".
Definition max : go_string := "max".
Definition panic : go_string := "panic".

(* helpers for signed comparisons *)
Section helpers.
Context `{ffi_syntax}.
Definition int_lt : val := λ: "x" "y", BinOp SignedLtOp "x" "y".
Definition int_leq : val := λ: "x" "y", BinOp SignedLeOp "x" "y".
Definition int_geq : val := λ: "x" "y", int_leq "y" "x".
Definition int_gt : val := λ: "x" "y", int_lt "y" "x".
End helpers.

Module go.

(* built-in types *)
Definition uint64 : go.type := go.Named "uint64"%go [].
Definition uint32 : go.type := go.Named "uint32"%go [].
Definition uint16 : go.type := go.Named "uint16"%go [].
Definition uint8 : go.type := go.Named "uint8"%go [].
Definition int64 : go.type := go.Named "int64"%go [].
Definition int32 : go.type := go.Named "int32"%go [].
Definition int16 : go.type := go.Named "int16"%go [].
Definition int8 : go.type := go.Named "int8"%go [].
Definition string : go.type := go.Named "string"%go [].
Definition bool : go.type := go.Named "bool"%go [].
Definition byte : go.type := uint8.
Definition rune : go.type := uint32.

Section defs.
Context `{ffi_syntax}.

Inductive is_primitive : go.type → Prop :=
| is_primitive_uint64 : is_primitive go.uint64
| is_primitive_uint32 : is_primitive go.uint32
| is_primitive_uint16 : is_primitive go.uint16
| is_primitive_uint8 : is_primitive go.uint8
| is_primitive_int64 : is_primitive go.int64
| is_primitive_int32 : is_primitive go.int32
| is_primitive_int16 : is_primitive go.int16
| is_primitive_int8 : is_primitive go.int8
| is_primitive_string : is_primitive go.string
| is_primitive_bool : is_primitive go.bool

| is_primitive_pointer t : is_primitive (go.PointerType t)
| is_primitive_function sig : is_primitive (go.FunctionType sig)
| is_primitive_interface elems : is_primitive (go.InterfaceType elems)
| is_primitive_slice elem : is_primitive (go.SliceType elem)
| is_primitive_map kt vt : is_primitive (go.MapType kt vt)
| is_primitive_channel dir t : is_primitive (go.ChannelType dir t).

Inductive is_primitive_zero_val : go.type → ∀ {V} `{!IntoVal V}, V → Prop :=
| is_primitive_zero_val_uint64 : is_primitive_zero_val go.uint64 (W64 0)
| is_primitive_zero_val_uint32 : is_primitive_zero_val go.uint32 (W32 0)
| is_primitive_zero_val_uint16 : is_primitive_zero_val go.uint16 (W16 0)
| is_primitive_zero_val_uint8 : is_primitive_zero_val go.uint8 (W8 0)
| is_primitive_zero_val_int64 : is_primitive_zero_val go.int64 (W64 0)
| is_primitive_zero_val_int32 : is_primitive_zero_val go.int32 (W32 0)
| is_primitive_zero_val_int16 : is_primitive_zero_val go.int16 (W16 0)
| is_primitive_zero_val_int8 : is_primitive_zero_val go.int8 (W8 0)
| is_primitive_zero_val_string : is_primitive_zero_val go.string ""%go
| is_primitive_zero_val_bool : is_primitive_zero_val go.bool false

| is_primitive_zero_val_pointer t : is_primitive_zero_val (go.PointerType t) null
| is_primitive_zero_val_function t : is_primitive_zero_val (go.FunctionType t) func.nil
(* | is_primitive_interface elems : is_primitive (go.InterfaceType elems) *)
| is_primitive_zero_val_slice elem : is_primitive_zero_val (go.SliceType elem) slice.nil
| is_primitive_zero_val_map kt vt : is_primitive_zero_val (go.MapType kt vt) null
| is_primitive_zero_val_channel dir t : is_primitive_zero_val (go.ChannelType dir t) null
.

(** [go.ValidCore] defines when a GoContext is valid, excluding slice, map, and
    channel stuff. *)
Class CoreSemantics `{!GoContext} :=
{
  alloc_underlying t : alloc t = alloc (to_underlying t);
  alloc_primitive t {V} (v : V) `{!IntoVal V} (H : is_primitive_zero_val t v) :
  alloc t = (λ: <>, ref #v)%V;
  alloc_struct fds :
    alloc (go.StructType fds) =
    (λ: <>,
        let: "l" := GoInstruction GoPrealloc #() in
        foldl (λ alloc_so_far fd,
                 alloc_so_far ;;
                 let (field_name, field_type) := match fd with
                                                 | go.FieldDecl n t => pair n t
                                                 | go.EmbeddedField n t => pair n t
                                                 end in
                let field_addr :=
                  (GoInstruction (StructFieldRef (go.StructType fds) field_name) "l") in
                let: "l_field" := GoInstruction (GoAlloc field_type) #() in
                if: ("l_field" ≠ field_addr) then
                  GoInstruction AngelicExit #()
                else
                  #()
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
                let field_addr :=
                  (GoInstruction (StructFieldRef (go.StructType fds) field_name) "l") in
                let field_val := (GoInstruction (GoLoad field_type) field_addr) in
                GoInstruction (StructFieldSet field_name) (struct_so_far, field_val)
         ) (StructV ∅) fds)%V;
  load_array n elem_type :
    load (go.ArrayType n elem_type) =
    (λ: "l",
       foldl (λ array_so_far j,
                let elem_addr :=
                  GoInstruction (IndexRef (go.ArrayType n elem_type)) #(W64 j) "l" in
                let elem_val := GoInstruction (GoLoad elem_type) elem_addr in
                GoInstruction ArrayAppend (array_so_far, elem_val)
         )
             (ArrayV []) (seqZ 0 n)
    )%V;

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
                let field_addr :=
                  (GoInstruction (StructFieldRef (go.StructType fds) field_name) "l") in
                let field_val := (GoInstruction (StructFieldGet field_name) "v") in
                GoInstruction (GoStore field_type) (field_addr, field_val)
         ) (StructV ∅) fds)%V;
  store_array n elem_type :
    store (go.ArrayType n elem_type) =
    (λ: "l" "v",
       foldl (λ str_so_far j,
                str_so_far;;
                let elem_addr :=
                  GoInstruction (IndexRef (go.ArrayType n elem_type)) #(W64 j) "l" in
                let elem_val := GoInstruction (Index $ go.ArrayType n elem_type) ("v", #(W64 n)) in
                GoInstruction (GoStore elem_type) (elem_addr, elem_val))
             (ArrayV []) (seqZ 0 n)
    )%V;

  struct_field_ref_underlying t : struct_field_ref t = struct_field_ref (to_underlying t);

  index_ref_underlying t : index_ref t = index_ref (to_underlying t);
  index_ref_array n elem_type i l :
    index_ref (go.ArrayType n elem_type) i #l = #(array_index_ref elem_type i l);

  index_underlying t : index t = index (to_underlying t);
  index_array n elem_type i l v (Hinrange : l !! (Z.to_nat i) = Some v):
    index (go.ArrayType n elem_type) i (ArrayV l) = (Val v);

  len_underlying t : functions len [t] = functions len [to_underlying t];

  cap_underlying t : functions cap [t] = functions cap [to_underlying t];

  make3_underlying t : functions make3 [t] = functions make3 [to_underlying t];
  make2_underlying t : functions make2 [t] = functions make2 [to_underlying t];
  make1_underlying t : functions make1 [t] = functions make1 [to_underlying t];
}.

End defs.
End go.

Global Notation "'func_call' a b" := (GoInstruction (FuncCall a b)) (at level 1).

Notation "@! func" :=
  #(functions func []) (at level 1, no associativity, format "@! func") : expr_scope.

Notation "![ t ] e" := (GoInstruction (GoLoad t) e%E)
                         (at level 9, right associativity, format "![ t ]  e") : expr_scope.
Notation "e1 <-[ t ] e2" := (GoInstruction (GoStore t) (Pair e1%E e2%E))
                             (at level 80, format "e1  <-[ t ]  e2") : expr_scope.
