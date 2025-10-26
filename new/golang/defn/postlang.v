(* Trusted stuff that's conceptually part of the GooseLang semantics. E.g.
   assumptions about valid GoContext and definition of zero values via
   IntoVal. *)

From Perennial.goose_lang Require Export lang notation.
From Perennial Require Export base.

(** [GoContext] contains several low-level Go functions for typed memory access,
    map updates, etc. *)
Class GoContext {ext : ffi_syntax} : Type :=
  {
    global_addr : go_string → loc;
    functions : go_string → list go.type → val;
    methods : go.type → go_string → val;

    alloc : go.type → val;
    load : go.type → val;
    store : go.type → val;

    struct_field_ref : go.type → go_string → loc → loc;

    index (container_type : go.type) (i : Z) (v : val) : expr;
    index_ref (container_type : go.type) (i : Z) (v : val) : expr;
    array_index_ref (elem_type : go.type) (i : Z) (l : loc) : loc;

    to_underlying : go.type → go.type;
    is_map_pure (v : val) (m : val → bool * val) : Prop;
    map_lookup : val → val → bool * val;
    map_insert : val → val → val → val;
  }.

Definition slice_index_ref `{GoContext} (elem_type : go.type) (i : Z) (s : slice.t) : loc :=
  array_index_ref elem_type i s.(slice.ptr).

Class IntoVal {ext : ffi_syntax} (V : Type) :=
  {
    to_val_def : V → val;
    zero_val : V;
  }.

Program Definition to_val := sealed @to_val_def.
Definition to_val_unseal : to_val = _ := seal_eq _.
Arguments to_val {_ _ _} v%go.
Arguments zero_val {_} (V) {_}.
(* Disable Notation "# l". *)
Global Notation "# x" := (to_val x%go).
Global Notation "#" := to_val (at level 0).

(* One of [V] or [ty] should not be an evar before doing typeclass search *)
Global Hint Mode IntoVal - ! : typeclass_instances.

Module func.
Section defn.
Context `{ffi_syntax}.
Record t := mk {
      f : binder;
      x : binder;
      e : expr;
    }.
Definition nil := mk <> <> (LitV LitPoison).
End defn.
End func.

Module chan.
Definition t := loc.
Definition nil : chan.t := null.
End chan.

Module interface.
Section goose_lang.
Context `{ffi_syntax}.

Inductive t :=
| mk (ty : go.type) (v : val) : t
| nil : t.

End goose_lang.
End interface.

Module array.
Section goose_lang.
(* Using [vec] here because the [to_val] must be a total function that always
   meets [has_go_type]. An alternative could be a sigma type. *)
Record t (ty : go.type) (V : Type) (n : nat) :=
mk { vec : vec V n }.
End goose_lang.
End array.
Arguments array.mk (ty) {_ _} (_).
Arguments array.vec {_ _ _} (_).

Section into_val_instances.
Context `{ffi_syntax}.

Global Instance into_val_loc : IntoVal loc :=
  {| to_val_def v := (LitV $ LitLoc v); zero_val := null |}.

Global Instance into_val_w64 : IntoVal w64 :=
  {| to_val_def v := (LitV $ LitInt v); zero_val := W64 0 |}.

Global Instance into_val_w32 : IntoVal w32 :=
  {| to_val_def v := (LitV $ LitInt32 v); zero_val := W32 0 |}.

Global Instance into_val_w16 : IntoVal w16 :=
  {| to_val_def v := (LitV $ LitInt16 v); zero_val := W16 0 |}.

Global Instance into_val_w8 : IntoVal w8 :=
  {| to_val_def v := (LitV $ LitByte v); zero_val := W8 0 |}.

Global Instance into_val_unit : IntoVal () :=
  {| to_val_def _ := (LitV $ LitUnit); zero_val := () |}.

Global Instance into_val_bool : IntoVal bool :=
  {| to_val_def b := (LitV $ LitBool b); zero_val := false |}.

Global Instance into_val_go_string : IntoVal go_string :=
  {| to_val_def s := (LitV $ LitString s); zero_val := ""%go |}.

Global Instance into_val_func : IntoVal func.t :=
  {| to_val_def f := RecV f.(func.f) f.(func.x) f.(func.e); zero_val := func.nil |}.

Global Instance into_val_array t `{!IntoVal V} n : IntoVal (array.t t V n) :=
  {|
    to_val_def v := ArrayV (to_val <$> (vec_to_list v.(array.vec)));
    zero_val := array.mk t $ vreplicate n (zero_val V);
  |}.

Global Instance into_val_slice : IntoVal slice.t :=
  {|
    to_val_def (s: slice.t) := LitV (LitSlice s);
    zero_val := slice.nil;
  |}.

Global Instance into_val_interface : IntoVal interface.t :=
  {|
    to_val_def (i: interface.t) :=
      match i with
      | interface.nil => InterfaceV None
      | interface.mk ty v => InterfaceV $ Some (ty, v)
      end;
    zero_val := interface.nil;
  |}.

End into_val_instances.
Global Notation "()" := tt : val_scope.
Global Opaque to_val.

(* Shortcircuit Boolean connectives *)
Notation "e1 && e2" :=
  (If e1%E e2%E #false) (only parsing) : expr_scope.
Notation "e1 || e2" :=
  (If e1%E #true e2%E) (only parsing) : expr_scope.

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

(* built-in functions *)
Definition make3 : go_string := "make3".
Definition make2 : go_string := "make2".
Definition len : go_string := "len".
Definition cap : go_string := "cap".

Section defs.
Context `{ffi_syntax}.

(* helpers for signed comparisons *)
Definition int_lt : val := λ: "x" "y", BinOp SignedLtOp "x" "y".
Definition int_leq : val := λ: "x" "y", BinOp SignedLeOp "x" "y".
Definition int_geq : val := λ: "x" "y", int_leq "y" "x".
Definition int_gt : val := λ: "x" "y", int_lt "y" "x".

Inductive is_primitive : go.type → Prop :=
| is_primitive_uint64 : is_primitive uint64
| is_primitive_uint32 : is_primitive uint32
| is_primitive_uint16 : is_primitive uint16
| is_primitive_uint8 : is_primitive uint8
| is_primitive_int64 : is_primitive int64
| is_primitive_int32 : is_primitive int32
| is_primitive_int16 : is_primitive int16
| is_primitive_int8 : is_primitive int8
| is_primitive_string : is_primitive string
| is_primitive_bool : is_primitive bool

| is_primitive_pointer t : is_primitive (go.PointerType t)
| is_primitive_function sig : is_primitive (go.FunctionType sig)
| is_primitive_interface elems : is_primitive (go.InterfaceType elems)
| is_primitive_slice elem : is_primitive (go.SliceType elem)
| is_primitive_map kt vt : is_primitive (go.MapType kt vt)
| is_primitive_channel dir t : is_primitive (go.ChannelType dir t).

Inductive is_primitive_zero_val : go.type → ∀ {V} `{!IntoVal V}, V → Prop :=
| is_primitive_zero_val_uint64 : is_primitive_zero_val uint64 (W64 0)
| is_primitive_zero_val_uint32 : is_primitive_zero_val uint32 (W32 0)
| is_primitive_zero_val_uint16 : is_primitive_zero_val uint16 (W16 0)
| is_primitive_zero_val_uint8 : is_primitive_zero_val uint8 (W8 0)
| is_primitive_zero_val_int64 : is_primitive_zero_val int64 (W64 0)
| is_primitive_zero_val_int32 : is_primitive_zero_val int32 (W32 0)
| is_primitive_zero_val_int16 : is_primitive_zero_val int16 (W16 0)
| is_primitive_zero_val_int8 : is_primitive_zero_val int8 (W8 0)
| is_primitive_zero_val_string : is_primitive_zero_val go.string ""%go
| is_primitive_zero_val_bool : is_primitive_zero_val go.bool false

| is_primitive_zero_val_pointer t : is_primitive_zero_val (go.PointerType t) null
| is_primitive_zero_val_function t : is_primitive_zero_val (go.FunctionType t) func.nil
(* | is_primitive_interface elems : is_primitive (go.InterfaceType elems) *)
| is_primitive_zero_val_slice elem : is_primitive_zero_val (go.SliceType elem) slice.nil
| is_primitive_zero_val_map kt vt : is_primitive_zero_val (go.MapType kt vt) null
| is_primitive_zero_val_channel dir t : is_primitive_zero_val (go.ChannelType dir t) null
.

Inductive is_go_step_pure `{!GoContext} :
  ∀ (op : go_op) (arg : val) (e' : expr), Prop :=
| angelic_exit_step : is_go_step_pure AngelicExit #() (GoInstruction AngelicExit #())%E
| load_step t arg : is_go_step_pure (GoLoad t) arg (load t arg)
| store_step t arg : is_go_step_pure (GoStore t) arg (store t arg)
| alloc_step t : is_go_step_pure (GoAlloc t) #() (alloc t #())%E
| prealloc_step (l : loc) : is_go_step_pure GoPrealloc #() #l
| func_call_step f targs : is_go_step_pure (FuncCall f targs) #() (functions f targs)
| method_call_step t m : is_go_step_pure (MethodCall t m) #() (methods t m)
| global_var_addr_step v : is_go_step_pure (GlobalVarAddr v) #() #(global_addr v)
| struct_field_ref_step t f l : is_go_step_pure (StructFieldRef t f) #l #(struct_field_ref t f l)
| struct_field_get_step f m v (Hf : m !! f = Some v) :
  is_go_step_pure (StructFieldGet f) (StructV m) (Val v)
| struct_field_set_step f m v :
  is_go_step_pure (StructFieldSet f) (StructV m, v)%V (StructV $ <[ f := v ]> m)

| internal_len_slice_step_pure elem_type s :
  is_go_step_pure (InternalLen (go.SliceType elem_type)) #s #s.(slice.len)
| internal_len_array_step_pure elem_type n v :
  is_go_step_pure (InternalLen (go.ArrayType n elem_type)) v #(W64 n)

| internal_cap_slice_step_pure elem_type s :
  is_go_step_pure (InternalCap (go.SliceType elem_type)) #s #s.(slice.cap)
| internal_dynamic_array_alloc_pure elem_type (n : w64) :
  is_go_step_pure (InternalDynamicArrayAlloc elem_type) #n
    (GoInstruction (GoAlloc $ go.ArrayType (sint.Z n) elem_type) #())
| internal_slice_make_pure p l c :
  is_go_step_pure InternalMakeSlice (#p, #l, #c) #(slice.mk p l c)
| slice_array_step_pure n elem_type p l c :
  is_go_step_pure (Slice (go.ArrayType n elem_type)) (#p, (#l, #c))%V #(slice.mk p l c)
| index_ref_step t v (j : w64) : is_go_step_pure (IndexRef t) (v, #j) (index_ref t (sint.Z j) v)
| index_step t v (j : w64) : is_go_step_pure (Index t) (v, #j) (index t (sint.Z j) v)
| array_append_step_pure l v : is_go_step_pure ArrayAppend (ArrayV l) (ArrayV $ l ++ [v])
| internal_map_lookup_step_pure m k :
  is_go_step_pure InternalMapLookup (m, k) (let '(ok, v) := map_lookup m k in (v, #ok))
| internal_map_insert_step_pure m k v :
  is_go_step_pure InternalMapLookup (m, k, v) (map_insert m k v)
.

(* TODO: add requirement that goose_go_stepper = this thing *)
Inductive is_go_step `{!GoContext} :
  ∀ (op : go_op) (arg : val) (e' : expr) (s : gset go_string) (s' : gset go_string), Prop :=
| go_step_pure op arg e' (Hpure : is_go_step_pure op arg e') s : is_go_step op arg e' s s
| package_init_check_step s p : is_go_step (PackageInitCheck p) #() #(bool_decide (p ∈ s)) s s
| package_init_mark_step s p : is_go_step (PackageInitMark p) #() #() s (s ∪ {[p]})
.

(** [go.ValidCore] defines when a GoContext is valid, excluding slice, map, and
    channel stuff. *)
Class ValidCore `{!GoContext} :=
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
  index_ref_slice elem_type i s (Hrange : 0 ≤ i < sint.Z s.(slice.len)) :
    index_ref (go.SliceType elem_type) i #s = #(slice_index_ref elem_type i s);

  index_underlying t : index t = index (to_underlying t);
  index_array n elem_type i l v (Hinrange : l !! (Z.to_nat i) = Some v):
    index (go.ArrayType n elem_type) i (ArrayV l) = (Val v);
  index_slice elem_type i (s : slice.t) :
    index (go.SliceType elem_type) i #s =
    GoInstruction (GoLoad elem_type) $ GoInstruction (Index $ go.SliceType elem_type) #(W64 i) #s;

  len_underlying t :
    functions len [t] = functions len [to_underlying t];
  len_slice elem_type :
  functions len [go.TypeLit $ go.SliceType elem_type] =
  (λ: "s", GoInstruction (InternalLen (go.SliceType elem_type)) "s")%V;

  cap_underlying t :
  functions cap [t] = functions cap [to_underlying t];
  cap_slice elem_type :
      functions cap [go.TypeLit $ go.SliceType elem_type] =
      (λ: "s", GoInstruction (InternalCap (go.SliceType elem_type)) "s")%V;

  make3_underlying t :
    functions make3 [t] = functions make3 [to_underlying t];
  make3_slice elem_type :
    functions make3 [go.TypeLit $ go.SliceType elem_type] =
    (λ: "t" "len" "cap",
       if: (int_lt "cap" "len") then Panic "makeslice: cap out of range" else #();;
       if: (int_lt "len" #(W64 0)) then Panic "makeslice: len out of range" else #();;
       if: "cap" = #(W64 0) then
         (* XXX: this computes a nondeterministic unallocated address by using
            "(Loc 1 0) +ₗ ArbiraryInt"*)
         GoInstruction InternalMakeSlice (#(Loc 1 0) +ₗ ArbitraryInt, "len", "cap")
       else
         let: "p" := GoInstruction (InternalDynamicArrayAlloc elem_type) "cap" in
         GoInstruction InternalMakeSlice ("p", "len", "cap"))%V;
  make2_unfold t :
    functions make2 [t] =
    (λ: "t" "sz", GoInstruction (FuncCall make3 [t]) #() "t" "sz" "sz")%V;
}.

End defs.
End go.
