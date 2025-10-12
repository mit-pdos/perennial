From New.golang.defn Require Export typing intoval.
From Perennial Require Import base.

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
Context `{!NamedUnderlyingTypes}.
Context `{ffi_syntax}.

Definition alloc_def (V : Type) `{!IntoVal V} : val := (λ: <>, ref #(zero_val V)).
Program Definition alloc := sealed @alloc_def.
Definition alloc_unseal : alloc = _ := seal_eq _.

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

Class MemOps :=
{
  load : go.type → val;
  store : go.type → val;
  size : go.type → Z;

  is_load_underlying t : load t = load (to_underlying t);
  is_load_primitive t (H : is_primitive t) : load t = (λ: "l", ! "l")%V;
  is_load_struct fds :
    let body := (foldl (λ '(offset, ld) (fd : go.field_decl),
                          (offset,
                             (ld, (match fd with
                                   | go.FieldDecl _ t 
                                   | go.EmbeddedField _ t => load t
                                   end)
                                    (BinOp (OffsetOp offset) #(W64 1) "l"))%E)
                   ) (0, Val #()) fds) in
    load (go.StructType fds) = (λ: "l", body.2)%V;
  is_load_array n elem :
    let body := (Z.iter n
                   (λ '(offset, ld),
                      (offset + 1,
                         (ld, load elem
                                (BinOp (OffsetOp (offset * size elem))
                                   #(W64 1) "l"))%E)
                   ) (0, Val #())) in
    load (go.ArrayType n elem) = (λ: "l", body.2)%V;

  size_underlying t : size t = size (to_underlying t);
  size_primitive t (H : is_primitive t) : size t = 1;
  size_struct fds : size (go.StructType fds) =
                    foldl Z.add 0 ((λ fd, match fd with
                                          | go.FieldDecl _ t
                                          | go.EmbeddedField _ t => size t
                                          end
                                   ) <$> fds);
  size_array n elem : size (go.ArrayType n elem) = n * size elem;
}.

Context `{!MemOps}.

Record foo_t := 
  mk {
      a : w64;
    }.
Global Instance into_val_foo : IntoVal foo_t :=
  {| to_val_def := λ v, (#v.(a), #())%V; zero_val := (mk (zero_val _)) |}.

Definition foo : go.type := go.Named "foo"%go [].
Definition foo_impl : go.type := go.StructType [(go.FieldDecl "a"%go uint64)].

Class foo_type_assumptions : Prop :=
  {
    foo_underlying : named_to_underlying "foo"%go [] = foo_impl
  }.

Context `{!foo_type_assumptions}.

Goal size (go.ArrayType 3 foo) = 3.
  rewrite size_array size_underlying /= foo_underlying
    size_struct /= size_primitive //. constructor.
Qed.

Definition struct_field_get (field_name : go_string) (t : go.type) : val :=
  match to_underlying t with
  | go.StructType fds =>
      (* Look for the first field named `field_name`. *)
      
  end
.

Goal load (go.ArrayType 3 foo) = (λ: "l", ! "l")%V.
  rewrite is_load_array /=. vm_compute Z.add.
  rewrite is_load_underlying /=. foo_underlying.
  rewrite is_load_struct /=.

Goal load foo = (λ: "l", ! "l")%V.
  rewrite is_load_underlying /= foo_underlying.
  rewrite is_load_struct /=.

  rewrite is_load_primitive; [|constructor].


(* load t -> (load f1, load f2, load f3) when underlying(t) is a struct with
   fields f1, f2, f3. *)
Inductive is_load : go.type → val → Prop :=
| is_load_uint64 t (H : is_primitive t) : is_load t (λ: "l", "l")%V
| is_load_struct t fds (H : underlying t = go.StructType fds)
                 (field_loads : list val)
  :
  is_load t (λ: "l", "l")%V
.

Definition load_def (t : go.type) : val := mem.load (to_mem_type t).
Program Definition load := sealed @load_def.
Definition load_unseal : load = _ := seal_eq _.

Definition store_def (t : go.type) : val := mem.store (to_mem_type t).
Program Definition store := sealed @store_def.
Definition store_unseal : store = _ := seal_eq _.

End defs.
End go.
