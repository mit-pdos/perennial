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
| is_primitive_zero_val_int8 : is_primitive_zero_val int8 (W8 0).

(* TODO: copied in lifting.v *)
Global Arguments alloc {_ _} (t).
Global Arguments load {_ _} (t).
Global Arguments store {_ _} (t).
Global Arguments struct_field_ref {_ _} (t field loc).
Global Arguments goose_lang.size {_ _} (t).
Existing Class GoContext.

Class MemOps `{!GoContext} :=
{
  alloc_underlying t : alloc t = alloc (to_underlying t);
  alloc_primitive t `{!IntoVal V} (v : V) (H : is_primitive_zero_val t v) :
    alloc t = (λ: <>, ref #v)%V;
  alloc_struct fds :
    let body := (foldl (λ '(offset, ld) (fd : go.field_decl),
                          (offset,
                             (ld, (match fd with
                                   | go.FieldDecl _ t 
                                   | go.EmbeddedField _ t => load t
                                   end)
                                    (BinOp (OffsetOp offset) #(W64 1) "l"))%E)
                   ) (0, Val #()) fds) in
    alloc (go.StructType fds) = (λ: "l", body.2)%V;

  load_underlying t : load t = load (to_underlying t);
  load_primitive t (H : is_primitive t) : load t = (λ: "l", ! "l")%V;
  load_struct fds :
    let body := (foldl (λ '(ld) (fd : go.field_decl),
                          (ld, let (name, t) := (match fd with
                                                 | go.FieldDecl n t => (n, t)%core
                                                 | go.EmbeddedField n t => (n, t)%core
                                                 end) in
                               (GoInstruction $ GoLoad t)
                                 ((GoInstruction $ StructFieldRef (go.StructType fds) name) "l"))%E
                   ) (Val #()) fds) in
    load (go.StructType fds) = (λ: "l", body)%V;
  load_array n elem :
    let body := (Z.iter n
                   (λ '(offset, ld),
                      (offset + 1,
                         (ld, load elem
                                (BinOp (OffsetOp (offset * goose_lang.size elem))
                                  "l" #(W64 1)))%E)
                   ) (0, Val #())) in
    load (go.ArrayType n elem) = (λ: "l", body.2)%V;

  size_underlying t : goose_lang.size t = goose_lang.size (to_underlying t);
  size_primitive t (H : is_primitive t) : goose_lang.size t = 1;
  size_struct fds : goose_lang.size (go.StructType fds) =
                    foldl Z.add 0 ((λ fd, match fd with
                                          | go.FieldDecl _ t
                                          | go.EmbeddedField _ t => goose_lang.size t
                                          end
                                   ) <$> fds);
  size_array n elem : goose_lang.size (go.ArrayType n elem) = n * goose_lang.size elem;

  struct_field_ref_underlying t : struct_field_ref t = struct_field_ref (to_underlying t);
}.

(*
Definition load_def (t : go.type) : val := mem.load (to_mem_type t).
Program Definition load := sealed @load_def.
Definition load_unseal : load = _ := seal_eq _.

Definition store_def (t : go.type) : val := mem.store (to_mem_type t).
Program Definition store := sealed @store_def.
Definition store_unseal : store = _ := seal_eq _. *)

End defs.
End go.
