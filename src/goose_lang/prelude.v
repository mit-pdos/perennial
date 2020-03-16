From Perennial.goose_lang Require Export lang notation typing.
From Perennial.goose_lang.lib Require Export
     typed_mem.impl struct.impl loop.impl
     encoding.impl map.impl slice.impl lock.impl.

(* We provide stubs here for primitive operations to make the Goose unit tests
   compile. *)

(* TODO: replace all of these stubs with real operations *)

Open Scope heap_types.
Open Scope struct_scope.

Definition uint64_to_string {ext: ext_op}: val := λ: <>, #().
Definition strLen {ext: ext_op}: val := λ: "s", #0.

Module Data.
  Section goose_lang.
    Context `{ext_ty:ext_types}.
    Axiom stringToBytes: val.

    Definition Var' s : @expr ext := Var s.
    Local Coercion Var' : string >-> expr.

    Definition bytesToString : val :=
      (rec: "bytesToString" "b" :=
         if: (slice.len "b") = #0
         then (Val #str "")
         else (to_string !(slice.ptr ("b"))) +
              ("bytesToString" ((slice.ptr "b" +ₗ #1, slice.len "b" - #1), slice.cap "b" - #1))).

    Axiom stringToBytes_t : ∅ ⊢ stringToBytes : (stringT -> slice.T byteT).
    Axiom bytesToString_t : ∅ ⊢ bytesToString : (slice.T byteT -> stringT).
    Definition randomUint64: val := λ: <>, #0.
    Theorem randomUint64_t: ∅ ⊢ randomUint64 : (unitT -> uint64T).
    Proof.
      typecheck.
    Qed.
  End goose_lang.
End Data.

Hint Resolve Data.stringToBytes_t Data.bytesToString_t : types.

Opaque Data.randomUint64.
Hint Resolve Data.randomUint64_t : types.

Module FS.
  Section goose_lang.
    Context {ext:ext_op}.
    Definition open: val := λ: <>, #().
    Definition close: val := λ: <>, #().
    Definition list: val := λ: <>, #().
    Definition size: val := λ: <>, #().
    Definition readAt: val := λ: <>, #().
    Definition create: val := λ: <>, #().
    Definition append: val := λ: <>, #().
    Definition delete: val := λ: <>, #().
    Definition rename: val := λ: <>, #().
    Definition truncate: val := λ: <>, #().
    Definition atomicCreate: val := λ: <>, #().
    Definition link: val := λ: <>, #().
  End goose_lang.
End FS.
Definition fileT {val_tys: val_types}: ty := unitT.

Module Globals.
  Section goose_lang.
    Context {ext:ext_op}.
    Definition getX: val := λ: <>, #().
    Definition setX: val := λ: <>, #().
  End goose_lang.
End Globals.
