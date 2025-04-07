(* These are the minimal dependencies needed for models implemented in 
Goose compatible Go i.e. the channel model. *)
From Perennial.goose_lang Require Export lang notation typing.
From Perennial.goose_lang.lib Require Export
     typed_mem.impl struct.impl loop.impl
     encoding.impl map.impl slice.impl lock.impl
     time.impl rand.impl proph.impl waitgroup.impl
     string.impl atomic.impl rwlock.impl.

(* We provide stubs here for primitive operations to make the Goose unit tests
   compile. *)

Open Scope heap_types.
Open Scope struct_scope.

(* TODO: replace all of these stubs with real operations *)
Definition uint64_to_string {ext: ffi_syntax}: val := λ: <>, #().

Module FS.
  Section goose_lang.
    Context {ext:ffi_syntax}.
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

(*
Module Globals.
  Section goose_lang.
    Context {ext:ffi_syntax}.
    Definition getX: val := λ: <>, #().
    Definition setX: val := λ: <>, #().
  End goose_lang.
End Globals.
*)
