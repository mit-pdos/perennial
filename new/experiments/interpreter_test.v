From Perennial.goose_lang Require Import prelude.
(* From Perennial.goose_lang Require Import ffi.disk_prelude. *)
From Perennial.goose_lang.interpreter Require Import test_config.

(* test functions *)
From New.code.github_com.goose_lang.goose.testdata.examples Require Import semantics.

Create HintDb golang_unseal.

From New.golang Require Import defn.
Hint Rewrite
  globals.package_init_unseal
  exception_do_unseal
  exception_seq_unseal
  do_execute_unseal
  to_val_unseal
  alist_val_unseal
  : golang_unseal.

Hint Unfold
  globals.globals.package_init_def
  : golang_unseal.

Definition initialize' : val :=
  (rec: "initialize'" <> :=
    globals.package_init semantics.semantics
     #()).

(* FIXME: evaluation gets stuck with this. *)
    (* globals.package_init semantics.semantics
      (λ: <>, #()))%V. *)

(* allocator.go *)
Example testAllocateDistinct_ok :
  (initialize' #()) ~~> #true.
apply do_test.
unfold initialize'.
(* FIXME: things inside of other functions won't get unsealed here. *)
repeat (autorewrite with golang_unseal || autounfold with golang_unseal).
unfold run.
pose proof (x := O).
replace 1000%nat with (S x)%nat by admit.
unfold semantics.
unfold globals.alloc.
rewrite list.Cons_unseal.
rewrite ref_ty_unseal.
rewrite zero_val_unseal.
unfold pkg_vars.
rewrite to_val_unseal.
unfold to_val_def.
autorewrite with golang_unseal.
simpl.
autorewrite with golang_unseal.
progress simpl.
replace x with (S x)%nat by admit.
(* XXX can't do any more here. *)
progress simpl.
progress autorewrite with golang_unseal.
progress simpl.

progress vm_compute.
progress autorewrite with golang_unseal.
vm_compute.
rewrite MapConsV

(* FIXME: too late to unseal now, but too early to unseal before *)
autorewrite with golang_unseal.
vm_compute.
unfold interpreter.interpret.
rewrite globals.globals.package_init_unseal.
vm_compute.
unfold semantics.testAll
vm_compute.
rewrite /run runStateT.
unfold semantics.testAllocateDistinct.
simpl.
