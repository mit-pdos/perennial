(* autogenerated by goose proofgen (types); do not modify *)
Require Export New.proof.proof_prelude.
Require Export New.manualproof.sync.
Require Export New.generatedproof.sync.atomic.
Require Export New.generatedproof.internal.race.
Require Export New.code.sync.
Require Export New.golang.theory.

Module sync.
Axiom falso : False.
Module noCopy.
Section def.
Context `{ffi_syntax}.
Record t := mk {
}.
End def.
End noCopy.

Section instances.
Context `{ffi_syntax}.
Global Instance into_val_noCopy `{ffi_syntax} : IntoVal noCopy.t.
Admitted.

Global Instance into_val_typed_noCopy `{ffi_syntax} : IntoValTyped noCopy.t sync.noCopy :=
{|
  default_val := noCopy.mk;
  to_val_has_go_type := ltac:(destruct falso);
  default_val_eq_zero_val := ltac:(destruct falso);
  to_val_inj := ltac:(destruct falso);
  to_val_eqdec := ltac:(solve_decision);
|}.

Context `{!ffi_model, !ffi_semantics _ _, !ffi_interp _, !heapGS Σ}.
Global Instance wp_struct_make_noCopy `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}:
  PureWp True
    (struct.make sync.noCopy (alist_val [
    ]))%V
    #(noCopy.mk).
Admitted.


End instances.
Module WaitGroup.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  noCopy' : noCopy.t;
  state' : atomic.Uint64.t;
  sema' : w32;
}.
End def.
End WaitGroup.

Section instances.
Context `{ffi_syntax}.

Global Instance settable_WaitGroup `{ffi_syntax}: Settable _ :=
  settable! WaitGroup.mk < WaitGroup.noCopy'; WaitGroup.state'; WaitGroup.sema' >.
Global Instance into_val_WaitGroup `{ffi_syntax} : IntoVal WaitGroup.t.
Admitted.

Global Instance into_val_typed_WaitGroup `{ffi_syntax} : IntoValTyped WaitGroup.t sync.WaitGroup :=
{|
  default_val := WaitGroup.mk (default_val _) (default_val _) (default_val _);
  to_val_has_go_type := ltac:(destruct falso);
  default_val_eq_zero_val := ltac:(destruct falso);
  to_val_inj := ltac:(destruct falso);
  to_val_eqdec := ltac:(solve_decision);
|}.
Global Instance into_val_struct_field_WaitGroup_noCopy `{ffi_syntax} : IntoValStructField "noCopy" sync.WaitGroup WaitGroup.noCopy'.
Admitted.

Global Instance into_val_struct_field_WaitGroup_state `{ffi_syntax} : IntoValStructField "state" sync.WaitGroup WaitGroup.state'.
Admitted.

Global Instance into_val_struct_field_WaitGroup_sema `{ffi_syntax} : IntoValStructField "sema" sync.WaitGroup WaitGroup.sema'.
Admitted.


Context `{!ffi_model, !ffi_semantics _ _, !ffi_interp _, !heapGS Σ}.
Global Instance wp_struct_make_WaitGroup `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} noCopy' state' sema':
  PureWp True
    (struct.make sync.WaitGroup (alist_val [
      "noCopy" ::= #noCopy';
      "state" ::= #state';
      "sema" ::= #sema'
    ]))%V
    #(WaitGroup.mk noCopy' state' sema').
Admitted.


Global Instance WaitGroup_struct_fields_split dq l (v : WaitGroup.t) :
  StructFieldsSplit dq l v (
    "HnoCopy" ∷ l ↦s[sync.WaitGroup :: "noCopy"]{dq} v.(WaitGroup.noCopy') ∗
    "Hstate" ∷ l ↦s[sync.WaitGroup :: "state"]{dq} v.(WaitGroup.state') ∗
    "Hsema" ∷ l ↦s[sync.WaitGroup :: "sema"]{dq} v.(WaitGroup.sema')
  ).
Admitted.

End instances.

Section names.

Class GlobalAddrs :=
{
}.

Context `{!GlobalAddrs}.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!goGlobalsGS Σ}.

Definition var_addrs : list (go_string * loc) := [
  ].

Definition is_defined := is_global_definitions sync.pkg_name' var_addrs sync.functions' sync.msets'.

Global Instance : PkgIsDefined sync.pkg_name' is_defined :=
  ltac:(prove_pkg_is_defined).

Definition own_allocated `{!GlobalAddrs} : iProp Σ :=
True.

Global Instance wp_func_call_NewCond :
  WpFuncCall sync.pkg_name' "NewCond" _ (is_pkg_defined sync.pkg_name') :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_runtime_Semacquire :
  WpFuncCall sync.pkg_name' "runtime_Semacquire" _ (is_pkg_defined sync.pkg_name') :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_runtime_SemacquireWaitGroup :
  WpFuncCall sync.pkg_name' "runtime_SemacquireWaitGroup" _ (is_pkg_defined sync.pkg_name') :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_runtime_Semrelease :
  WpFuncCall sync.pkg_name' "runtime_Semrelease" _ (is_pkg_defined sync.pkg_name') :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_method_call_Cond'ptr_Broadcast :
  WpMethodCall sync.pkg_name' "Cond'ptr" "Broadcast" _ (is_pkg_defined sync.pkg_name') :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Cond'ptr_Signal :
  WpMethodCall sync.pkg_name' "Cond'ptr" "Signal" _ (is_pkg_defined sync.pkg_name') :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Cond'ptr_Wait :
  WpMethodCall sync.pkg_name' "Cond'ptr" "Wait" _ (is_pkg_defined sync.pkg_name') :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Mutex'ptr_Lock :
  WpMethodCall sync.pkg_name' "Mutex'ptr" "Lock" _ (is_pkg_defined sync.pkg_name') :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Mutex'ptr_Unlock :
  WpMethodCall sync.pkg_name' "Mutex'ptr" "Unlock" _ (is_pkg_defined sync.pkg_name') :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_WaitGroup'ptr_Add :
  WpMethodCall sync.pkg_name' "WaitGroup'ptr" "Add" _ (is_pkg_defined sync.pkg_name') :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_WaitGroup'ptr_Done :
  WpMethodCall sync.pkg_name' "WaitGroup'ptr" "Done" _ (is_pkg_defined sync.pkg_name') :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_WaitGroup'ptr_Wait :
  WpMethodCall sync.pkg_name' "WaitGroup'ptr" "Wait" _ (is_pkg_defined sync.pkg_name') :=
  ltac:(apply wp_method_call'; reflexivity).

End names.
End sync.
