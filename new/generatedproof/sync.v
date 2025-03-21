(* autogenerated by goose proofgen; do not modify *)
Require Export New.proof.proof_prelude.
Require Export New.manualproof.sync.
Require Export New.generatedproof.sync.atomic.
Require Export New.generatedproof.internal.race.
Require Export New.golang.theory.

Require Export New.code.sync.
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
    ]))%struct
    #(noCopy.mk).
Admitted.


End instances.
Module RWMutex.
Section def.
Context `{ffi_syntax}.
Axiom t : Type.
End def.
End RWMutex.

Global Instance into_val_RWMutex `{ffi_syntax} : IntoVal RWMutex.t.
Admitted.

Global Instance into_val_typed_RWMutex `{ffi_syntax} : IntoValTyped RWMutex.t sync.RWMutex.
Admitted.
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
    ]))%struct
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

Global Instance is_pkg_defined_instance : IsPkgDefined sync :=
{|
  is_pkg_defined := is_global_definitions sync var_addrs;
|}.

Definition own_allocated `{!GlobalAddrs} : iProp Σ :=
True.

Global Instance wp_func_call_NewCond :
  WpFuncCall sync "NewCond" _ (is_pkg_defined sync) :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_runtime_Semacquire :
  WpFuncCall sync "runtime_Semacquire" _ (is_pkg_defined sync) :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_runtime_SemacquireWaitGroup :
  WpFuncCall sync "runtime_SemacquireWaitGroup" _ (is_pkg_defined sync) :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_runtime_Semrelease :
  WpFuncCall sync "runtime_Semrelease" _ (is_pkg_defined sync) :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_method_call_Cond'ptr_Broadcast :
  WpMethodCall sync "Cond'ptr" "Broadcast" _ (is_pkg_defined sync) :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Cond'ptr_Signal :
  WpMethodCall sync "Cond'ptr" "Signal" _ (is_pkg_defined sync) :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Cond'ptr_Wait :
  WpMethodCall sync "Cond'ptr" "Wait" _ (is_pkg_defined sync) :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Mutex'ptr_Lock :
  WpMethodCall sync "Mutex'ptr" "Lock" _ (is_pkg_defined sync) :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Mutex'ptr_Unlock :
  WpMethodCall sync "Mutex'ptr" "Unlock" _ (is_pkg_defined sync) :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_WaitGroup'ptr_Add :
  WpMethodCall sync "WaitGroup'ptr" "Add" _ (is_pkg_defined sync) :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_WaitGroup'ptr_Done :
  WpMethodCall sync "WaitGroup'ptr" "Done" _ (is_pkg_defined sync) :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_WaitGroup'ptr_Wait :
  WpMethodCall sync "WaitGroup'ptr" "Wait" _ (is_pkg_defined sync) :=
  ltac:(apply wp_method_call'; reflexivity).

End names.
End sync.
