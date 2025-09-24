From New.golang.defn Require Import mem list assume typing.
From Perennial Require Import base.

(** [GoContext] contains the immutable global state of a node running Go code.
    It is a typeclass so that [global_addr] can be conveniently used in proofs
    that have a section variable of type [GoContext]. A new [global_addr] is
    (angelically) nondeterministically chosen on reboot. This choice is angelic
    in the sense that future code (package.alloc) will actually allocate on the
    heap and angelically assumes that the allocated location matches the
    [global_addr] map.

    This also contains `to_mem_type`, which is not actually global state as far
    as execution semantics are concerned. Instead, this serves as the
    interaction point by which package A can define a generic function that
    takes in any type `T`, and package B can define the relationship between
    `T.id : go_string` and `T : go_type` and know that `A` generic function has
    been monomorphized so that `T.id` connects to `T : go_type`. I.e. the
    `to_mem_type` makes it easier to state local assumptions about the other maps
    (like the __functions map) that allow for types in one package to be used
    with generic functions/methods in another package.
 *)
Class GoContext {ext : ffi_syntax} :=
  {
    global_addr_def : go_string → loc;
    __function : go_string → option val;
    __method : go_string → go_string → option val;
    to_mem_type : go_string → go_type;
  }.

(** [PkgInfo] associates a pkg_name to its static information. *)
Class PkgInfo (pkg_name: go_string) `{ffi_syntax} := {
    pkg_vars : list (go_string * go_type);
    pkg_functions : go_string → option val;
    pkg_msets : go_string → option (list (go_string * val));
    pkg_imported_pkgs : list go_string;
  }.

Arguments pkg_vars (pkg_name) {_ _}.
Arguments pkg_functions (pkg_name) {_ _}.
Arguments pkg_msets (pkg_name) {_ _}.
Arguments pkg_imported_pkgs (pkg_name) {_ _}.

Module option.
Section defns.
Context `{ffi_syntax}.

Definition unwrap_def : val :=
  λ: "x", match: "x" with
            NONE => #() #()
          | SOME "x" => "x"
          end.
Program Definition unwrap := sealed @unwrap_def.
Definition unwrap_unseal : unwrap = _ := seal_eq _.

End defns.
End option.

Module globals.
Section defns.
Context `{ffi_syntax}.

Definition get_def : val :=
  λ: "var_name", (option.unwrap $ GlobalGet (#"V" + "var_name")).
Program Definition get := sealed @get_def.
Definition get_unseal : get = _ := seal_eq _.

End defns.
End globals.

Module package.
Section defns.
Context `{ffi_syntax}.

(** Allocates variables *just* for a single package. Unsealed because user
   proves WPs for this by unfolding. See the comment in [theory/pkg.v] to
   understand the call to [assume]. *)
Definition alloc pkg_name `{!PkgInfo pkg_name} : val :=
  λ: <>, (fix alloc (vars : list (go_string * go_type)) : expr :=
           (match vars with
            | Datatypes.nil => #()
            | (pair name t) :: vars =>
                let: "addr" := mem.alloc t (zero_val t) in
                assume (globals.get #name = "addr");;
                alloc vars
            end)%E) (pkg_vars pkg_name).

Local Definition check_status (pkg_name : go_string) : val :=
  λ: <>, match: GlobalGet #("P" ++ pkg_name)%go with
      SOME "status" => "status" = #"done"
    | NONE => #false
    end.

Local Definition try_start_initialization (pkg_name : go_string) : val :=
  λ: <>, match: GlobalGet #("P" ++ pkg_name)%go with
      SOME "status" => assume ("status" ≠ #"started");; #false
    | NONE => GlobalPut #("P" ++ pkg_name) #"started";; #true
    end.

Local Definition mark_initialized (pkg_name : go_string) : val :=
  λ: <>, GlobalPut #("P" ++ pkg_name) #"initialized".

Definition init_def (pkg_name : go_string) (init_fn : val) : val :=
  λ: <>,
    if: try_start_initialization pkg_name #() then
      init_fn #();; mark_initialized pkg_name #()
    else #().
Program Definition init := sealed @init_def.
Definition init_unseal : init = _ := seal_eq _.
End defns.
End package.

Section defns.
Context `{ffi_syntax}.

Definition func_call_def : val :=
  λ: "func_name",
    (λ: "firstArg",
       (option.unwrap $ GlobalGet (#"F" + "func_name")) "firstArg").
Program Definition func_call := sealed @func_call_def.
Definition func_call_unseal : func_call = _ := seal_eq _.

Definition method_call_def : val :=
  λ: "type_id" "method_name" "receiver",
    λ: "firstArg",
       let: "method_set" := option.unwrap $ GlobalGet (#"M" + "type_id") in
       (option.unwrap $ alist_lookup "method_name" "method_set") "receiver" "firstArg"
    .
Program Definition method_call := sealed @method_call_def.
Definition method_call_unseal : method_call = _ := seal_eq _.

End defns.
