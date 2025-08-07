From New.golang.defn Require Import mem typing list assume.
From Perennial Require Import base.

(** [PkgInfo] associates a pkg_name to its static information. *)
Class PkgInfo (pkg_name: go_string) `{ffi_syntax} := {
    pkg_vars : list (go_string * go_type);
    pkg_functions : list (go_string * val);
    pkg_msets : list (go_string * (list (go_string * val)));
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
  λ: "var_name", match: alist_lookup "var_name" (option.unwrap $ GlobalGet #"__global_vars") with
                   NONE => #null
                 | SOME "v" => "v"
                 end .
Program Definition get := sealed @get_def.
Definition get_unseal : get = _ := seal_eq _.

End defns.
End globals.

Module package.
Section defns.
Context `{ffi_syntax}.

(* Allocates variables *just* for a single package. Unsealed because user proves
   WPs for this by unfolding. *)
Definition alloc pkg_name `{!PkgInfo pkg_name} : val :=
  λ: <>, (fix alloc (vars : list (go_string * go_type)) : expr :=
           (match vars with
            | Datatypes.nil => #()
            | (pair name t) :: vars =>
                let: "addr" := mem.alloc (zero_val t) in
                assume (globals.get #name = "addr")
            end)%E) (pkg_vars pkg_name).

Local Definition check_status (pkg_name : go_string) : val :=
  λ: <>, match: GlobalGet #"__packages" with
      SOME "initmap" =>
        match: (alist_lookup #pkg_name "initmap") with
          SOME "status" => "status" = #"done"
        | NONE => #false
        end
    | NONE => #false
    end.

Local Definition try_start_initialization : val :=
  λ: "pkg_name",
    let: "initmap" := option.unwrap $ GlobalGet #"__packages" in
    let: "status" := (alist_lookup "pkg_name" "initmap") in
    match: "status" with
      SOME "s" =>
          assume ("s" ≠ #"started");;
          #false
    | NONE =>
      GlobalPut #"__packages" (list.Cons ("pkg_name", #"started") "initmap");;
      #true
    end.

Local Definition mark_initialized (pkg_name : go_string) : val :=
  λ: <>,
    let: "initmap" := option.unwrap $ GlobalGet #"__packages" in
    GlobalPut #"__packages" (list.Cons (#pkg_name, #"initialized") "initmap").

Definition init_def : val :=
  λ: "pkg_name" "init",
    if: try_start_initialization "pkg_name" then
      "init" #();; mark_initialized "pkg_name"
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
       (option.unwrap $ alist_lookup "func_name" (option.unwrap $ GlobalGet #"__functions")) "firstArg").
Program Definition func_call := sealed @func_call_def.
Definition func_call_unseal : func_call = _ := seal_eq _.

Definition method_call_def : val :=
  λ: "type_id" "method_name" "receiver",
    λ: "firstArg",
       let: "method_set" := option.unwrap $ alist_lookup "type_id" (option.unwrap $ GlobalGet #"__msets") in
       (option.unwrap $ alist_lookup "method_name" "method_set") "receiver" "firstArg"
    .
Program Definition method_call := sealed @method_call_def.
Definition method_call_unseal : method_call = _ := seal_eq _.

End defns.
