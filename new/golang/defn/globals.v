From New.golang.defn Require Import mem typing list pkg assume.
From Perennial Require Import base.

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

(* Allocates variables *just* for a single package. Unsealed because user proves
   WPs for this by unfolding. *)
Definition alloc (vars : list (go_string * go_type)) : val :=
  λ: <>, (fix alloc (vars : list (go_string * go_type)) : expr :=
           (match vars with
            | Datatypes.nil => #()
            | (pair name t) :: vars =>
                let: "addr" := mem.alloc (zero_val t) in
                assume (get #name = "addr")
            end)%E) vars.

End defns.
End globals.

Module package.
Section defns.
Context `{ffi_syntax}.

Definition init_def (pkg_name : go_string) : val :=
  λ: "init", match: GlobalGet #pkg_name with
               SOME <> => #()
             | NONE => "init" #()
             end.
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
