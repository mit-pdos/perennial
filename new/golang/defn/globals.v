From New.golang.defn Require Import mem typing list pkg.
From Perennial Require Import base.

Module globals.
Section defns.
Context `{ffi_syntax}.

Definition unwrap_def : val :=
  λ: "x", match: "x" with
            NONE => #() #()
          | SOME "x" => "x"
          end.
Program Definition unwrap := sealed @unwrap_def.
Definition unwrap_unseal : unwrap = _ := seal_eq _.

Definition get_def : val :=
  λ: "pkg_name" "var_name",
    let: (("varAddrs", "functions"), "typeToMethodSets") := unwrap $ GlobalGet "pkg_name" in
    unwrap $ alist_lookup "var_name" "varAddrs".
Program Definition get := sealed @get_def.
Definition get_unseal : get = _ := seal_eq _.

(* XXX: unsealed because user has to prove WPs for this by unfolding. *)
Definition alloc (vars : list (go_string * go_type)) : val :=
  λ: <>, (fix alloc (vars : list (go_string * go_type)) : expr :=
           (match vars with
            | Datatypes.nil => alist_val []
            | (pair name t) :: vars =>
                list.Cons (#name, mem.alloc (zero_val t)) (alloc vars)
            end)%E) vars
.

Definition package_init_def (pkg_name : go_string) `{!PkgInfo pkg_name} : val :=
  let functions_val := alist_val (pkg_functions pkg_name) in
  let msets_val := alist_val ((λ '(name, mset), (name, alist_val mset)) <$> (pkg_msets pkg_name)) in
  λ: "init",
    match: GlobalGet #pkg_name with
      SOME <> => #()
    | NONE =>
        let: "var_addrs" := alloc (pkg_vars pkg_name) #() in
        GlobalPut #pkg_name ("var_addrs", functions_val, msets_val) ;;
        "init" #()
    end.
Program Definition package_init := sealed @package_init_def.
Definition package_init_unseal : package_init = _ := seal_eq _.
#[global]
Arguments package_init pkg_name {PkgInfo0}.

End defns.
End globals.

Section defns.
Context `{ffi_syntax}.

Definition func_call_def : val :=
  λ: "pkg_name" "func_name",
    (λ: "firstArg",
    let: (("varAddrs", "functions"), "typeToMethodSets") := globals.unwrap $ GlobalGet "pkg_name" in
    (globals.unwrap $ alist_lookup "func_name" "functions") "firstArg").
Program Definition func_call := sealed @func_call_def.
Definition func_call_unseal : func_call = _ := seal_eq _.

Definition method_call_def : val :=
  λ: "pkg_name" "type_name" "method_name" "receiver",
    (λ: "firstArg",
       let: (("varAddrs", "functions"), "typeToMethodSets") := globals.unwrap $ GlobalGet "pkg_name" in
       let: "methodSet" := globals.unwrap $ alist_lookup "type_name" "typeToMethodSets" in
       (globals.unwrap $ alist_lookup "method_name" "methodSet") "receiver" "firstArg"
    ).
Program Definition method_call := sealed @method_call_def.
Definition method_call_unseal : method_call = _ := seal_eq _.

End defns.
