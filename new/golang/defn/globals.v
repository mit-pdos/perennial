From New.golang.defn Require Export mem typing list.

Module globals.
Section defns.
Context `{ffi_syntax}.

Definition unwrap_def : val :=
  λ: "x", match: "x" with
            NONE => #() #()
          | SOME "x" => "x"
          end.
Program Definition unwrap := unseal (_:seal (@unwrap_def)). Obligation 1. by eexists. Qed.
Definition unwrap_unseal : unwrap = _ := seal_eq _.

Definition get_def : val :=
  λ: "pkg_name" "var_name",
    let: (("varAddrs", "functions"), "typeToMethodSets") := unwrap $ GlobalGet "pkg_name" in
    unwrap $ alist_lookup "var_name" "varAddrs".
Program Definition get := unseal (_:seal (@get_def)). Obligation 1. by eexists. Qed.
Definition get_unseal : get = _ := seal_eq _.

(* XXX: unsealed because user has to prove WPs for this by unfolding. *)
Definition alloc (vars : list (go_string * go_type)) : val :=
  λ: <>, (fix alloc (vars : list (go_string * go_type)) : expr :=
           (match vars with
            | Datatypes.nil => alist_val []
            | (pair name t) :: vars =>
                list.Cons (#name, ref_ty t (zero_val t)) (alloc vars)
            end)%E) vars
.

Definition package_init_def (pkg_name : go_string) vars functions msets : val :=
  let functions_val := alist_val functions in
  let msets_val := alist_val ((λ '(name, mset), (name, alist_val mset)) <$> msets) in
  λ: "init",
    match: GlobalGet #pkg_name with
      SOME <> => #()
    | NONE =>
        let: "var_addrs" := alloc vars #() in
        GlobalPut #pkg_name ("var_addrs", functions_val, msets_val) ;;
        "init" #()
    end.
Program Definition package_init := unseal (_:seal (@package_init_def)). Obligation 1. by eexists. Qed.
Definition package_init_unseal : package_init = _ := seal_eq _.

End defns.
End globals.

Section defns.
Context `{ffi_syntax}.

Definition func_call_def : val :=
  λ: "pkg_name" "func_name",
    let: (("varAddrs", "functions"), "typeToMethodSets") := globals.unwrap $ GlobalGet "pkg_name" in
    globals.unwrap $ alist_lookup "func_name" "functions".
Program Definition func_call := unseal (_:seal (@func_call_def)). Obligation 1. by eexists. Qed.
Definition func_call_unseal : func_call = _ := seal_eq _.

Definition method_call_def : val :=
  λ: "pkg_name" "type_name" "method_name",
    let: (("varAddrs", "functions"), "typeToMethodSets") := globals.unwrap $ GlobalGet "pkg_name" in
    let: "methodSet" := globals.unwrap $ alist_lookup "type_name" "typeToMethodSets" in
    globals.unwrap $ alist_lookup "method_name" "methodSet".
Program Definition method_call := unseal (_:seal (@method_call_def)). Obligation 1. by eexists. Qed.
Definition method_call_unseal : method_call = _ := seal_eq _.

End defns.
