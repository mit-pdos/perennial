From New.golang.defn Require Export mem typing list.

Module globals.
Section defns.
Context `{ffi_syntax}.

Definition unwrap : val :=
  λ: "x", match: "x" with
            NONE => #() #()
          | SOME "x" => "x"
          end.

Definition get (pkg_var_name : (go_string * go_string)): val :=
  λ: <>,
    let: (("varAddrs", "functions"), "typeToMethodSets") := unwrap $ GlobalGet #("pkg:" ++ pkg_var_name.1) in
    unwrap $ alist_lookup #(pkg_var_name.2) "varAddrs".

Fixpoint alloc_and_define
  (pkg_name : go_string)
  (vars : list (go_string * go_type))
  (functions : list (go_string * val))
  (msets : list (go_string * (list (go_string * val)))) : val :=
  let functions_val := alist_val functions in
  let msets_val := alist_val ((λ '(name, mset), (name, alist_val mset)) <$> msets) in
  λ: <>,
    GlobalPut #pkg_name ((fix alloc (vars : list (go_string * go_type)) : expr :=
        (match vars with
         | Datatypes.nil => list.Nil
         | (pair name t) :: vars =>
             let: "addr" := ref_ty t (zero_val t) in
             list.Cons (#name, "addr") (alloc vars)
         end)%E) vars, functions_val, msets_val)
.

Definition package_init (pkg_name : go_string) vars functions msets : val :=
  λ: "init",
    match: GlobalGet #("pkg:" ++ pkg_name) with
      SOME <> => #()
    | NONE => alloc_and_define pkg_name vars functions msets #() ;;
             "init" #()
    end.

End defns.
End globals.

Section defns.
Context `{ffi_syntax}.

Definition func_call (pkg_func_name : go_string * go_string) : val :=
  λ: <>,
    let: (("varAddrs", "functions"), "typeToMethodSets") := globals.unwrap $ GlobalGet #("pkg:" ++ pkg_func_name.1) in
    globals.unwrap $ alist_lookup #(pkg_func_name.2) "functions".

Definition method_call (pkg_type_method_name : go_string * go_string * go_string) : val :=
  λ: <>,
    let pkg_name := pkg_type_method_name.1.1 in
    let type_name := pkg_type_method_name.1.2 in
    let method_name := pkg_type_method_name.2 in
    let: (("varAddrs", "functions"), "typeToMethodSets") := globals.unwrap $ GlobalGet #("pkg:" ++ pkg_name) in
    let: "methodSet" := globals.unwrap $ GlobalGet #("type:" ++ type_name) in
    globals.unwrap $ alist_lookup #method_name "methodSet".

End defns.

Global Arguments globals.get {_} (_)%go.
