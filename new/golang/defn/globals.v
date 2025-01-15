From New.golang.defn Require Export mem typing list.

Module globals.
Section defns.
Context `{ffi_syntax}.

Definition unwrap : val :=
  λ: "x", match: "x" with
            NONE => #() #()
          | SOME "x" => "x"
          end.

Definition get : val :=
  λ: "pkg_name" "var_name",
    let: (("varAddrs", "functions"), "typeToMethodSets") := unwrap $ GlobalGet (#"pkg:" + "pkg_name") in
    unwrap $ alist_lookup "var_name" "varAddrs".

Definition alloc_and_define
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

Definition func_call : val :=
  λ: "pkg_name" "func_name",
    let: (("varAddrs", "functions"), "typeToMethodSets") := globals.unwrap $ GlobalGet (#"pkg:" + "pkg_name") in
    globals.unwrap $ alist_lookup "func_name" "functions".

Definition method_call : val :=
  λ: "pkg_name" "type_name" "method_name",
    let: (("varAddrs", "functions"), "typeToMethodSets") := globals.unwrap $ GlobalGet (#"pkg:" + "pkg_name") in
    let: "methodSet" := globals.unwrap $ GlobalGet (#"type:" + "type_name") in
    globals.unwrap $ alist_lookup "method_name" "methodSet".

End defns.
