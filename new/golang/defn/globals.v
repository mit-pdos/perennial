From New.golang.defn Require Export mem typing list.
From New.golang.defn Require Import hex.

Module globals.
Section defns.
Context `{ffi_syntax}.

Definition get (pkg_var_name : (go_string * go_string)): val :=
  λ: <>,
    match: GlobalGet #("vars:" ++ pkg_var_name.1) with
      NONE => #() #()
    | SOME "globalVarAddrs" => alist_lookup #(pkg_var_name.2) "globalVarAddrs"
    end.

Fixpoint alloc (vars : list (go_string * go_type)) : val :=
  (λ: <>,
    match vars with
    | Datatypes.nil => #()
    | (pair name t) :: vars =>
        let: "addr" := ref_ty t (zero_val t) in
        list.Cons (#name, "addr") (alloc vars)
    end)%V.

Definition package_init (pkg_name : go_string) (vars : list (go_string * go_type)) : val :=
  λ: "init",
    match: GlobalGet #("pkg:" ++ pkg_name) with
      SOME <> => #()
    | NONE => alloc vars #() ;; "init" #() ;; GlobalPut #("pkg:" ++ pkg_name) #()
    end.

End defns.
End globals.

Section defns.
Context `{ffi_syntax}.

Definition func_call (pkg_func_name : go_string * go_string) : val :=
  λ: <>,
    match: GlobalGet #("funcs:" ++ pkg_func_name.1) with
      NONE => #() #()
    | SOME "funcs" => alist_lookup #(pkg_func_name.2) "funcs"
    end.

Definition method_call (pkg_type_method_name : go_string * go_string * go_string) : val :=
  λ: <>,
    let pkg_name := pkg_type_method_name.1.1 in
    let type_name := pkg_type_method_name.1.2 in
    let method_name := pkg_type_method_name.2 in
    match: GlobalGet #("type:" ++ type_name) with
      NONE => #() #()
    | SOME "typeToMethodSet" =>
        let: "methodSet" := (alist_lookup #type_name "globalVarAddrs") in
        alist_lookup #method_name "methodSet"
    end.

End defns.

Global Arguments globals.get {_} (_)%go.
