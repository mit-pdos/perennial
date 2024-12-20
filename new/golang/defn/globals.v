From New.golang.defn Require Export mem typing.

Module globals.
Section defns.
Context `{ffi_syntax}.

Local Definition encode_var_name (pkg_name var_name : go_string) : go_string :=
  pkg_name ++ " "%go ++ var_name.

Definition get (x : go_string * go_string) : val :=
  λ: <>, match: GlobalGet #(encode_var_name x.1 x.2) with
            SOME "x" => "x"
          | NONE => #() #()
          end.

Definition put (x : go_string * go_string) : val :=
  λ: "y", GlobalPut #(encode_var_name x.1 x.2) "y".

Definition package_init (pkg_name : go_string) : val :=
  λ: "init",
    match: GlobalGet #pkg_name with
      SOME <> => #()
    | NONE => "init" #() ;; GlobalPut #pkg_name #()
    end.

End defns.
End globals.

Global Arguments globals.get {_} _%core_scope.
Global Arguments globals.put {_} _%core_scope.
