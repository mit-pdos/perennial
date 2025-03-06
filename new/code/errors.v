(* autogenerated from errors *)
From New.golang Require Import defn.

Module errors.
Section code.
Context `{ffi_syntax}.


Axiom ErrUnsupported'init : val.

Axiom errorType'init : val.

Definition pkg_name' : go_string := "errors".

Definition vars' : list (go_string * go_type) := [].

Definition functions' : list (go_string * val) := [].

Definition msets' : list (go_string * (list (go_string * val))) := [].

Definition info' : pkg_info.t := {|
             pkg_info.vars := vars';
             pkg_info.functions := functions';
             pkg_info.msets := msets';
             pkg_info.imported_pkgs := [];
           |}.

#[global] Instance  : PkgInfo pkg_name' info' :=
  {}.

Axiom _'init : val.

Definition initialize' : val :=
  rec: "initialize'" <> :=
    globals.package_init pkg_name' (λ: <>,
      exception_do (do:  (ErrUnsupported'init #());;;
      do:  (errorType'init #()))
      ).

End code.
End errors.
