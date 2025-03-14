(* autogenerated from strings *)
From New.golang Require Import defn.

Definition strings : go_string := "strings".

Module strings.
Section code.
Context `{ffi_syntax}.


Definition Builder : go_type := structT [
  "addr" :: ptrT;
  "buf" :: sliceT
].

Axiom asciiSpace'init : val.

Definition vars' : list (go_string * go_type) := [].

Definition functions' : list (go_string * val) := [].

Definition msets' : list (go_string * (list (go_string * val))) := [("Builder"%go, []); ("Builder'ptr"%go, [])].

#[global] Instance info' : PkgInfo strings.strings :=
  {|
    pkg_vars := vars';
    pkg_functions := functions';
    pkg_msets := msets';
    pkg_imported_pkgs := [];
  |}.

Axiom _'init : val.

Definition initialize' : val :=
  rec: "initialize'" <> :=
    globals.package_init strings.strings (λ: <>,
      exception_do (do:  (asciiSpace'init #()))
      ).

End code.
End strings.
