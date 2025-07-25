(* autogenerated from testing *)
From New.golang Require Import defn.

Definition testing : go_string := "testing".

Module testing.
Section code.
Context `{ffi_syntax}.


Axiom benchTime'init : val.

Axiom hideStdoutForTesting'init : val.

Axiom minimizeDuration'init : val.

Axiom corpusDir'init : val.

Axiom supportedTypes'init : val.

Axiom testBinary'init : val.

Axiom T : go_type.

Axiom errNilPanicOrGoexit'init : val.

Axiom errMain'init : val.

Definition vars' : list (go_string * go_type) := [].

Definition functions' : list (go_string * val) := [].

Definition msets' : list (go_string * (list (go_string * val))) := [("T"%go, []); ("T'ptr"%go, [])].

#[global] Instance info' : PkgInfo testing.testing :=
  {|
    pkg_vars := vars';
    pkg_functions := functions';
    pkg_msets := msets';
    pkg_imported_pkgs := [];
  |}.

Axiom _'init : val.

Definition initialize' : val :=
  rec: "initialize'" <> :=
    globals.package_init testing.testing (λ: <>,
      exception_do (do:  (benchTime'init #());;;
      do:  (hideStdoutForTesting'init #());;;
      do:  (minimizeDuration'init #());;;
      do:  (corpusDir'init #());;;
      do:  (_'init #());;;
      do:  (supportedTypes'init #());;;
      do:  (testBinary'init #());;;
      do:  (_'init #());;;
      do:  (_'init #());;;
      do:  (errNilPanicOrGoexit'init #());;;
      do:  (errMain'init #()))
      ).

End code.
End testing.
