(* autogenerated from github.com/goose-lang/primitive/disk *)
From New.golang Require Import defn.

Require Export New.trusted_code.github_com.goose_lang.primitive.disk.
Import disk.
From New Require Import disk_prelude.
Module disk.
Section code.


Definition pkg_name' : go_string := "github.com/goose-lang/primitive/disk".

Definition vars' : list (go_string * go_type) := [].

Definition functions' : list (go_string * val) := [("Get"%go, Get); ("Read"%go, Read); ("Write"%go, Write); ("Size"%go, Size); ("Barrier"%go, Barrier)].

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
      exception_do (do:  (_'init #());;;
      do:  (_'init #()))
      ).

End code.
End disk.
