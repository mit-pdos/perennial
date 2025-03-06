(* autogenerated from github.com/mit-pdos/gokv/kv *)
From New.golang Require Import defn.

Module kv.
Section code.
Context `{ffi_syntax}.


Definition Kv : go_type := interfaceT.

Definition KvCput : go_type := interfaceT.

Definition pkg_name' : go_string := "github.com/mit-pdos/gokv/kv".

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

Definition initialize' : val :=
  rec: "initialize'" <> :=
    globals.package_init pkg_name' (λ: <>,
      exception_do (do:  #())
      ).

End code.
End kv.
