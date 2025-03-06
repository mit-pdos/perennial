(* autogenerated from github.com/mit-pdos/gokv/globals_test *)
From New.golang Require Import defn.

Module main.
Section code.
Context `{ffi_syntax}.


(* go: globals.go:3:6 *)
Definition foo : val :=
  rec: "foo" <> :=
    exception_do (return: (#(W64 10))).

Definition pkg_name' : go_string := "github.com/mit-pdos/gokv/globals_test".

(* go: globals.go:12:6 *)
Definition other : val :=
  rec: "other" <> :=
    exception_do (let: "$r0" := #"ok"%go in
    do:  ((globals.get #pkg_name' #"globalY"%go) <-[stringT] "$r0")).

(* go: globals.go:16:6 *)
Definition bar : val :=
  rec: "bar" <> :=
    exception_do (do:  ((func_call #pkg_name' #"other"%go) #());;;
    (if: ((![uint64T] (globals.get #pkg_name' #"GlobalX"%go)) ≠ #(W64 10)) || ((![stringT] (globals.get #pkg_name' #"globalY"%go)) ≠ #"ok"%go)
    then
      do:  (let: "$a0" := (interface.make #""%go #"string"%go #"bad"%go) in
      Panic "$a0")
    else do:  #())).

(* go: globals.go:31:6 *)
Definition main : val :=
  rec: "main" <> :=
    exception_do (do:  ((func_call #pkg_name' #"bar"%go) #())).

Definition vars' : list (go_string * go_type) := [("GlobalX"%go, uint64T); ("globalY"%go, stringT); ("globalA"%go, stringT); ("globalB"%go, stringT)].

Definition functions' : list (go_string * val) := [("foo"%go, foo); ("other"%go, other); ("bar"%go, bar); ("main"%go, main)].

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
      exception_do (let: "$r0" := ((func_call #pkg_name' #"foo"%go) #()) in
      do:  ((globals.get #pkg_name' #"GlobalX"%go) <-[uint64T] "$r0");;;
      let: "$r0" := #"a"%go in
      do:  ((globals.get #pkg_name' #"globalA"%go) <-[stringT] "$r0");;;
      let: "$r0" := #"b"%go in
      do:  ((globals.get #pkg_name' #"globalB"%go) <-[stringT] "$r0");;;
      do:  ((λ: <>,
        exception_do (let: "$r0" := ((![uint64T] (globals.get #pkg_name' #"GlobalX"%go)) + #(W64 0)) in
        do:  ((globals.get #pkg_name' #"GlobalX"%go) <-[uint64T] "$r0"))
        ) #());;;
      do:  ((λ: <>,
        exception_do (let: "$r0" := #""%go in
        do:  ((globals.get #pkg_name' #"globalY"%go) <-[stringT] "$r0"))
        ) #()))
      ).

End code.
End main.
