From New.golang.defn Require Export postlang.

(** [PkgInfo] associates a pkg_name to its static information *)
Class PkgInfo (pkg_name: go_string) `{ffi_syntax} :=
  {
    pkg_imported_pkgs : list go_string;
  }.

Arguments pkg_imported_pkgs (pkg_name) {_ _}.

Module package.
Section defns.
Context {ext : ffi_syntax}.
Context {go_lctx : GoLocalContext} {go_gctx : GoGlobalContext}.

Definition init_def (pkg_name : go_string) : val :=
  λ: "init",
    if: PackageInitCheck pkg_name #() then #()
    else PackageInitStart pkg_name #();; "init" #();; PackageInitFinish pkg_name #().
Program Definition init := sealed @init_def.
Definition init_unseal : init = _ := seal_eq _.
End defns.
End package.
