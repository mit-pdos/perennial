From Perennial.goose_lang Require Import notation.
From New.golang.defn Require Import typing.

(** [PkgInfo] associates a pkg_name to its static information. *)
Class PkgInfo (pkg_name: go_string) `{ffi_syntax} := {
    pkg_vars : list (go_string * go_type);
    pkg_functions : list (go_string * val);
    pkg_msets : list (go_string * (list (go_string * val)));
    pkg_imported_pkgs : list go_string;
  }.

Arguments pkg_vars (pkg_name) {_ _}.
Arguments pkg_functions (pkg_name) {_ _}.
Arguments pkg_msets (pkg_name) {_ _}.
Arguments pkg_imported_pkgs (pkg_name) {_ _}.
