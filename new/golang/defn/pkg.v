From Perennial.goose_lang Require Import notation.
From New.golang.theory Require Import proofmode.

Module pkg_info.
Section defn.
  Context `{ffi_syntax}.
  Record t :=
    mk {
        vars : list (go_string * go_type);
        functions : list (go_string * val);
        msets : list (go_string * (list (go_string * val)));
        imported_pkgs : list go_string;
      }.
End defn.
End pkg_info.

(** [PkgInfo] associates a pkg_name to its static information. *)
Class PkgInfo (pkg_name: go_string) `{ffi_syntax} (info: pkg_info.t) := {}.

(* These are much like projection functions but get the [info] argument from a
pkg name (by looking it up via the PkgInfo class) *)

Definition pkg_info (pkg_name: go_string) `{PkgInfo pkg_name info} :=
  info.
Definition pkg_vars (pkg_name: go_string) `{PkgInfo pkg_name info} :=
  pkg_info.vars info.
Definition pkg_functions (pkg_name: go_string) `{PkgInfo pkg_name info} :=
  pkg_info.functions info.
Definition pkg_msets (pkg_name: go_string) `{PkgInfo pkg_name info} :=
  pkg_info.msets info.
Definition pkg_imported_pkgs (pkg_name: go_string) `{PkgInfo pkg_name info} :=
  pkg_info.imported_pkgs info.
