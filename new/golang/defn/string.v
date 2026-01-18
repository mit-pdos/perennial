From New.golang.defn Require Export loop assume predeclared.
From New.code.github_com.goose_lang.goose.model Require Import strings.

Module go.
Section defs.
Context {ext : ffi_syntax}.
Context {go_lctx : GoLocalContext} {go_gctx : GoGlobalContext}.

Class StringSemantics `{!GoSemanticsFunctions} :=
{
  (* FIXME: convert semantics *)
  #[global] package_sem :: strings.Assumptions;
}.
End defs.
End go.
