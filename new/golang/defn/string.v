From New.golang.defn Require Export loop assume predeclared.
From New.code.github_com.goose_lang.goose.model Require Import strings.

Module string.
Section defns.
Context {ext : ffi_syntax} {go_gctx : GoGlobalContext}.

Definition to_bytes : val :=
  λ: "s", FuncResolve strings.StringToByteSlice [] #() "s" #().

Definition from_bytes : val :=
  λ: "a", FuncResolve strings.ByteSliceToString [] #() "a" #().

End defns.
End string.
