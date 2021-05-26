From Perennial.goose_lang Require Export notation typing.

Module barrier.
  Section goose_lang.
    Context {ext:ffi_syntax}.
    Local Coercion Var' (s:string): expr := Var s.
    Definition newbarrier : val := λ: <>, ref #false.
    Definition signal : val := λ: "x", CAS "x" #false #true.
    Definition wait : val :=
      rec: "wait" "x" := if: !"x" then #() else "wait" "x".
  End goose_lang.
End barrier.
