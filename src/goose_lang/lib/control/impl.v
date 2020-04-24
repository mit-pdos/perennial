From Perennial.goose_lang Require Import lang notation.

Section goose_lang.
Context {ext: ext_op}.

Definition Assume: val :=
  λ: "cond", if: Var "cond" then #()
             else (rec: "loop" <> := Var "loop" #()) #().

End goose_lang.
