From Perennial.goose_lang Require Import notation typing.

Definition timerRefT {ext} {ext_ty: ext_types ext} := refT (arrowT unitT unitT).

Module time.
  Section goose_lang.
    Context {ext:ffi_syntax}.

    Local Coercion Var' (s:string): expr := Var s.

    Definition Millisecond: val := #1000000.
    Definition Second: val := #1000000000.
    Definition Sleep: val := λ: "duration", #().
    Definition AfterFunc: val := λ: "duration" "f", Fork "f" ;; ref "f".
    Definition Timer__Reset: val := λ: "timer", !"timer" #(). (* FIXME: this could rerun f *)
  End goose_lang.
End time.
