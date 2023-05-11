From Perennial.goose_lang Require Import notation typing.

Module rand.
  Section goose_lang.
    Context {ext:ffi_syntax}.

    Local Coercion Var' (s:string): expr := Var s.

    Definition RandomUint64: val := λ: <>, ArbitraryInt.
  End goose_lang.
End rand.
