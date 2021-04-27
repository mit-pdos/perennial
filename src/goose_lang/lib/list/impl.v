From Perennial.goose_lang Require Import lang notation.

Notation ListConsV hd tl := (InjRV (PairV hd tl)).
Notation ListNilV := (InjLV (LitV LitUnit)).
Notation ListCons hd tl := (InjR (Pair hd tl)).

Section goose_lang.
Context {ext:ffi_syntax}.
Local Coercion Var' (s:string) : expr := Var s.

Definition ListMatch : val :=
  λ: "l" "nilfun" "consfun",
  (match: "l" with
     InjL "nil" => "nilfun" #()
   | InjR "p" => "consfun" "p"
   end).

End goose_lang.
