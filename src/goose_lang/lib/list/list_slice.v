From Perennial.goose_lang Require Import lang notation.
From Perennial.goose_lang.lib Require Import typed_mem.impl.
From Perennial.goose_lang Require Import slice.impl list.impl.

Section goose_lang.
Context `{ffi_sem: ext_semantics}.
Context {ext_ty:ext_types ext}.
Local Coercion Var' (s:string) : expr := Var s.

Definition SliceToList t : val :=
  λ: "s",
  let: "len" := slice.len "s" in
  (rec: "loop" "i" :=
       if: ("i" < "len") then
         let: "x" := SliceGet t "s" "i" in
         ListCons "x" ("loop" ("i" + #1))
       else ListNilV) #0.

Definition ListToSlice t : val :=
  λ: "l",
  (rec: "loop" "l" "s" :=
     ListMatch "l"
               (λ: "x", "s")
               (λ: "p", "loop" (Snd "p") (SliceAppend t "s" (Fst "p")))).

End goose_lang.
