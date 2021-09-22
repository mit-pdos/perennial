From Perennial.goose_lang Require Import lang notation typing.
From Perennial.goose_lang.lib Require Import typed_mem.impl.
From Perennial.goose_lang Require Import slice.impl list.impl.

Section goose_lang.
Context `{ffi_sem: ffi_semantics}.
Context {ext_ty:ext_types ext}.
Local Coercion Var' (s:string) : expr := Var s.

Definition SliceToListFrom t : val :=
  rec: "loop" "s" "i" :=
    let: "len" := slice.len "s" in
    if: ("i" < "len") then
      let: "x" := SliceGet t "s" "i" in
      ListCons "x" ("loop" "s" ("i" + #1))
    else ListNilV.

Definition SliceToList t : val :=
  λ: "s",
    SliceToListFrom t "s" #0%nat.

Definition ListToSliceApp t : val :=
  rec: "loop" "l" "s" :=
    ListMatch "l"
      (λ: "x", "s")
      (λ: "p",
        "loop" (Snd "p") (SliceAppend t "s" (Fst "p"))
      ).

Definition ListToSlice t : val :=
  λ: "l",
    ListToSliceApp t "l" (NewSlice t #0).

End goose_lang.
