From Perennial.goose_lang Require Import lang slice notation typing.
From Perennial.goose_lang.lib Require Import control.impl.

Section goose_lang.
Context {ext:ffi_syntax}.
Context {ext_ty:ext_types ext}. (* need this to use slice *)

Definition StringFromBytes : val :=
  (rec: "StringFromBytes" "b" :=
     if: (slice.len "b") = #0
     then (Val #str "")
     else (to_string (SliceGet byteT "b" #0)) +
            ("StringFromBytes" (SliceSubslice byteT "b" #1 (slice.len "b")))).

Definition stringToBytes : val :=
  (rec: "stringToBytes" "i" "s" :=
     if: (Var "i") = #0
     then slice.nil
     else
       let: "j" := "i" - #1 in
       (SliceAppend byteT ("stringToBytes" "j" "s") (StringGet "s" "j")))
.

Definition StringToBytes : val :=
  λ: "s",
    Assume (IsNoStringOverflow "s") ;;
    stringToBytes (StringLength "s") "s"
.

End goose_lang.
