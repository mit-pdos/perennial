From Perennial.goose_lang Require Import lang slice notation typing.

Section goose_lang.
Context {ext:ffi_syntax}.
Context {ext_ty:ext_types ext}. (* need this to use slice *)
Local Coercion Var' (s:string) : expr := Var s.

Definition StringFromBytes : val :=
  (rec: "StringFromBytes" "b" :=
     if: (slice.len "b") = #0
     then (Val #str "")
     else (to_string (SliceGet byteT "b" #0)) +
            ("StringFromBytes" (SliceSubslice byteT "b" #1 (slice.len "b")))).

Definition StringToBytes : val :=
  (rec: "stringToBytes" "b" :=
     if: (StringLength "b") = #0
     then slice.nil
     else (SliceAppend byteT (SliceGet byteT "b" #0)) +
            ("bytesToString" (SliceSubslice byteT "b" #1 (slice.len "b")))).

End goose_lang.
