From Perennial.goose_lang Require Import notation typing.
From Perennial.goose_lang.lib.lock Require Import impl.
From Perennial.goose_lang.lib.typed_mem Require Import impl.

Module waitgroup.
  Section goose_lang.
    Context {ext:ffi_syntax}.
    Context {ext_tys: ext_types ext}.

    Local Coercion Var' (s:string): expr := Var s.

    Definition New: val := λ: <>, (lock.new #(), ref_to uint64T #0).
    Definition Add: val := λ: "wg" "delta",
        let: ("mu", "v") := "wg" in
        lock.acquire "mu" ;;
        "v" <-[uint64T] ("delta" + (![uint64T] "v")) ;;
        lock.release "mu"
    .

    Definition Done: val :=
      λ: "wg",
        let: ("mu", "v") := "wg" in
        lock.acquire "mu" ;;
        "v" <-[uint64T] ((![uint64T] "v") - #1) ;;
        lock.release "mu"
    .

    Definition Wait: val :=
      rec: "Wait" "wg" :=
        let: ("mu", "vptr") := "wg" in
        lock.acquire "mu" ;;
        let: "v" := (![uint64T] "vptr") in
        lock.release "mu" ;;
        if: "v" = #0 then #()
        else "Wait" "wg".
  End goose_lang.

End waitgroup.
