From Perennial.goose_lang Require Import lang notation prelude.

Section goose_lang.
Context `{ffi_sem: ffi_semantics}.
Context {ext_ty:ext_types ext}.

(* begin copied from wrbuf.v *)
Definition WrEnt := struct.decl [
  "key" :: uint64T;
  "val" :: stringT;
  "wr" :: boolT;
  "tpl" :: ptrT
].

Definition WrBuf := struct.decl [
  "ents" :: slice.T (struct.t WrEnt)
].
(* end copied from wrbuf.v *)


Definition ActReadId : Z := 0.
Definition ActAbortId : Z := 1.
Definition ActCommitId : Z := 2.

Definition NewProphⁱᵐᵖˡ : val :=
  λ: <>, goose_lang.NewProph.

Definition ResolveRead : val :=
  λ: "p" "tid" "key", goose_lang.ResolveProph "p" (#ActReadId, ("tid", "key")).

Definition ResolveAbort : val :=
  λ: "p" "tid", goose_lang.ResolveProph "p" (#ActAbortId, "tid").

Definition WrbufToVal : val :=
  λ: "wrbuf",
    (* Goose alloc lemmas are very wonky, and directly allocating a #() does not work.
       So we allocate a 0 and then store #() in it... *)
    let: "res" := ref #0 in
    "res" <- #();;
    let: "slice" := (struct.loadF WrBuf "ents" "wrbuf") in
    forSlice (structTy WrEnt) (λ: "idx" "val",
      let: "key" := Fst "val" in
      let: "str" := Fst (Snd "val") in
      let: "present" := Fst (Snd (Snd "val")) in
      "res" <- ("key", "present", "str", !"res")
    ) "slice";;
    !"res".

Definition ResolveCommit : val :=
  λ: "p" "tid" "wrbuf",
  let: "wrbufval" := WrbufToVal "wrbuf" in
  goose_lang.ResolveProph "p" (#ActCommitId, ("tid", "wrbufval")).

End goose_lang.

