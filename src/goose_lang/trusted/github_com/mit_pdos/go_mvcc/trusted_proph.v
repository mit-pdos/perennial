From Perennial.goose_lang Require Import lang notation.

Section goose_lang.
Context {ext:ffi_syntax}.
Local Coercion Var' (s:string) : expr := Var s.

Definition EvReadId : Z := 0.
Definition EvAbortId : Z := 1.
Definition EvCommitId : Z := 2.

Definition NewProph : val :=
  λ: <>, NewProph.

Definition ResolveRead : val :=
  λ: "p" "tid" "key", ResolveProph "p" (#EvReadId, ("tid", "key")).

Definition ResolveAbort : val :=
  λ: "p" "tid", ResolveProph "p" (#EvAbortId, "tid").

(* FIXME implement this *)
Definition ResolveCommit : val :=
  λ: "p" "tid" "wrbuf", #().

End goose_lang.

