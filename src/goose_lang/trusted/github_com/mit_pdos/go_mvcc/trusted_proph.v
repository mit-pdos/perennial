From Perennial.goose_lang Require Import lang notation.

Section goose_lang.
Context {ext:ffi_syntax}.
Local Coercion Var' (s:string) : expr := Var s.

Definition ActReadId : Z := 0.
Definition ActAbortId : Z := 1.
Definition ActCommitId : Z := 2.

Definition NewProph : val :=
  λ: <>, NewProph.

Definition ResolveRead : val :=
  λ: "p" "tid" "key", ResolveProph "p" (#ActReadId, ("tid", "key")).

Definition ResolveAbort : val :=
  λ: "p" "tid", ResolveProph "p" (#ActAbortId, "tid").

(* FIXME implement this *)
Definition ResolveCommit : val :=
  λ: "p" "tid" "wrbuf", #().

End goose_lang.

