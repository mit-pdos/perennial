From Perennial.goose_lang Require Import lang notation prelude.

Section goose_lang.
Context `{ffi_sem: ffi_semantics}.
Context {ext_ty:ext_types ext}.

Definition ActReadId : Z := 0.
Definition ActAbortId : Z := 1.
Definition ActCommitId : Z := 2.

Definition NewProph : val :=
  λ: <>, goose_lang.NewProph.

Definition ResolveRead : val :=
  λ: "p" "tid" "key", goose_lang.ResolveProph "p" (#ActReadId, ("tid", "key")).

Definition ResolveAbort : val :=
  λ: "p" "tid", goose_lang.ResolveProph "p" (#ActAbortId, "tid").

(* TODO *)
Definition WrsToVal : val.
Admitted.

Definition ResolveCommit : val :=
  λ: "p" "tid" "wrbuf",
  let: "wrsval" := WrsToVal "wrbuf" in
  goose_lang.ResolveProph "p" (#ActCommitId, ("tid", "wrsval")).

End goose_lang.
