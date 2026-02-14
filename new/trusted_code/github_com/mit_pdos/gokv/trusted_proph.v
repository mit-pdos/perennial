From New.golang Require Import defn.

Section defs.
Context `{ffi_syntax}.

Definition NewProphⁱᵐᵖˡ : val :=
  λ: <>, goose_lang.NewProph.

Definition ResolveBytesⁱᵐᵖˡ : val :=
  λ: "p" "slice",
  let: "s" := Convert (go.SliceType go.byte) go.string "slice" in
  goose_lang.ResolveProph "p" "s".

End defs.
