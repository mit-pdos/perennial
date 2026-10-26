/-
`github.com/goose-lang/std.Spawn`'s spec.
-/
module

public import Perennial.Proof.github_com.goose_lang.std.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.goose_lang.std.Assumptions]

/-- `Spawn(f)`: runs `f` in a new goroutine; the returned handle's `Join` gives `f`'s resource `P`. -/
abbrev github_com.goose_lang.std.Spawn.spec : Prop :=
  ∀ (P : IProp GF) (f : GoFunc),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.goose_lang.std ∗
        (∀ Φ : val → IProp GF, ▷ (P -∗ Φ #()) -∗ WP (App (Val #f) (Val #())) {{ Φ }}) }}
      (App (Val (@! Spawn)) (Val #f))
    {{ (l : Loc), RET #l; isJoinHandle l P }}

end spec

end Perennial
