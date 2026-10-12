/-
`channel.fibonacci`'s spec: a producer sends the Fibonacci numbers over a
single-producer single-consumer channel (`go.dev/tour/concurrency/4`).
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.channel.Base
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.channel.FibonacciDefs

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.channel.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel

abbrev github_com.mit_pdos.perennial.goose.testdata.examples.channel.fibonacci.spec : Prop :=
  ∀ (n : w64) (c0 : Loc) (γ : SpscNames),
  0 < sint.Z n →
    {{ isPkgInit (PROP := IProp GF) pkg ∗
        isSpsc γ c0 (fun i v => iprop(⌜v = fib i.toNat⌝))
          (fun sent => iprop(⌜sent = fibList (sint.nat n)⌝)) ∗
        spscProducer γ ([] : List w64) }}
      (App (App (Val (@! fibonacci)) (Val #n)) (Val #c0))
    {{ RET #(); True }}

end spec

end Perennial
