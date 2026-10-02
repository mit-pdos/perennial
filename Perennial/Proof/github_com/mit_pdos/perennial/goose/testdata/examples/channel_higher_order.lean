/-
Port of `new/proof/github_com/mit_pdos/perennial/goose/testdata/examples/channel_higher_order.v`:
worker goroutines run closures received over a channel and send the result back
over a per-request future channel.

Lean notes:
* The channel ghost state needs `Pos.Countable` of the element type. A
  `request.t` contains a `func.t` (GooseLang syntax, which mentions the
  arbitrary `ffi_val`), and the Lean `ffi_syntax` does not provide countability
  of `ffi_val`/`ffi_opcode` (Rocq's does), so `Pos.Countable request.t` cannot be
  proved here; the lemmas about the request channel take it as an instance
  argument `[Pos.Countable request.t]`.
-/
import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.channel_examples_init
import Perennial.Golang.Theory.Chan
import Perennial.Golang.Theory.Chan.Idioms.Bag
import Perennial.Golang.Theory.Chan.Idioms.Future

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

namespace github_com.mit_pdos.perennial.goose.testdata.examples.channel

section proof
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : heapGS HasLC.hasLC GF] [allG GF]
variable [sem : go.Semantics] [package_sem : channel.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel

def do_request (r : request.t) (γfut : future_names) (Q : go_string → IProp GF) : IProp GF :=
  iprop("Hf" ∷ WP (App (Val #r.f') (Val #())) {{ fun v => ∃ s : go_string, ⌜v = #s⌝ ∗ Q s }} ∗
    "#Hfut" ∷ is_future go_string γfut r.result' ∗
    "Hpromise" ∷ Fulfill (V := go_string) γfut Q)

def await_request (r : request.t) (γfut : future_names) (Q : go_string → IProp GF) : IProp GF :=
  iprop("#Hfut" ∷ is_future go_string γfut r.result' ∗
    "HAwait" ∷ Await (V := go_string) γfut [Q])

set_option goose.wp.extras true

theorem wp_mkRequest (f : func.t) (Q : go_string → IProp GF) :
    {{ is_pkg_init (PROP := IProp GF) pkg ∗
        WP (App (Val #f) (Val #())) {{ fun v => ∃ s : go_string, ⌜v = #s⌝ ∗ Q s }} }}
      (App (Val (@! mkRequest)) (Val #f))
    {{ (γfut : future_names) (r : request.t), RET #r;
        do_request r γfut Q ∗ await_request r γfut Q }} := by
  wp_start as Hf
  wp_auto
  sorry

end proof

end github_com.mit_pdos.perennial.goose.testdata.examples.channel

end Perennial
