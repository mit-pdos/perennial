/-
The proof of `crypto/rand.initialize'`, from the trust-boundary axiom
`crypto.rand.wp_Reader_init` on the package's one untranslated variable initializer.
-/
module

public import Perennial.Spec.crypto.rand.initialize
public import Perennial.Spec.math.big.initialize

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **Trust boundary: `crypto/rand`'s untranslated variable initializer sets `Reader`.**
`var Reader io.Reader = rand.Reader` (the reader of `crypto/internal/rand`, behind the
platform's random source) is not translated (`crypto/rand.toml` translates nothing but the
trusted `Int`), so goose emits an axiomatized `Reader.init : val` with no semantics, and no
`GlobalAlloc` of `Reader`; in Go it runs at program start, allocates the global and stores
the reader. The axiom says only that the global then holds some `io.Reader`, for good
(`↦□`: nothing translated writes it; `isInitialized`). Satisfiable: `Reader.init` is an
uninterpreted constant, and `go.GlobalAlloc Reader t` (`t` the interface type `io.Reader`)
meets the triple: by `wp_GlobalAlloc`, the global holds the zero `GoInterface`, made persistent
(a second call allocates a location other than `globalAddr Reader`, so it does not return). -/
axiom crypto.rand.wp_Reader_init :
    {{ (True : IProp GF) }}
      (App (Val crypto.rand.Reader.init) (Val #()))
    {{ (rdr : GoInterface), RET #(); globalAddr crypto.rand.Reader ↦□ rdr }}

variable [package_sem : crypto.rand.Assumptions]

theorem crypto.rand.initialize'.wp_proof
    (wp_big_initialize : math.big.initialize'.spec (GF := GF) (hG := hG)) :
    crypto.rand.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_big_initialize _ Hinit.2.1 $$ Hown as ⟨Hown, #Hbig⟩
  wp_apply crypto.rand.wp_Reader_init as %rdr #HReader
  iframe Hown
  is_pkg_init_finish
  unfold crypto.rand.isInitialized
  iexists rdr
  iexact HReader

end proof

end Perennial
