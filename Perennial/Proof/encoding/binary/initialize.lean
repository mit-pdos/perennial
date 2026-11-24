/-
The proof of `encoding/binary.initialize'`.
-/
module

public import Perennial.Spec.encoding.binary.initialize
public import Perennial.Spec.sync.initialize
public import Perennial.Spec.slices.initialize
public import Perennial.Spec.math.initialize
public import Perennial.Spec.reflect.initialize
public import Perennial.Spec.io.initialize
public import Perennial.Spec.errors.initialize
public import Perennial.Spec.errors.New
public import Perennial.Proof.errors.NewVar

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : encoding.binary.Assumptions]

theorem encoding.binary.initialize'.wp_proof
    (wp_sync_initialize : sync.initialize'.spec (GF := GF) (hG := hG))
    (wp_slices_initialize : slices.initialize'.spec (GF := GF) (hG := hG))
    (wp_math_initialize : math.initialize'.spec (GF := GF) (hG := hG))
    (wp_reflect_initialize : reflect.initialize'.spec (GF := GF) (hG := hG))
    (wp_io_initialize : io.initialize'.spec (GF := GF) (hG := hG))
    (wp_errors_initialize : errors.initialize'.spec (GF := GF) (hG := hG))
    (wp_New : errors.New.spec (GF := GF) (hG := hG)) :
    encoding.binary.initialize'.spec (GF := GF) (hG := hG) := fun get_is_pkg_init Hinit => by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := GoInterface) errOverflow go.error as HO
  wp_apply wp_GlobalAlloc (V := bigEndian) BigEndian bigEndian.ty as Hbig
  ipersist Hbig
  wp_apply wp_GlobalAlloc (V := littleEndian) LittleEndian littleEndian.ty as Hlit
  ipersist Hlit
  wp_apply wp_GlobalAlloc (V := GoInterface) errBufferTooSmall go.error as _
  wp_apply wp_sync_initialize _ Hinit.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H1⟩
  wp_apply wp_slices_initialize _ Hinit.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H2⟩
  wp_apply wp_reflect_initialize _ Hinit.2.2.2.2.1 $$ Hown as ⟨Hown, #H6⟩
  wp_apply wp_math_initialize _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #H3⟩
  wp_apply wp_io_initialize _ Hinit.2.2.1 $$ Hown as ⟨Hown, #H4⟩
  wp_apply wp_errors_initialize _ Hinit.2.1 $$ Hown as ⟨Hown, #H5⟩
  -- the stores into `errOverflow` and `errBufferTooSmall` end the initializer: keep an update to
  -- make `errOverflow`'s cell persistent afterwards
  iapply wp_fupd
  wp_apply wp_New as %_ _
  wp_apply (errors.wp_New_errorString go!"binary: varint overflows a 64-bit integer") as %xO #EO
  ipersist HO
  ihave #NO : errors.newVar (GF := GF) errOverflow _ $$ []
  · iunfold errors.newVar
    iexists _
    iframe HO EO
  imodintro
  isplitr
  · ipureintro; exact isPanic_intoVal ()
  iframe Hown
  is_pkg_init_finish
  imodintro
  iunfold isInit
  iframe Hlit Hbig NO

end proof

end Perennial
