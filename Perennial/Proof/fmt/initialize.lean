/-
The proof of `fmt.initialize'`.
-/
module

public import Perennial.Spec.fmt.initialize
public import Perennial.Spec.sync.initialize
public import Perennial.Spec.io.initialize
public import Perennial.Spec.errors.initialize
public import Perennial.Spec.unicode.utf8.initialize
public import Perennial.Spec.reflect.initialize
public import Perennial.Spec.strconv.initialize
public import Perennial.Spec.errors.New
public import Perennial.Spec.syscall.initialize
public import Perennial.Spec.io.fs.initialize
public import Perennial.Spec.internal.poll.initialize
public import Perennial.Spec.internal.gomodel.initialize
public import Perennial.Spec.internal.stringslite.initialize

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : fmt.Assumptions]

theorem fmt.initialize'.wp_proof
    (wp_sync_initialize : sync.initialize'.spec (GF := GF) (hG := hG))
    (wp_io_initialize : io.initialize'.spec (GF := GF) (hG := hG))
    (wp_errors_initialize : errors.initialize'.spec (GF := GF) (hG := hG))
    (wp_utf8_initialize : unicode.utf8.initialize'.spec (GF := GF) (hG := hG))
    (wp_reflect_initialize : reflect.initialize'.spec (GF := GF) (hG := hG))
    (wp_strconv_initialize : strconv.initialize'.spec (GF := GF) (hG := hG))
    (wp_New : errors.New.spec (GF := GF) (hG := hG))
    (wp_syscall_initialize : syscall.initialize'.spec (GF := GF) (hG := hG))
    (wp_fs_initialize : io.fs.initialize'.spec (GF := GF) (hG := hG))
    (wp_poll_initialize : internal.poll.initialize'.spec (GF := GF) (hG := hG))
    (wp_gomodel_initialize : internal.gomodel.initialize'.spec (GF := GF) (hG := hG))
    (wp_stringslite_initialize : internal.stringslite.initialize'.spec (GF := GF) (hG := hG)) :
    fmt.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  repeat (wp_apply wp_GlobalAlloc (V := GoInterface) _ go.error as _)
  wp_apply wp_GlobalAlloc (V := sync.Pool) ssFree sync.Pool.ty as _
  wp_apply wp_GlobalAlloc (V := GoSlice) space _ as _
  wp_apply wp_GlobalAlloc (V := sync.Pool) ppFree sync.Pool.ty as Hpp
  wp_apply wp_syscall_initialize _ Hinit.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hsyscall⟩
  wp_apply wp_fs_initialize _ Hinit.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hfs⟩
  wp_apply wp_poll_initialize _ Hinit.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hpoll⟩
  wp_apply wp_gomodel_initialize _ Hinit.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hgomodel⟩
  wp_apply wp_sync_initialize _ Hinit.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hsync⟩
  wp_apply wp_reflect_initialize _ Hinit.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hreflect⟩
  wp_apply wp_io_initialize _ Hinit.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hio⟩
  wp_apply wp_utf8_initialize _ Hinit.2.2.2.2.1 $$ Hown as ⟨Hown, #Hutf8⟩
  wp_apply wp_strconv_initialize _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #Hstrconv⟩
  wp_apply wp_stringslite_initialize _ Hinit.2.2.1 $$ Hown as ⟨Hown, #Hstringslite⟩
  wp_apply wp_errors_initialize _ Hinit.2.1 $$ Hown as ⟨Hown, #Herrors⟩
  repeat (first
    | (wp_apply wp_New as %_ _)
    | (rw [recv_eq_func_mk BAnon BAnon]; wp_auto)
    | wp_auto)
  wp_apply wp_slice_literal (V := GoArray w16 2)
    [array.mk 2 [W16 9, W16 13], array.mk 2 [W16 32, W16 32], array.mk 2 [W16 133, W16 133], array.mk 2 [W16 160, W16 160], array.mk 2 [W16 5760, W16 5760], array.mk 2 [W16 8192, W16 8202], array.mk 2 [W16 8232, W16 8233], array.mk 2 [W16 8239, W16 8239], array.mk 2 [W16 8287, W16 8287], array.mk 2 [W16 12288, W16 12288]]
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, Hcap⟩
  -- `ppFree` is a `sync.Pool` of printers: its `New` returns a zero `pp`
  -- (`init_Pool`'s premise `local = nil` is the last goal)
  imod sync.init_Pool (globalAddr ppFree) _ iprop(True) fmt.ppFreeElem ⊤ ?_ $$ [Hpp] with #Hpool
  rotate_left
  · iframe Hpp
    iapply sync.newSpec_of_true
    iright
    wp_start
    dsimp only
    wp_auto
    wp_alloc l as Hl
    wp_auto
    iapply HΦ
    unfold fmt.ppFreeElem
    iexists l, (zero_val fmt.pp)
    iframe Hl
    isplitr
    · ipureintro; rfl
    rw [show (zero_val fmt.pp).buf' = slice.nil from rfl,
      show (zero_val fmt.pp).wrappedErrs' = slice.nil from rfl]
    isplitl; · iapply ownSlice_nil
    isplitl; · iapply ownSliceCap_nil
    isplitl; · iapply ownSlice_nil
    iapply ownSliceCap_nil
  repeat (first
    | (wp_apply wp_New as %_ _)
    | (rw [recv_eq_func_mk BAnon BAnon]; wp_auto)
    | wp_auto)
  iframe Hown
  is_pkg_init_finish
  unfold fmt.isInit
  iexists _
  iframe #
  ipureintro
  simp [func.nil]
  -- `init_Pool`'s premise: the literal's field `local` is `nil`
  rfl

end proof

end Perennial
