/-
The proof of `strconv.initialize'`. The variables made by `errors.New` are kept with their exact
type (`errors.wp_New_errorString`).
-/
module

public import Perennial.Spec.strconv.initialize
public import Perennial.Spec.errors.initialize
public import Perennial.Spec.internal.strconv.initialize
public import Perennial.Spec.internal.stringslite.initialize
public import Perennial.Spec.unicode.utf8.initialize

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : strconv.Assumptions]

omit package_sem in
/-- `wp_slice_literal` with the literal's size given as `n` (`go.arrayLiteralSize kvs = n`, by
`rfl` for a concrete literal): the array literal's WP is then over `go.ArrayType n t` with `n` a
literal, which `wp_pures` steps in one step (`pure_wp_array_lit`), where it would step the
`ArraySet` chain of the long literal one element at a time. -/
private theorem wp_slice_literal_size {s : Stuckness} {E : CoPset} {V : Type} [ZeroVal V]
    [TypedPointsto (GF := GF) V] {st t : go.GoType} [IntoValTyped (GF := GF) V t]
    [st ↓u go.SliceType t] (n : Int) (l : List V) (kvs : List keyed_element)
    (hn : go.arrayLiteralSize kvs = n) (Φ : val → IProp GF) :
    WP (App (Val (GoInstruction (CompositeLiteral (go.ArrayType n t))))
          (Val (LiteralValueV kvs))) @ s; E
      {{ v, ⌜v = #(array.mk n l)⌝ ∗
        (∀ sl_ptr : Loc,
          (slice.mk sl_ptr (W64 n) (W64 n) ↦* l ∗
            ownSliceCap V (slice.mk sl_ptr (W64 n) (W64 n)) (DFrac.own 1)) -∗
          Φ #(slice.mk sl_ptr (W64 n) (W64 n))) }} ⊢
    WP (App (Val (GoInstruction (CompositeLiteral st))) (Val (LiteralValueV kvs))) @ s; E {{ Φ }} := by
  subst hn
  exact wp_slice_literal l kvs Φ

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem strconv.initialize'.wp_proof
    (wp_errors_initialize : errors.initialize'.spec (GF := GF) (hG := hG))
    (wp_strconv_initialize : internal.strconv.initialize'.spec (GF := GF) (hG := hG))
    (wp_stringslite_initialize : internal.stringslite.initialize'.spec (GF := GF) (hG := hG))
    (wp_utf8_initialize : unicode.utf8.initialize'.spec (GF := GF) (hG := hG)) :
    strconv.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrSyntax go.error as HS
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrRange go.error as HR
  wp_apply wp_GlobalAlloc (V := GoSlice) isNotPrint32 (go.GoType.SliceType go.uint16) as HNP32
  wp_apply wp_GlobalAlloc (V := GoSlice) isPrint32 (go.GoType.SliceType go.uint32) as HP32
  wp_apply wp_GlobalAlloc (V := GoSlice) isNotPrint16 (go.GoType.SliceType go.uint16) as HNP16
  wp_apply wp_GlobalAlloc (V := GoSlice) isPrint16 (go.GoType.SliceType go.uint16) as HP16
  wp_apply wp_utf8_initialize _ Hinit.2.2.2.2.1 $$ Hown as ⟨Hown, #Hutf8⟩
  wp_apply wp_stringslite_initialize _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #Hsl⟩
  wp_apply wp_strconv_initialize _ Hinit.2.2.1 $$ Hown as ⟨Hown, #Hisc⟩
  wp_apply wp_errors_initialize _ Hinit.2.1 $$ Hown as ⟨Hown, #Herrors⟩
  wp_apply wp_slice_literal_size (V := w16) (t := go.uint16) 412 _ _ (by rfl)
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_auto
  ipersist Hsl
  ipersist HP16
  ihave #THP16 : strconv.tableVar w16 _ 412 $$ []
  · iunfold strconv.tableVar
    iexists _, _
    iframe HP16 Hsl
    ipureintro; rfl
  iclear Hsl HP16
  wp_apply wp_slice_literal_size (V := w16) (t := go.uint16) 132 _ _ (by rfl)
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_auto
  ipersist Hsl
  ipersist HNP16
  ihave #THNP16 : strconv.tableVar w16 _ 132 $$ []
  · iunfold strconv.tableVar
    iexists _, _
    iframe HNP16 Hsl
    ipureintro; rfl
  iclear Hsl HNP16
  wp_apply wp_slice_literal_size (V := w32) (t := go.uint32) 566 _ _ (by rfl)
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_auto
  ipersist Hsl
  ipersist HP32
  ihave #THP32 : strconv.tableVar w32 _ 566 $$ []
  · iunfold strconv.tableVar
    iexists _, _
    iframe HP32 Hsl
    ipureintro; rfl
  iclear Hsl HP32
  wp_apply wp_slice_literal_size (V := w16) (t := go.uint16) 120 _ _ (by rfl)
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_auto
  ipersist Hsl
  ipersist HNP32
  ihave #THNP32 : strconv.tableVar w16 _ 120 $$ []
  · iunfold strconv.tableVar
    iexists _, _
    iframe HNP32 Hsl
    ipureintro; rfl
  iclear Hsl HNP32
  wp_apply errors.wp_New_errorString as %xR #ER
  ipersist HR
  -- the store into `ErrSyntax` ends the initializer: keep an update to make its cell
  -- persistent afterwards
  iapply wp_fupd
  wp_apply errors.wp_New_errorString as %xS #ES
  ipersist HS
  ihave #NR : errors.newVar (GF := GF) ErrRange _ $$ []
  · iunfold errors.newVar
    iexists _
    iframe HR ER
  ihave #NS : errors.newVar (GF := GF) ErrSyntax _ $$ []
  · iunfold errors.newVar
    iexists _
    iframe HS ES
  imodintro
  isplitr
  · ipureintro; exact isPanic_intoVal ()
  iframe Hown
  is_pkg_init_finish
  imodintro
  iunfold isInit
  iframe NR NS THP16 THNP16 THP32 THNP32

end proof

end Perennial
