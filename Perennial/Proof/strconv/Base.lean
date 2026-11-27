/-
Shared definitions of the proofs of the Go `strconv` package: its `isPkgInit` (the `errors.New`
errors `ErrRange` and `ErrSyntax`, and the lengths of `IsPrint`'s tables).
-/
module

public import Perennial.Proof.errors.Base
public import Perennial.Proof.errors.NewVar
public import Perennial.Proof.internal.strconv.Base
public import Perennial.Proof.internal.stringslite.Base
public import Perennial.Proof.unicode.utf8.Base
public import Perennial.Code.strconv
public import Perennial.GeneratedProof.strconv

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace strconv

/-- The indices `lowerhex[...]` that `appendQuotedWith` and `appendEscapedRune` read are below 16:
`b&0xF` of a byte, -/
theorem lowerhex_idx_and_w8 (y : w8) :
    0 ≤ sint.Z (W64 (uint.Z (y &&& W8 15))) ∧ sint.Z (W64 (uint.Z (y &&& W8 15))) < 16 := by
  have h : (y &&& 15#8).toNat < 16 := by
    rw [BitVec.toNat_and]; have := Nat.and_le_right (n := y.toNat) (m := (15#8).toNat)
    have h : (15#8).toNat = 15 := rfl; omega
  rw [show (W8 15 : w8) = 15#8 from rfl]
  constructor <;> word

/-- `r>>s&0xF` of a rune, -/
theorem lowerhex_idx_and_w32 (x : w32) :
    0 ≤ sint.Z (W64 (sint.Z (x &&& W32 15))) ∧ sint.Z (W64 (sint.Z (x &&& W32 15))) < 16 := by
  have h : (x &&& 15#32).toNat < 16 := by
    rw [BitVec.toNat_and]; have := Nat.and_le_right (n := x.toNat) (m := (15#32).toNat)
    have h : (15#32).toNat = 15 := rfl; omega
  have hz : (x &&& 15#32).toInt = (x &&& 15#32).toNat := by
    rw [BitVec.toInt_eq_toNat_cond]; split <;> omega
  rw [show (W32 15 : w32) = 15#32 from rfl]
  simp only [sint.Z, hz]
  constructor <;> word

/-- `b>>4` of a byte. -/
theorem lowerhex_idx_shr_w8_lo (y : w8) : 0 ≤ sint.Z (W64 (uint.Z (y >>> W64 4))) := by word
theorem lowerhex_idx_shr_w8_hi (y : w8) : sint.Z (W64 (uint.Z (y >>> W64 4))) < 16 := by word

/-- `lowerhex[k]` (`quote.go`), the `k`-th lower-case hexadecimal digit. -/
def lowerhexAt (k : w64) : w8 := (go!"0123456789abcdef" : GoString).getD (sint.nat k) (W8 0)

/-- Indexing `lowerhex`, as the semantics does: some digit for `0 ≤ k < 16`. -/
theorem lowerhex_get (k : w64) :
    (if 0 ≤ sint.Z k then (go!"0123456789abcdef" : GoString)[sint.nat k]? else none) =
      if 0 ≤ sint.Z k ∧ sint.Z k < 16 then some (lowerhexAt k) else none := by
  unfold lowerhexAt
  by_cases h0 : 0 ≤ sint.Z k <;> by_cases h1 : sint.Z k < 16 <;> simp [h0, h1]

/-- `lowerhex[k]` once the semantics' sign test is simplified: some digit for `0 ≤ k < 16`. -/
theorem lowerhex_get' (k : w64) (h0 : 0 ≤ sint.Z k) (h1 : sint.Z k < 16) :
    (go!"0123456789abcdef" : GoString)[sint.nat k]? = some (lowerhexAt k) := by
  unfold lowerhexAt
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem (by simp only [sint.nat] at *; simp; omega)]
  rfl

theorem lowerhex_idx_and_w8_lo (y : w8) : 0 ≤ sint.Z (W64 (uint.Z (y &&& W8 15))) :=
  (lowerhex_idx_and_w8 y).1
theorem lowerhex_idx_and_w8_hi (y : w8) : sint.Z (W64 (uint.Z (y &&& W8 15))) < 16 :=
  (lowerhex_idx_and_w8 y).2

theorem lowerhex_idx_and_w32_lo (x : w32) : 0 ≤ sint.Z (W64 (sint.Z (x &&& W32 15))) :=
  (lowerhex_idx_and_w32 x).1

theorem lowerhex_idx_and_w32_hi (x : w32) : sint.Z (W64 (sint.Z (x &&& W32 15))) < 16 :=
  (lowerhex_idx_and_w32 x).2

/-- `quoteWith`'s capacity `3*len(s)/2` is not negative, for `len(s) ≤ 2^47` (`maxAddr`). -/
theorem quoteWith_cap (n : Nat) (h : (n : Int) ≤ 2^47) :
    0 ≤ sint.Z (BitVec.sdiv (W64 3 * W64 (n : Int)) (W64 2)) := by
  have hx : (W64 (n : Int)).toNat = n := by simp only [W64, BitVec.toNat_ofInt]; omega
  have h3 : (W64 3 * W64 (n : Int)).toNat = 3 * n := by
    rw [BitVec.toNat_mul, hx, show (W64 3 : w64).toNat = 3 from rfl]; omega
  have hm : (W64 3 * W64 (n : Int)).msb = false := by
    rw [BitVec.msb_eq_decide, h3]; simp only [decide_eq_false_iff_not]; omega
  rw [BitVec.sdiv_eq, hm, show (W64 2 : w64).msb = false from rfl]
  have hu : (BitVec.udiv (W64 3 * W64 (n : Int)) (W64 2)).toNat = 3 * n / 2 := by
    change (BitVec.toNat ((W64 3 * W64 (n : Int)) / W64 2)) = _
    rw [BitVec.toNat_udiv, h3, show (W64 2 : w64).toNat = 2 from rfl]
  simp only [sint.Z]
  rw [BitVec.toInt_eq_toNat_cond, hu]
  split <;> omega

set_option maxRecDepth 100000 in
/-- `IsPrint`'s indices `i&^1` and `i|1` stay below the length of an even table. -/
theorem isPrint_idx_bv (i : BitVec 64) (n : BitVec 64) (hn : n = 424#64 ∨ n = 508#64) (h : i < n) :
    (i &&& ~~~1#64) < n ∧ (i ||| 1#64) < n := by
  have htab : ∀ k < 508, k ||| 1 < 508 ∧ (k < 424 → k ||| 1 < 424) := by decide
  rw [BitVec.lt_def] at h ⊢
  rw [BitVec.lt_def, BitVec.toNat_and, BitVec.toNat_or]
  have h1 : (1#64).toNat = 1 := rfl
  rw [h1]
  have hle := Nat.and_le_left (n := i.toNat) (m := (~~~1#64).toNat)
  rcases hn with rfl | rfl
  · have : (424#64).toNat = 424 := rfl
    rw [this] at h ⊢
    exact ⟨by omega, (htab _ (by omega)).2 h⟩
  · have : (508#64).toNat = 508 := rfl
    rw [this] at h ⊢
    exact ⟨by omega, (htab _ h).1⟩

/-- `IsPrint`'s indices `i&^1` and `i|1`, for `0 ≤ i < n`, are in `[0, n)` (`n` the even length of
`isPrint16` or `isPrint32`). -/
theorem isPrint_idx (i : w64) (n : Nat) (hn : n = 424 ∨ n = 508) (h0 : 0 ≤ sint.Z i)
    (h1 : sint.Z i < n) :
    (0 ≤ sint.Z (i &&& ~~~W64 1) ∧ sint.Z (i &&& ~~~W64 1) < n) ∧
      (0 ≤ sint.Z (i ||| W64 1) ∧ sint.Z (i ||| W64 1) < n) := by
  have hiN : i.toNat < n := by
    simp only [sint.Z] at h0 h1; rw [BitVec.toInt_eq_toNat_cond] at h0 h1; split at h1 <;> omega
  have hb := isPrint_idx_bv i (W64 n) (by rcases hn with rfl | rfl <;> decide)
    (by rw [BitVec.lt_def]; simp only [W64, BitVec.toNat_ofInt]; rcases hn with rfl | rfl <;> omega)
  rw [BitVec.lt_def, BitVec.lt_def] at hb
  have hW : (W64 n).toNat = n := by simp only [W64, BitVec.toNat_ofInt]; rcases hn with rfl | rfl <;> omega
  rw [hW] at hb
  have hn' : n < 2 ^ 63 := by omega
  rw [show (W64 1 : w64) = 1#64 from rfl]
  simp only [sint.Z]
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toInt_eq_toNat_cond]
  constructor <;> constructor <;> split <;> omega

/-- `bsearch`'s midpoint `i + (j-i)>>1`, for `0 ≤ i ≤ j`, is `i + (j - i) / 2`. -/
theorem bsearch_mid (i j : w64) (hi : 0 ≤ sint.Z i) (hij : sint.Z i ≤ sint.Z j) :
    sint.Z (i + BitVec.sshiftRight' (j - i) (W64 1)) = sint.Z i + (sint.Z j - sint.Z i) / 2 := by
  have hi' : i.toNat < 2^63 := by simp only [sint.Z] at hi; rw [BitVec.toInt_eq_toNat_cond] at hi; split at hi <;> omega
  have hj' : j.toNat < 2^63 := by simp only [sint.Z] at hi hij; rw [BitVec.toInt_eq_toNat_cond, BitVec.toInt_eq_toNat_cond] at hij; split at hij <;> split at hij <;> omega
  have hij' : i.toNat ≤ j.toNat := by simp only [sint.Z] at hi hij; rw [BitVec.toInt_eq_toNat_cond, BitVec.toInt_eq_toNat_cond] at hij; split at hij <;> split at hij <;> omega
  have hmsb : (j - i).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_sub, decide_eq_false_iff_not]; omega
  rw [BitVec.sshiftRight', BitVec.sshiftRight_eq_of_msb_false hmsb]
  have hiZ : i.toInt = i.toNat := by rw [BitVec.toInt_eq_toNat_cond]; split <;> omega
  have hjZ : j.toInt = j.toNat := by rw [BitVec.toInt_eq_toNat_cond]; split <;> omega
  have h1 : (W64 1).toNat = 1 := rfl
  simp only [sint.Z, hiZ, hjZ]
  rw [BitVec.toInt_eq_toNat_cond]
  simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_sub, h1, Nat.shiftRight_eq_div_pow]
  split <;> omega

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : strconv.Assumptions]

/-- The package variable `X`, a table of `IsPrint` (`isprint.go`): a slice of `n` elements of
type `V`, read-only. Only the length is kept: what `IsPrint`'s indexing needs. -/
def tableVar (V : Type) [ZeroVal V] [TypedPointsto (GF := GF) V] (X : GoString) (n : Nat) : IProp GF :=
  iprop(∃ (sl : GoSlice) (xs : List V), globalAddr X ↦□ sl ∗ sl ↦*□ xs ∗ ⌜xs.length = n⌝)

instance tableVar_persistent (V : Type) [ZeroVal V] [TypedPointsto (GF := GF) V] (X : GoString) (n : Nat) :
    Persistent (tableVar (GF := GF) V X n) := by
  unfold tableVar; infer_instance

/-- The package-initialized state (persistent; Go never writes these variables after
initialization): each error variable made by `errors.New` holds that error (`errors.newVar`),
and `IsPrint`'s tables have their lengths (each `isPrint` table of ranges an even one). -/
abbrev isInit : IProp GF :=
  iprop("#HErrRange" ∷ errors.newVar ErrRange go!"value out of range" ∗
  "#HErrSyntax" ∷ errors.newVar ErrSyntax go!"invalid syntax" ∗
  "#HisPrint16" ∷ tableVar w16 isPrint16 424 ∗
  "#HisNotPrint16" ∷ tableVar w16 isNotPrint16 133 ∗
  "#HisPrint32" ∷ tableVar w32 isPrint32 508 ∗
  "#HisNotPrint32" ∷ tableVar w16 isNotPrint32 112)

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.strconv :=
  define_is_pkg_init isInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.strconv :=
  build_get_is_pkg_init_wf

theorem isInit_access :
    isPkgInit (PROP := IProp GF) pkg_id.strconv ⊢ isInit (GF := GF) := by
  with_unfolding_all exact isPkgInit_access (PROP := IProp GF) pkg_id.strconv

/-- **`err` is a fresh `*NumError` for the function `fn` and the input `s`**, whose `Err` is the
error the package variable `X` holds (`ErrSyntax` or `ErrRange`): what `ParseUint` and the other
parsers return on a failed conversion. -/
def numErrorOf (err : GoInterface) (fn s X : GoString) : IProp GF :=
  iprop(∃ (l : Loc) (e : GoInterface),
    ⌜err = interface.mkOk (go.GoType.PointerType NumError.ty) #l⌝ ∗
    l ↦ NumError.mk fn s e ∗ globalAddr X ↦□ e)

/-- **The error `ei`'s `Error()` returns** (some string): what `NumError.Error` needs of its `Err`. -/
def errorReturns (ei : GoInterfaceOk) : IProp GF :=
  iprop(∀ Φ : val → IProp GF, ▷ (∀ m : GoString, Φ #m) -∗
    WP (App (Val #(methods ei.ty go!"Error" ei.v)) (Val #())) {{ Φ }})

/-- **`*NumError`'s method set** (goose's `ptr_method_set`): `Error() string` and `Unwrap() error`;
no `Is`, `As` or `Format` method. -/
theorem numError_methodSet :
    methodSet (go.GoType.PointerType NumError.ty) !! go!"Error" =
        some (go.signature.Signature [] false [go.string]) ∧
      methodSet (go.GoType.PointerType NumError.ty) !! go!"Unwrap" =
        some (go.signature.Signature [] false [go.error]) ∧
      methodSet (go.GoType.PointerType NumError.ty) !! go!"Is" = none ∧
      methodSet (go.GoType.PointerType NumError.ty) !! go!"As" = none ∧
      methodSet (go.GoType.PointerType NumError.ty) !! go!"Format" = none := by
  have h := fun m => go.method_set_is (t := go.GoType.PointerType NumError.ty) m
  have hE := h go!"Error"; have hU := h go!"Unwrap"; have hIs := h go!"Is"
  have hAs := h go!"As"; have hF := h go!"Format"
  simp only [go.methodSetLookup_cons, go.methodSetLookup_nil, gooseReduceIteDecide] at hE hU hIs hAs hF
  exact ⟨hE, hU, hIs, hAs, hF⟩

end wps

end strconv

end Perennial
