/-
What `Sprintf`'s output `fmt.Out` is without method arguments: a function of the pieces and the
arguments, `fmt.render` (`fmt.Out.eq_render`); and `Sprintf`'s spec in that form, from the spec
(`fmt.Sprintf_render_of`, `fmt.Sprintf_walName_of`).
-/
module

public import Perennial.Spec.fmt.Sprintf

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace fmt

/-- What Go writes for the directive `%verb` (`zw = none`) or `%0Nverb` of an argument without a
method, but `%q` (`DirOut`; nothing for `Arg.method`, whose output is the method's result; `s`
for `%q` of a string `s`, whose output `strconv`'s spec leaves open, `NoQuote`). -/
def dirOutFn (zw : Option Nat) (v : w8) : Arg → GoString
  | .nil => nilAngle
  | .bool b => if b then go!"true" else go!"false"
  | .int z => if v = verb_x then hexPad (zw.getD 0) z else decimalPad (zw.getD 0) z
  | .str s => if v = verb_x then bytesHex false s else s
  | .bytes bs _ => if v = verb_s then bs else if v = verb_x then bytesHex false bs else bytesDec bs
  | .method _ => []

/-- What Go writes for the directive `%.Pverb` of an integer (`PrecOut`; nothing for the other
arguments, which `PrecOk` excludes). -/
def precOutFn (p : Nat) (v : w8) : Arg → GoString
  | .int z => precPad (verbBase v) (decide (v = verb_X)) p z
  | _ => []

/-- The output of `Sprintf` for the pieces `ps` (without `%q`, `NoQuote`) and arguments without
methods (`Out`). -/
def render : List Piece → List Arg → GoString
  | [], _ => []
  | .lit s :: ps, args => s ++ render ps args
  | .percent :: ps, args => W8 37 :: render ps args
  | .dir zw v :: ps, a :: args => dirOutFn zw v a ++ render ps args
  | .dir _ _ :: _, [] => []
  | .prec p v :: ps, a :: args => precOutFn p v a ++ render ps args
  | .prec _ _ :: _, [] => []

/-- The pieces have no `%q`, whose output `strconv`'s spec leaves open. -/
def NoQuote (ps : List Piece) : Prop := ∀ zw, Piece.dir zw verb_q ∉ ps

/-- The argument is not `Arg.method`. -/
def Arg.NoMethod : Arg → Prop
  | .method _ => False
  | _ => True

theorem DirOut.eq_dirOutFn {zw : Option Nat} {v : w8} {a : Arg} {o : GoString}
    (h : DirOut zw v a o) (hm : a.NoMethod) (hq : v ≠ verb_q) : o = dirOutFn zw v a := by
  cases h <;> simp_all [dirOutFn, Arg.NoMethod, verb_x, verb_v, verb_d, verb_s, verb_t]

theorem PrecOut.eq_precOutFn {p : Nat} {v : w8} {a : Arg} {o : GoString} (h : PrecOut p v a o) :
    o = precOutFn p v a := by
  cases h; rfl

theorem NoQuote.tail {p : Piece} {ps : List Piece} (h : NoQuote (p :: ps)) : NoQuote ps :=
  fun zw hm => h zw (List.mem_cons_of_mem _ hm)

/-- Without `%q` and without method arguments, `Sprintf`'s output is `render ps args`. -/
theorem Out.eq_render {ps : List Piece} {args : List Arg} {s : GoString} (h : Out ps args s)
    (hm : ∀ a ∈ args, a.NoMethod) (hq : NoQuote ps) : s = render ps args := by
  induction h with
  | nil => rfl
  | lit s ps args out _ ih => simp [render, ih hm hq.tail]
  | percent ps args out _ ih => simp [render, ih hm hq.tail]
  | dir zw v a o ps args out hd _ ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hm
    have hv : v ≠ verb_q := by rintro rfl; exact hq zw (List.mem_cons_self ..)
    simp [render, ih hm.2 hq.tail, hd.eq_dirOutFn hm.1 hv]
  | prec p v a o ps args out hd _ ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hm
    simp [render, ih hm.2 hq.tail, hd.eq_precOutFn]

/-- `widthPad` with lowercase digits is `intOut`. -/
theorem widthPad_false (base w : Nat) (z : Int) (hb : base = 10 ∨ base = 16) :
    widthPad base false w z = intOut base w z := by
  unfold widthPad intOut hexPad decimalPad digitsIn
  rcases hb with rfl | rfl <;> simp

/-- `%.2X` of `0` is `00` (`versionPart` of OpenTelemetry's trace-context propagator). -/
theorem precPad_X_two_zero : precPad 16 true 2 0 = go!"00" := by
  simp (config := { decide := true }) [precPad, digitsIn, padZeros, hexNatU, hexDigitByteU]

/-- The pieces of `%016x-%016x.wal` (etcd's WAL file names, `walName`). -/
theorem encode_walName :
    go!"%016x-%016x.wal" =
      encode [.dir (some 16) verb_x, .lit go!"-", .dir (some 16) verb_x, .lit go!".wal"] := by
  simp [encode, Piece.encode, decimalNat_eq, digitByte, verb_x]

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `Sprintf` without method arguments returns `render ps args`. -/
theorem Sprintf_render_of (wp_Sprintf : fmt.Sprintf.spec (GF := GF) (hG := hG)) :
    ∀ (format : GoString) (ps : List Piece) (args_sl : GoSlice) (xs : List GoInterface)
      (args : List Arg) (dq : DFrac),
    format = encode ps → Fits ps args → (∀ a ∈ args, a.NoMethod) → NoQuote ps →
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args_sl ↦*{dq} xs ∗
        [∗list] x;a ∈ xs;args, isArg x a }}
      (App (App (Val (@! fmt.Sprintf)) (Val #format)) (Val #args_sl))
    {{ (s : GoString), RET #s; args_sl ↦*{dq} xs ∗ ([∗list] x;a ∈ xs;args, isArg x a) ∗
        ⌜s = render ps args⌝ }} := by
  intro format ps args_sl xs args dq he hf hm hq
  iintro %Φ ⟨#Hpkg, Hsl, Hargs⟩ HΦ
  iapply (wp_Sprintf format ps args_sl xs args dq he hf) $$ [Hsl Hargs]
  · iframe
    iexact Hpkg
  inext
  iintro %s ⟨Hsl, Hargs, %Hout⟩
  iapply HΦ
  iframe
  ipureintro
  exact Hout.eq_render hm hq

/-- `Sprintf("%016x-%016x.wal", seq, index)` of two `uint64`s: each zero-padded to 16 lowercase
hexadecimal digits. -/
theorem Sprintf_walName_of (wp_Sprintf : fmt.Sprintf.spec (GF := GF) (hG := hG)) :
    ∀ (seq index : w64) (sl : GoSlice) (dq : DFrac),
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗
        sl ↦*{dq} [interface.mkOk go.uint64 #seq, interface.mkOk go.uint64 #index] }}
      (App (App (Val (@! fmt.Sprintf)) (Val #(go!"%016x-%016x.wal"))) (Val #sl))
    {{ (r : GoString), RET #r;
        sl ↦*{dq} [interface.mkOk go.uint64 #seq, interface.mkOk go.uint64 #index] ∗
        ⌜r = hexPad 16 (uint.Z seq) ++ go!"-" ++ hexPad 16 (uint.Z index) ++ go!".wal"⌝ }} := by
  intro seq index sl dq
  iintro %Φ ⟨#Hpkg, Hsl⟩ HΦ
  iapply (Sprintf_render_of wp_Sprintf _ _ sl _ [.int (uint.Z seq), .int (uint.Z index)] dq
    encode_walName ?fits ?nm ?nq) $$ [Hsl]
  case fits =>
    refine .dir _ _ _ _ _ ⟨by simp, by simp [ZeroWidthOk]⟩ (.lit _ _ _ (by decide) ?_)
    exact .dir _ _ _ _ _ ⟨by simp, by simp [ZeroWidthOk]⟩ (.lit _ _ _ (by decide) .nil)
  case nm => simp [Arg.NoMethod]
  case nq => intro zw h; simp [verb_x, verb_q] at h
  · iframe
    isplitr
    · iexact Hpkg
    iapply BigSepL2.bigSepL2_cons.2
    isplitr
    · simp only [isArg]; ipureintro; exact .uint64 seq
    iapply BigSepL2.bigSepL2_cons.2
    isplitr
    · simp only [isArg]; ipureintro; exact .uint64 index
    iapply BigSepL2.bigSepL2_nil.2
    itrivial
  inext
  iintro %r ⟨Hsl, -, %Hr⟩
  iapply HΦ
  iframe
  ipureintro
  simp [Hr, render, dirOutFn, verb_x]

end wps

end fmt

end Perennial
