/-
Shared definitions of the proofs of `fmt`'s print path (print.go, format.go), translated from Go:
what the spec of `Sprintf` says (a format made of `Piece`s, the arguments as `Arg`s, the output
`Out`), and the resources its proofs pass around (a printer's buffer, its `fmt`, the printer).

The verified subset: literal text, `%%`, and `%d %v %x` of an integer (also `%0Nd %0Nv %0Nx`, and
`%.Pd %.Pv %.Px %.PX`), `%v %t` of a bool, `%v` of `nil`, `%s %v %x %q` of a string and of a value
with an `Error()` or `String()` method, `%s %v %d %x` of a `[]byte`, with exactly one argument per
directive. Everything else (other verbs or flags, a width with a precision, a precision of anything
but an integer, argument indices, `%T`, `%p`, floats, extra or missing arguments, and `%v` of a
value Go formats by reflection, `printValue`) is outside the precondition: the translated code is
stuck there or not verified.
-/
module

public import Perennial.Proof.fmt.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace fmt

/-! ## The format and the arguments -/

/-- The bytes of the verbs: `d` is `W8 100`, `s` `W8 115`, `v` `W8 118`, `x` `W8 120`, `q`
`W8 113`, `t` `W8 116`, `X` `W8 88`; `%` is `W8 37`, `0` `W8 48`, `.` `W8 46`. -/
abbrev verb_d : w8 := W8 100
abbrev verb_s : w8 := W8 115
abbrev verb_v : w8 := W8 118
abbrev verb_x : w8 := W8 120
abbrev verb_q : w8 := W8 113
abbrev verb_t : w8 := W8 116
abbrev verb_X : w8 := W8 88

/-- A piece of a format string in the verified subset. -/
inductive Piece where
  /-- Literal bytes, copied (none of them a `%`, `Fits`). -/
  | lit (s : GoString)
  /-- `%%`, which writes `%`. -/
  | percent
  /-- `%` and the verb `verb`, or, with `zw = some N`, `%0N` and the verb: zero padding to the
  width `N` (written in decimal, `1 ≤ N ≤ 10^6`, `Fits`). -/
  | dir (zw : Option Nat) (verb : w8)
  /-- `%.P` and the verb: the precision `P` (written in decimal, `P ≤ 10^6`, `Fits`). -/
  | prec (p : Nat) (verb : w8)

/-- The bytes of a piece in the format string. -/
def Piece.encode : Piece → GoString
  | .lit s => s
  | .percent => [W8 37, W8 37]
  | .dir none v => [W8 37, v]
  | .dir (some n) v => W8 37 :: W8 48 :: (decimalNat n ++ [v])
  | .prec p v => W8 37 :: W8 46 :: (decimalNat p ++ [v])

/-- The format string made of the pieces `ps`. -/
def encode (ps : List Piece) : GoString := ps.flatMap Piece.encode

/-- An argument of `Sprintf` in the verified subset, as Go's `printArg` sees it (`isArg` says
which Go values these are). -/
inductive Arg where
  /-- `nil`. -/
  | nil
  /-- A `bool`. -/
  | bool (b : Bool)
  /-- A value of one of the predeclared integer types (`int`, `int8`, ..., `uint64`, `uintptr`;
  not a named one, which Go formats by reflection), as an integer. -/
  | int (z : Int)
  /-- A `string`. -/
  | str (s : GoString)
  /-- A `[]byte` holding `bs`, lent at the fraction `dq`. -/
  | bytes (bs : GoString) (dq : DFrac)
  /-- A value whose `Error()` (or, if it is not an `error`, whose `String()`) Go calls, which
  returns some string `s` with `P s`. -/
  | method (P : GoString → Prop)

/-- The width of `%0N` is between 1 and `10^6` (Go's `parsenum` gives up on more digits). -/
def ZeroWidthOk : Option Nat → Prop
  | none => True
  | some n => 1 ≤ n ∧ n ≤ 1000000

/-- The directive `%verb` (`zw = none`) or `%0Nverb` (`zw = some N`) of the argument `a` is in
the verified subset. `%x` of fewer than `2^62` bytes: `fmtSbx` computes the width `2 * length` in
an `int`, and writes nothing if that wraps. -/
def DirOk : Option Nat → w8 → Arg → Prop
  | zw, v, .int _ => (v = verb_d ∨ v = verb_v ∨ v = verb_x) ∧ ZeroWidthOk zw
  | none, v, .nil => v = verb_v
  | none, v, .bool _ => v = verb_v ∨ v = verb_t
  | none, v, .str s => v = verb_s ∨ v = verb_v ∨ (v = verb_x ∧ s.length < 2 ^ 62) ∨ v = verb_q
  | none, v, .bytes bs _ =>
    v = verb_s ∨ v = verb_v ∨ v = verb_d ∨ (v = verb_x ∧ bs.length < 2 ^ 62)
  | none, v, .method P =>
    v = verb_s ∨ v = verb_v ∨ (v = verb_x ∧ ∀ s, P s → s.length < 2 ^ 62) ∨ v = verb_q
  | some _, _, _ => False

/-- The directive `%.Pverb` of the argument `a` is in the verified subset: an integer under `d`,
`v`, `x` or `X`, the precision at most `10^6` (Go's `parsenum` gives up on more digits). -/
def PrecOk (p : Nat) (v : w8) : Arg → Prop
  | .int _ => (v = verb_d ∨ v = verb_v ∨ v = verb_x ∨ v = verb_X) ∧ p ≤ 1000000
  | _ => False

/-- The pieces `ps` and the arguments `as` are in the verified subset: no literal contains a `%`,
each directive takes the next argument and is `DirOk` of it, and every argument is used. -/
inductive Fits : List Piece → List Arg → Prop
  | nil : Fits [] []
  | lit (s : GoString) (ps : List Piece) (args : List Arg) :
      W8 37 ∉ s → Fits ps args → Fits (.lit s :: ps) args
  | percent (ps : List Piece) (args : List Arg) : Fits ps args → Fits (.percent :: ps) args
  | dir (zw : Option Nat) (v : w8) (a : Arg) (ps : List Piece) (args : List Arg) :
      DirOk zw v a → Fits ps args → Fits (.dir zw v :: ps) (a :: args)
  | prec (p : Nat) (v : w8) (a : Arg) (ps : List Piece) (args : List Arg) :
      PrecOk p v a → Fits ps args → Fits (.prec p v :: ps) (a :: args)

/-! ## The output -/

/-- What `%0Nx` writes for `N = w` (`%x` for `w = 0`): the lowercase hexadecimal of `z`, with
leading zeros up to width `w`, the sign of a negative `z` before the zeros. -/
def hexPad (w : Nat) (z : Int) : GoString :=
  if z < 0 then W8 45 :: padZeros (w - 1) (hexNat z.natAbs)
  else padZeros w (hexNat z.natAbs)

/-- What `fmtInteger` writes in base `base` (10 or 16, lowercase digits) for the width `w` of
zero padding (0 for none): `decimalPad w z` or `hexPad w z`. -/
def intOut (base : Nat) (w : Nat) (z : Int) : GoString :=
  if base = 16 then hexPad w z else decimalPad w z

/-- The uppercase hexadecimal digit of `d < 16`: `'0' + d` below 10, `'A' + (d - 10)` above. -/
def hexDigitByteU (d : Nat) : w8 := if d < 10 then W8 (48 + d) else W8 (65 + (d - 10))

/-- The uppercase hexadecimal digits of `n`, most significant first, without leading zeros. -/
def hexNatU (n : Nat) : GoString :=
  (if n < 16 then [] else hexNatU (n / 16)) ++ [hexDigitByteU (n % 16)]
termination_by n
decreasing_by omega

/-- The digits of `n` in base `base`: hexadecimal for 16 (uppercase if `upper`), decimal
otherwise. -/
def digitsIn (base : Nat) (upper : Bool) (n : Nat) : GoString :=
  if base = 16 then (if upper then hexNatU n else hexNat n) else decimalNat n

/-- What `fmtInteger` writes for the width `w` of zero padding (`%0Nd`; 0 for none): the digits
of `z` in base `base` (`digitsIn`) with leading zeros up to width `w`, the sign of a negative `z`
before the zeros (and counted in the width). `intOut base w z` for lowercase digits
(`widthPad_false`). -/
def widthPad (base : Nat) (upper : Bool) (w : Nat) (z : Int) : GoString :=
  if z < 0 then W8 45 :: padZeros (w - 1) (digitsIn base upper z.natAbs)
  else padZeros w (digitsIn base upper z.natAbs)

/-- What `fmtInteger` writes for the precision `p` (`%.Pd`): the digits of `z` in base `base`
(`digitsIn`) with leading zeros up to `p` digits, the sign of a negative `z` before them; nothing
for `z = 0` at precision 0. -/
def precPad (base : Nat) (upper : Bool) (p : Nat) (z : Int) : GoString :=
  if p = 0 ∧ z = 0 then []
  else if z < 0 then W8 45 :: padZeros p (digitsIn base upper z.natAbs)
  else padZeros p (digitsIn base upper z.natAbs)

/-- The base `fmtInteger` formats the integer verb `v` in: 16 for `x` and `X`, 10 otherwise. -/
def verbBase (v : w8) : Nat := if v = verb_x ∨ v = verb_X then 16 else 10

/-- The digits `fmt` takes for hexadecimal: `ldigits` (`upper` false) or `udigits`. -/
def hexDigits (upper : Bool) : GoString :=
  if upper then go!"0123456789ABCDEFX" else go!"0123456789abcdefx"

/-- `<nil>`. -/
def nilAngle : GoString := go!"<nil>"

/-- `DirOut zw verb a out`: Go writes `out` for the directive (`%verb`, or `%0Nverb` for
`zw = some N`) of the argument `a`. -/
inductive DirOut : Option Nat → w8 → Arg → GoString → Prop
  | nil_v : DirOut none verb_v .nil nilAngle
  | bool_v (b : Bool) : DirOut none verb_v (.bool b) (if b then go!"true" else go!"false")
  | bool_t (b : Bool) : DirOut none verb_t (.bool b) (if b then go!"true" else go!"false")
  | int_d (zw : Option Nat) (z : Int) : DirOut zw verb_d (.int z) (decimalPad (zw.getD 0) z)
  | int_v (zw : Option Nat) (z : Int) : DirOut zw verb_v (.int z) (decimalPad (zw.getD 0) z)
  | int_x (zw : Option Nat) (z : Int) : DirOut zw verb_x (.int z) (hexPad (zw.getD 0) z)
  | str_s (s : GoString) : DirOut none verb_s (.str s) s
  | str_v (s : GoString) : DirOut none verb_v (.str s) s
  | str_x (s : GoString) : DirOut none verb_x (.str s) (bytesHex false s)
  /-- `%q` writes `s` double-quoted as a Go literal (`strconv.Quote`), of which `strconv`'s spec
  says nothing more: any string. -/
  | str_q (s o : GoString) : DirOut none verb_q (.str s) o
  | bytes_s (bs : GoString) (dq : DFrac) : DirOut none verb_s (.bytes bs dq) bs
  | bytes_v (bs : GoString) (dq : DFrac) : DirOut none verb_v (.bytes bs dq) (bytesDec bs)
  | bytes_d (bs : GoString) (dq : DFrac) : DirOut none verb_d (.bytes bs dq) (bytesDec bs)
  | bytes_x (bs : GoString) (dq : DFrac) : DirOut none verb_x (.bytes bs dq) (bytesHex false bs)
  | method_s (P : GoString → Prop) (s : GoString) : P s → DirOut none verb_s (.method P) s
  | method_v (P : GoString → Prop) (s : GoString) : P s → DirOut none verb_v (.method P) s
  | method_x (P : GoString → Prop) (s : GoString) :
      P s → DirOut none verb_x (.method P) (bytesHex false s)
  /-- `%q` of the method's result `s`: as `str_q`, any string. -/
  | method_q (P : GoString → Prop) (s o : GoString) : P s → DirOut none verb_q (.method P) o

/-- What `pp.fmtString` writes for the verb `verb` (`s`, `v`, `x` or `q`, without flags) of the
string `s`: `s` itself (`s`, `v`), its hexadecimal (`x`), or, for `q`, any string (`DirOut.str_q`). -/
def StrOut (verb : w8) (s o : GoString) : Prop :=
  verb = verb_q ∨ o = if verb = verb_x then bytesHex false s else s

/-- `PrecOut p verb a out`: Go writes `out` for the directive `%.Pverb` of the argument `a`. -/
inductive PrecOut : Nat → w8 → Arg → GoString → Prop
  | int (p : Nat) (v : w8) (z : Int) :
      PrecOut p v (.int z) (precPad (verbBase v) (decide (v = verb_X)) p z)

/-- `Out ps as out`: `Sprintf(encode ps, as...)` returns `out` (given `Fits ps as`): the pieces'
outputs in order, a directive's from the next argument. -/
inductive Out : List Piece → List Arg → GoString → Prop
  | nil : Out [] [] []
  | lit (s : GoString) (ps : List Piece) (args : List Arg) (out : GoString) :
      Out ps args out → Out (.lit s :: ps) args (s ++ out)
  | percent (ps : List Piece) (args : List Arg) (out : GoString) :
      Out ps args out → Out (.percent :: ps) args (W8 37 :: out)
  | dir (zw : Option Nat) (v : w8) (a : Arg) (o : GoString) (ps : List Piece) (args : List Arg)
      (out : GoString) :
      DirOut zw v a o → Out ps args out → Out (.dir zw v :: ps) (a :: args) (o ++ out)
  | prec (p : Nat) (v : w8) (a : Arg) (o : GoString) (ps : List Piece) (args : List Arg)
      (out : GoString) :
      PrecOut p v a o → Out ps args out → Out (.prec p v :: ps) (a :: args) (o ++ out)

/-! ## `parsenum` -/

/-- The loop of `parsenum(s, start, e)` from index `i`, with the number `num` read so far
(`isnum`: a digit was read): it reads decimal digits before `e`, giving up (`(0, false, e)`) at a
digit once the number is above `10^6` (`tooLarge`). The number, whether there was one, and the
index after it. -/
def parsenumLoop (s : GoString) (e : Nat) (i num : Nat) (isnum : Bool) : Nat × Bool × Nat :=
  if i < e then
    match s[i]? with
    | some c =>
      if 48 ≤ uint.nat c ∧ uint.nat c ≤ 57 then
        if 1000000 < num then (0, false, e)
        else parsenumLoop s e (i + 1) (num * 10 + (uint.nat c - 48)) true
      else (num, isnum, i)
    | none => (num, isnum, i)
  else (num, isnum, i)
termination_by e - i

/-- What `parsenum(s, start, e)` returns. -/
def parsenumSpec (s : GoString) (start e : Nat) : Nat × Bool × Nat :=
  if e ≤ start then (0, false, e) else parsenumLoop s e start 0 false

/-! ## Which Go values the arguments are -/

section args
variable [GooseExts] [GoLocalContext] [GoGlobalContext] [GoSemanticsFunctions]

/-- `IntArg x z`: `x` holds the integer `z`, of one of Go's predeclared integer types (signed for
`int`, ..., `int8`; unsigned for `uint`, ..., `uint8`, `uintptr`), the types `printArg`'s type
switch formats with `fmtInteger`. -/
inductive IntArg : GoInterface → Int → Prop
  | int (n : w64) : IntArg (interface.mkOk go.int #n) (sint.Z n)
  | int64 (n : w64) : IntArg (interface.mkOk go.int64 #n) (sint.Z n)
  | int32 (n : w32) : IntArg (interface.mkOk go.int32 #n) (sint.Z n)
  | int16 (n : w16) : IntArg (interface.mkOk go.int16 #n) (sint.Z n)
  | int8 (n : w8) : IntArg (interface.mkOk go.int8 #n) (sint.Z n)
  | uint (n : w64) : IntArg (interface.mkOk go.uint #n) (uint.Z n)
  | uint64 (n : w64) : IntArg (interface.mkOk go.uint64 #n) (uint.Z n)
  | uint32 (n : w32) : IntArg (interface.mkOk go.uint32 #n) (uint.Z n)
  | uint16 (n : w16) : IntArg (interface.mkOk go.uint16 #n) (uint.Z n)
  | uint8 (n : w8) : IntArg (interface.mkOk go.uint8 #n) (uint.Z n)
  | uintptr (n : w64) : IntArg (interface.mkOk go.uintptr #n) (uint.Z n)

/-- The types `printArg`'s type switch formats itself (before trying methods or reflection). -/
def SwitchType (t : go.GoType) : Prop :=
  t = go.bool ∨ t = go.float32 ∨ t = go.float64 ∨ t = go.complex64 ∨ t = go.complex128 ∨
  t = go.int ∨ t = go.int8 ∨ t = go.int16 ∨ t = go.int32 ∨ t = go.int64 ∨
  t = go.uint ∨ t = go.uint8 ∨ t = go.uint16 ∨ t = go.uint32 ∨ t = go.uint64 ∨ t = go.uintptr ∨
  t = go.string ∨ t = go.GoType.SliceType go.byte ∨ t = reflect.Value.ty

/-- `MethodArg ii m`: Go formats `ii` under `%s`, `%v` or `%x` by calling its method `m`
(`handleMethods`): its type is not one the type switch formats itself, it is not a `Formatter`,
and `m` is `Error` if it is an `error`, otherwise `String`, of a `Stringer`. -/
def MethodArg (ii : GoInterfaceOk) (m : GoString) : Prop :=
  ¬ SwitchType ii.ty ∧ go.typeSetContains ii.ty Formatter.ty = false ∧
  ((m = go!"Error" ∧ go.typeSetContains ii.ty go.error = true) ∨
   (m = go!"String" ∧ go.typeSetContains ii.ty go.error = false ∧
     go.typeSetContains ii.ty Stringer.ty = true))

end args

section iprops
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The method `m` of `ii`, called with no arguments, returns some string `s` with `P s`, needing
nothing (persistently). -/
def methodSpec (ii : GoInterfaceOk) (m : GoString) (P : GoString → Prop) : IProp GF :=
  iprop(□ ∀ Φ : val → IProp GF, ▷ (∀ s : GoString, ⌜P s⌝ -∗ Φ #s) -∗
    WP (App (Val #(methods ii.ty m ii.v)) (Val #())) {{ Φ }})

instance methodSpec_persistent (ii : GoInterfaceOk) (m : GoString) (P : GoString → Prop) :
    Persistent (methodSpec (GF := GF) ii m P) := by
  unfold methodSpec; infer_instance

/-- The Go value `x` is the argument `a`: what `Sprintf` needs of it (a `[]byte`'s contents, the
spec of a method it calls). -/
def isArg (x : GoInterface) : Arg → IProp GF
  | .nil => iprop(⌜x = interface.nil⌝)
  | .bool b => iprop(⌜x = interface.mkOk go.bool #b⌝)
  | .int z => iprop(⌜IntArg x z⌝)
  | .str s => iprop(⌜x = interface.mkOk go.string #s⌝)
  | .bytes bs dq => iprop(∃ sl : GoSlice,
      ⌜x = interface.mkOk (go.GoType.SliceType go.byte) #sl⌝ ∗ sl ↦*{dq} bs)
  | .method P => iprop(∃ (ii : GoInterfaceOk) (m : GoString),
      ⌜x = interface.ok ii ∧ MethodArg ii m⌝ ∗ methodSpec ii m P)

/-! ## The printer -/

/-- The buffer at `b` (a `*buffer`: a printer's field `buf`, which its `fmt.buf` points to)
holds the bytes `bs`, and owns its backing array's capacity. -/
def bufferOwn (b : Loc) (bs : GoString) : IProp GF :=
  iprop(∃ sl : GoSlice, b ↦ (sl : buffer) ∗ sl ↦* bs ∗ ownSliceCap w8 sl (DFrac.own 1))

/-- The `fmt` at `f` writes to the buffer at `b`, with the flags `F`, the width `wid` and the
precision `prec`: its fields but `intbuf` (`intbufOwn`), which `fmtInteger` formats into while
it calls `pad` on a slice of it. -/
def fmtOwn (f b : Loc) (F : fmtFlags) (wid prec : w64) : IProp GF :=
  iprop(f.[fmt.fmt, go!"buf"] ↦ b ∗ f.[fmt.fmt, go!"fmtFlags"] ↦ F ∗
    f.[fmt.fmt, go!"wid"] ↦ wid ∗ f.[fmt.fmt, go!"prec"] ↦ prec)

/-- The scratch array `intbuf` of the `fmt` at `f`, holding anything. -/
def intbufOwn (f : Loc) : IProp GF :=
  iprop(∃ ib : GoArray w8 68, f.[fmt.fmt, go!"intbuf"] ↦ ib)

/-- No flag set (`clearflags`). -/
def noFlags : fmtFlags := ⟨false, false, false, false, false, false, false, false, false⟩

/-- The flags of the directive `%verb` (`zw = none`) or `%0Nverb` (`zw = some N`) when `doPrintf`
calls `printArg`: `zero` and `widPresent` for `%0N`; `sharpV` and `plusV` (set for `%v` from
`sharp` and `plus`) false. -/
def dirFlags : Option Nat → fmtFlags
  | none => noFlags
  | some _ => { noFlags with widPresent' := true, zero' := true }

/-- The width of the directive `%verb` (`zw = none`: 0) or `%0Nverb` (`N`). -/
def dirWid (zw : Option Nat) : w64 := W64 (zw.getD 0)

/-- What a directive of the verified subset puts between the `%` and the verb: nothing or a zero
width (`width zw`: `%verb`, `%0Nverb`, `Piece.dir`), or a precision (`prec p`: `%.Pverb`,
`Piece.prec`). -/
inductive Mod where
  | width (zw : Option Nat)
  | prec (p : Nat)

/-- The flags `doPrintf` sets for the directive when it calls `printArg`: `dirFlags` for a width,
`precPresent` alone for a precision. -/
def Mod.flags : Mod → fmtFlags
  | .width zw => dirFlags zw
  | .prec _ => { noFlags with precPresent' := true }

/-- The width `doPrintf` sets for the directive (`parsenum` gives 0 when there is none). -/
def Mod.wid : Mod → w64
  | .width zw => dirWid zw
  | .prec _ => W64 0

/-- The precision `doPrintf` sets for the directive (0 when there is none). -/
def Mod.precW : Mod → w64
  | .width _ => W64 0
  | .prec p => W64 p

/-- The directive is in the verified subset (`DirOk`, `PrecOk`). -/
def Mod.Ok : Mod → w8 → Arg → Prop
  | .width zw => DirOk zw
  | .prec p => PrecOk p

/-- What Go writes for the directive (`DirOut`, `PrecOut`). -/
def Mod.Out : Mod → w8 → Arg → GoString → Prop
  | .width zw => DirOut zw
  | .prec p => PrecOut p

/-- The integer directives of the verified subset: `%d %v %x`, zero-padded to a width of at most
`10^6`, or `%d %v %x %X` with a precision of at most `10^6`. -/
def Mod.IntOk : Mod → w8 → Prop
  | .width zw, v => (v = verb_d ∨ v = verb_v ∨ v = verb_x) ∧ ZeroWidthOk zw
  | .prec p, v => (v = verb_d ∨ v = verb_v ∨ v = verb_x ∨ v = verb_X) ∧ p ≤ 1000000

/-- What Go writes for the integer directive of `z` (`Mod.IntOk`). -/
def Mod.intOut : Mod → w8 → Int → GoString
  | .width zw, v, z => widthPad (verbBase v) (decide (v = verb_X)) (zw.getD 0) z
  | .prec p, v, z => precPad (verbBase v) (decide (v = verb_X)) p z

/-- The printer at `p` (a `*pp` that `newPrinter` returned), its field `arg` holding `x`, its
buffer holding `bs`, its `fmt` the flags `F`, width `wid` and precision `prec`: the struct's
fields, with `panicking`, `erroring` and `wrapErrs` false, and the backing array of
`wrappedErrs`. -/
def isPrinterA (p : Loc) (x : GoInterface) (bs : GoString) (F : fmtFlags) (wid prec : w64) :
    IProp GF :=
  iprop(bufferOwn (p.[pp, go!"buf"]) bs ∗
    fmtOwn (p.[pp, go!"fmt"]) (p.[pp, go!"buf"]) F wid prec ∗
    intbufOwn (p.[pp, go!"fmt"]) ∗
    p.[pp, go!"arg"] ↦ x ∗
    (∃ v : reflect.Value, p.[pp, go!"value"] ↦ v) ∗
    (∃ b : Bool, p.[pp, go!"reordered"] ↦ b) ∗
    (∃ b : Bool, p.[pp, go!"goodArgNum"] ↦ b) ∗
    p.[pp, go!"panicking"] ↦ false ∗
    p.[pp, go!"erroring"] ↦ false ∗
    p.[pp, go!"wrapErrs"] ↦ false ∗
    (∃ (sl : GoSlice) (ws : List w64), p.[pp, go!"wrappedErrs"] ↦ sl ∗ sl ↦* ws ∗
      ownSliceCap w64 sl (DFrac.own 1)))

/-- `isPrinterA`, whatever the field `arg` holds. -/
def isPrinter (p : Loc) (bs : GoString) (F : fmtFlags) (wid prec : w64) : IProp GF :=
  iprop(∃ x : GoInterface, isPrinterA p x bs F wid prec)

/-- `isPrinter`, whatever the flags, width and precision, of a printer at a non-`nil` address,
whose `fmt` is not at `nil` either (what `pp.free` needs to give the whole struct back to the
pool, `ppFreeElem`: a typed points-to of a struct says its address is not `nil`; the field
points-tos of `isPrinterA` don't). -/
def isPrinterAny (p : Loc) (bs : GoString) : IProp GF :=
  iprop(⌜p ≠ null ∧ p.[pp, go!"fmt"] ≠ null⌝ ∗
    ∃ (F : fmtFlags) (wid prec : w64), isPrinter p bs F wid prec)

end iprops

end fmt

end Perennial
