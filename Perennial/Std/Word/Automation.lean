/-
The `word` tactic. Port of `src/Helpers/Word/Automation.v`.

Rocq's `word` turns word arithmetic into `Z` arithmetic (`uint.Z (word.add x y)`
becomes `wrap (uint.Z x + uint.Z y)`) and calls `lia`. Here words are
`BitVec n`, `uint.Z x = (x.toNat : Int)` and `sint.Z x = x.toInt`, so `word`:

1. unfolds `uint.Z`, `sint.Z`, `W64`, ... and everything tagged `@[word_unfold]`
   (Rocq: `Hint Unfold foo : word`);
2. for every `BitVec.toInt t` in the goal or context, adds the fact relating it
   to `t.toNat` (`sint_Z_cases`), so signed values become linear in the
   unsigned ones;
3. rewrites `toNat` of BitVec operations into `Nat` arithmetic with `% 2^n`
   (the `bitvec_to_nat` simp set of `bv_omega`, without its `toInt` rules);
4. calls `omega`.

If that fails it tries `bv_decide` (bit-blasting; good for bitwise ops on
concrete widths, where `omega` is helpless).

Like Rocq's `word`, it is good at linear arithmetic (`x + y`, `4 * x`, `x / 8`,
`x % 8`), treats non-linear products as atoms, and does not understand
bitwise operations unless `bv_decide` can do the whole goal.

`word` closes the goal or fails. For a non-terminal version use `word_simp`,
which rewrites `uint.Z` of arithmetic ops into `Int` arithmetic, discharging
no-overflow side conditions with `word`.
-/
import Perennial.Std.Word
import Perennial.Std.Attrs

namespace Perennial

/-- The signed value in terms of the unsigned one. -/
theorem sint_Z_cases {n : Nat} (x : BitVec n) :
    (2 * x.toNat < 2 ^ n ∧ x.toInt = (x.toNat : Int)) ∨
    (2 ^ n ≤ 2 * x.toNat ∧ x.toInt = (x.toNat : Int) - (2 ^ n : Nat)) := by
  rw [BitVec.toInt_eq_toNat_cond]
  by_cases h : 2 * x.toNat < 2 ^ n
  · left; simp [h]
  · right; simp only [h, ite_false]; refine ⟨by omega, ?_⟩; simp

namespace word

open Lean Elab Tactic Meta

/-- Collect the subterms `BitVec.toInt t` of `e` (without loose bound variables). -/
partial def collectToInt (e : Expr) (acc : Array Expr) : Array Expr :=
  let acc :=
    if e.isAppOfArity ``BitVec.toInt 2 && !e.hasLooseBVars && !acc.contains e then acc.push e
    else acc
  match e with
  | .app f a => collectToInt a (collectToInt f acc)
  | .lam _ t b _ => collectToInt b (collectToInt t acc)
  | .forallE _ t b _ => collectToInt b (collectToInt t acc)
  | .letE _ t v b _ => collectToInt b (collectToInt v (collectToInt t acc))
  | .mdata _ b => collectToInt b acc
  | .proj _ _ b => collectToInt b acc
  | _ => acc

/-- Does `e` mention an Iris entailment (an Iris proof mode goal, a spec, ...)? -/
def mentionsEntailment (e : Expr) : Bool :=
  (e.find? fun s => match s with
    | .const n _ => n == `Iris.BI.BIBase.Entails || n == `Iris.ProofMode.Entails' ||
        n == `Iris.Wp.wp
    | _ => false).isSome

/-- Add `sint_Z_cases t` for every `BitVec.toInt t` in the goal and context.
Each fact is a case split for `omega`, so when there are more than ten such
terms only those of the goal and of the hypotheses connected to the goal through
shared free variables are used. Hypotheses mentioning
Iris entailments are ignored. -/
elab "word_sint_facts" : tactic => withMainContext do
  let maxAll := 10
  let tgt ← instantiateMVars (← getMainTarget)
  let mut hyps : Array Expr := #[]
  for h in ← getLCtx do
    unless h.isImplementationDetail do
      let ty ← instantiateMVars h.type
      unless mentionsEntailment ty do hyps := hyps.push ty
  let mut ts : Array Expr := #[]
  for ty in hyps do ts := collectToInt ty ts
  ts := collectToInt tgt ts
  if ts.size > maxAll then
    -- only the relevant ones: those of the goal and of the hypotheses connected to
    -- the goal through shared free variables (transitively)
    let mut vars : Std.HashSet FVarId := {}
    for x in (collectFVars {} tgt).fvarSet.toList do vars := vars.insert x
    let mut relevant : Array Bool := hyps.map fun _ => false
    let mut changed := true
    while changed do
      changed := false
      for h : i in [:hyps.size] do
        if relevant[i]! then continue
        let fvs := (collectFVars {} hyps[i]).fvarSet.toList
        if fvs.any vars.contains then
          relevant := relevant.set! i true
          changed := true
          for x in fvs do vars := vars.insert x
    let mut ts' := collectToInt tgt #[]
    for h : i in [:hyps.size] do
      if relevant[i]! then ts' := collectToInt hyps[i] ts'
    ts := ts'
  for t in ts do
    let pf ← mkAppM ``sint_Z_cases #[t.appArg!]
    let ty ← inferType pf
    liftMetaTactic fun g => do
      let (_, g) ← (← g.assert `hsint ty pf).intro1P
      return [g]

end word

/-- Preprocessing of `word`: everything to `Nat`/`Int` arithmetic. -/
macro "word_prep" : tactic => `(tactic| (
  (try simp only [uint.Z, uint.nat, sint.Z, sint.nat, W64, W32, W16, W8, word_unfold] at *)
  word_sint_facts
  (try simp -implicitDefEqProofs only [BitVec.toNat_ofNat, BitVec.toNat_ofFin,
      BitVec.toNat_setWidth, BitVec.toNat_neg, BitVec.ofNat_eq_ofNat, BitVec.toNat_eq,
      BitVec.toNat_ne, BitVec.toNat_ofInt, BitVec.toNat_not, BitVec.toNat_shiftLeft,
      BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_mul,
      BitVec.le_def, BitVec.lt_def, BitVec.toNat_udiv, BitVec.toNat_umod, BitVec.toNat_twoPow,
      BitVec.toNat_cast, BitVec.toNat_ofNatLT, BitVec.toNat_ofBool,
      Int.toNat_natCast, Int.natCast_pow] at *)))

/-- Reduce arithmetic on literals left by `word_prep` (e.g. `x / (2 % 2^64)`,
`(W64 3).toNat`) and shifts by literals, at the hypotheses and the goal. -/
macro "word_lit_reduce" : tactic => `(tactic|
  (try simp only [Nat.reduceMod, Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceAdd,
    Nat.reduceSub, Int.reduceMod, Int.reducePow, Int.reduceDiv, Int.reduceMul, Int.reduceAdd,
    Int.reduceSub, Int.reduceToNat, Int.reduceNeg, Int.reduceNatCast, Int.reduceNatCast', Int.reduceOfNat,
    Int.natCast_pow, BitVec.toNat_udiv, BitVec.toNat_umod,
    BitVec.toNat_ofNat, BitVec.toNat_ofInt, BitVec.ushiftRight_eq', BitVec.shiftLeft_eq',
    BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftRight_eq_div_pow,
    Nat.shiftLeft_eq] at *))

open Lean Elab Tactic Meta in
/-- Fails unless the goal mentions a bitwise operation (where `bv_decide` may help). -/
elab "word_bitwise_goal" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let ops := [``HAnd.hAnd, ``HOr.hOr, ``HXor.hXor, ``Complement.complement, ``HShiftLeft.hShiftLeft,
    ``HShiftRight.hShiftRight, ``BitVec.sshiftRight, ``BitVec.sdiv, ``BitVec.smod, ``BitVec.srem]
  unless (tgt.find? fun s => match s with
      | .const n _ => ops.contains n
      | _ => false).isSome do
    throwError "word: not a bitwise goal"

/-- Solve word-arithmetic goals (Rocq `word`). See the module docstring.

`word` first tries `word_prep; omega`, then the same after reducing literal
arithmetic and shifts by literals (`word_lit_reduce`), then plain `omega`, then
`bv_decide` with a 3 second SAT timeout (previously 10). Only the `toInt` facts
relevant to the goal are added when there are many (`word_sint_facts`). -/
syntax "word" : tactic
macro_rules
  | `(tactic| word) => `(tactic| first
      | (word_prep; omega)
      | (word_prep; word_lit_reduce; (try omega); done)
      | omega
      | bv_decide (timeout := 3))

/-! ## Rewriting lemmas for `uint.Z` / `sint.Z` of operations

Names follow coqutil (`word.unsigned_add`, ...). The `_nowrap` versions have a
no-overflow hypothesis and are tagged `@[word_nowrap]`... (see `word_simp`). -/

namespace word

variable {n : Nat}

theorem unsigned_add (x y : BitVec n) : uint.Z (x + y) = (uint.Z x + uint.Z y) % 2 ^ n := by
  simp only [uint.Z, BitVec.toNat_add]; push_cast; rfl

theorem unsigned_sub (x y : BitVec n) :
    uint.Z (x - y) = (uint.Z x - uint.Z y) % 2 ^ n := by
  simp only [uint.Z, BitVec.toNat_sub]
  have := x.isLt; have := y.isLt
  rw [Int.natCast_emod, Int.natCast_add, Int.natCast_sub (by omega)]
  push_cast
  rw [show (2:Int)^n - y.toNat + x.toNat = (x.toNat - y.toNat) + 2^n by omega, Int.add_emod_right]

theorem unsigned_mul (x y : BitVec n) : uint.Z (x * y) = (uint.Z x * uint.Z y) % 2 ^ n := by
  simp only [uint.Z, BitVec.toNat_mul]; push_cast; rfl

theorem unsigned_of_Z (z : Int) : uint.Z (BitVec.ofInt n z) = z % 2 ^ n := by
  simp only [uint.Z, BitVec.toNat_ofInt]
  have : (0 : Int) < 2 ^ n := Int.pow_pos (by decide)
  rw [Int.natCast_pow, Int.toNat_of_nonneg (Int.emod_nonneg _ (Int.ne_of_gt (by simpa using this)))]; rfl

theorem unsigned_of_Z_nowrap (z : Int) (h0 : 0 ≤ z) (h1 : z < 2 ^ n) :
    uint.Z (BitVec.ofInt n z) = z := by
  rw [unsigned_of_Z, Int.emod_eq_of_lt h0 h1]

theorem unsigned_divu (x y : BitVec n) : uint.Z (x / y) = uint.Z x / uint.Z y := by
  simp only [uint.Z, BitVec.toNat_udiv]; push_cast; rfl

theorem unsigned_modu (x y : BitVec n) : uint.Z (x % y) = uint.Z x % uint.Z y := by
  simp only [uint.Z, BitVec.toNat_umod]; push_cast; rfl

theorem unsigned_add_nowrap (x y : BitVec n) (h : uint.Z x + uint.Z y < 2 ^ n) :
    uint.Z (x + y) = uint.Z x + uint.Z y := by
  rw [unsigned_add, Int.emod_eq_of_lt (by simp only [uint.Z]; omega) h]

theorem unsigned_sub_nowrap (x y : BitVec n) (h : uint.Z y ≤ uint.Z x) :
    uint.Z (x - y) = uint.Z x - uint.Z y := by
  rw [unsigned_sub, Int.emod_eq_of_lt (by omega)]
  have := uint_Z_lt x; have := uint_Z_nonneg y; omega

theorem unsigned_mul_nowrap (x y : BitVec n) (h : uint.Z x * uint.Z y < 2 ^ n) :
    uint.Z (x * y) = uint.Z x * uint.Z y := by
  rw [unsigned_mul, Int.emod_eq_of_lt (Int.mul_nonneg (uint_Z_nonneg x) (uint_Z_nonneg y)) h]

theorem unsigned_inj {x y : BitVec n} (h : uint.Z x = uint.Z y) : x = y := uint_Z_inj.mp h

theorem unsigned_range (x : BitVec n) : 0 ≤ uint.Z x ∧ uint.Z x < 2 ^ n :=
  ⟨uint_Z_nonneg x, uint_Z_lt x⟩

theorem signed_range (x : BitVec n) :
    -(2 ^ (n - 1) : Int) ≤ sint.Z x ∧ sint.Z x < 2 ^ (n - 1) := by
  simp only [sint.Z]
  exact ⟨BitVec.le_toInt x, BitVec.toInt_lt⟩

/-- coqutil `word.word_eq_iff_Z_eq` -/
theorem word_eq_iff_Z_eq {x y : BitVec n} : x = y ↔ uint.Z x = uint.Z y := uint_Z_inj.symm

/-- Rocq `Automation.word.word_signed_divs_nowrap_pos` (signed division of
non-negative by positive). -/
theorem word_signed_divs_nowrap_pos (x y : BitVec n) (h : 0 < sint.Z y ∧ 0 ≤ sint.Z x) :
    sint.Z (x.sdiv y) = sint.Z x / sint.Z y := by
  simp only [sint.Z] at *
  rw [BitVec.toInt_sdiv]
  rcases n with _ | n
  · simp [BitVec.eq_nil y] at h
  · have hx := BitVec.toInt_lt (x := x)
    have hd : x.toInt.tdiv y.toInt ≤ x.toInt := by
      rw [Int.tdiv_eq_ediv_of_nonneg h.2]; exact Int.ediv_le_self _ h.2
    have hd0 : 0 ≤ x.toInt.tdiv y.toInt := by
      rw [Int.tdiv_eq_ediv_of_nonneg h.2]; exact Int.ediv_nonneg h.2 (by omega)
    simp only [Nat.add_sub_cancel] at hx
    push_cast at hx
    rw [Int.bmod_eq_of_le, Int.tdiv_eq_ediv_of_nonneg h.2]
    all_goals (push_cast; rw [Int.pow_succ]; omega)

end word

/-- Rewrite `uint.Z` of word operations into `Int` arithmetic, using the
no-overflow lemmas when `word` can prove their side condition, and the
wrapping (`% 2^n`) lemmas otherwise is *not* attempted. Does not close goals
by itself. -/
macro "word_simp" : tactic => `(tactic|
  simp (disch := word) only [word.unsigned_add_nowrap, word.unsigned_sub_nowrap,
    word.unsigned_mul_nowrap, word.unsigned_of_Z_nowrap, word.unsigned_divu,
    word.unsigned_modu])

/-- Rocq `nat_cleanup`. -/
macro "nat_cleanup" : tactic => `(tactic|
  (try simp only [Int.toNat_natCast, Int.toNat_of_nonneg, uint.Z, uint.nat]))

section tests

example (x y : w64) (h : uint.Z x + uint.Z y < 2^64) : uint.Z (x + y) = uint.Z x + uint.Z y := by
  word

example (x y : w64) : uint.Z (x + y) < uint.Z x ↔ uint.Z x + uint.Z y ≥ 2^64 := by word

example (x : w64) (h : 0 ≤ sint.Z x) : uint.Z x = sint.Z x := by word

example (x : w64) (h : uint.Z x < 10) : sint.Z (x + 1) = sint.Z x + 1 := by word

example (z : Int) (h : 0 ≤ z) (h2 : z < 2^64) : uint.Z (W64 z) = z := by word

example (x y : w64) (h : uint.Z y ≤ uint.Z x) : uint.Z (x - y) = uint.Z x - uint.Z y := by word

example (x : w64) (h : x ≠ 0) : 0 < uint.Z x := by word

example (x : w8) : x &&& 0 = 0 := by word

example (x y : w64) (h : uint.Z x + uint.Z y < 2^64) :
    uint.Z (x + y) + 1 = uint.Z x + uint.Z y + 1 := by
  word_simp

example (x : w64) (h : uint.Z x < 100) : uint.Z (x * 4) = 4 * uint.Z x := by word

example (x : w64) (h : uint.Z x < 100) : uint.nat (x + 1) = uint.nat x + 1 := by word

end tests

end Perennial
