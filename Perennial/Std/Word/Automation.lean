/-
The `word` tactic. Port of `src/Helpers/Word/Automation.v`.

Rocq's `word` turns word arithmetic into `Z` arithmetic (`uint.Z (word.add x y)`
becomes `wrap (uint.Z x + uint.Z y)`) and calls `lia`. Here words are
`BitVec n`, `uint.Z x = (x.toNat : Int)` and `sint.Z x = x.toInt`.

`word` (see `word_fast`) does:

1. drop hypotheses that mention Iris entailments (`word_filter iris`);
2. unfold `uint.Z`, `sint.Z`, `W64`, ... and everything tagged `@[word_unfold]`
   (Rocq: `Hint Unfold foo : word`), rewrite sign extensions
   `W64 (sint.Z (x : w32))`, and evaluate word literals (`W64 3` becomes `3#64`,
   `(W64 3).toInt` becomes `3`) (`word_unfold_lit`);
3. drop the hypotheses `omega` cannot use, and the arithmetic hypotheses not
   connected to the goal through shared variables (`word_filter`);
4. for `(x.sdiv y).toInt` with a positive literal `y`, add the case split relating
   it to `x.toInt / y.toInt` (`word_sdiv_facts`);
5. rewrite `toNat` of BitVec operations into `Nat` arithmetic with `% 2^n`, and
   shifts by literals into division/multiplication (`word_tonat`);
6. call `omega`, treating `x.toInt` as an atom: first without the hypotheses
   that make `omega` case split (Nat subtraction, `Int.toNat`, `min`, `≠`, ...;
   `word_filter_simple`; this gives much smaller proofs), then with them;
7. if that fails, add for every `x.toInt` the fact relating it to `x.toNat`
   (`sint_Z_cases`), resolving the case split with a quick `omega` call when
   the context decides the sign and rewriting `x.toInt` away
   (`word_sint_resolve`), and call `omega` again, first without the unresolved
   case splits (`word_drop_cases`).

Only if that fails, the old, unfiltered pipeline (`word_prep; omega`, which
case-splits on the sign of every `toInt` and can be exponential) is tried under
a heartbeat limit, then `omega`, then `bv_normalize` (the kernel-checked
rewriting front end of `bv_decide`; it closes some bitwise goals on concrete
widths, where `omega` is helpless), also bounded. `word` never calls
`bv_decide` itself: its SAT step is trusted via `Lean.ofReduceBool` (native
code), which this port avoids. `word` therefore fails in bounded time instead
of hanging.

Like Rocq's `word`, it is good at linear arithmetic (`x + y`, `4 * x`, `x / 8`,
`x % 8`), treats non-linear products as atoms, and does not understand
bitwise operations unless `bv_normalize` can do the whole goal.

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

theorem sint_Z_pos {n : Nat} (x : BitVec n)
    (h : ¬(2 ^ n ≤ 2 * x.toNat ∧ x.toInt = (x.toNat : Int) - (2 ^ n : Nat))) :
    2 * x.toNat < 2 ^ n ∧ x.toInt = (x.toNat : Int) := (sint_Z_cases x).resolve_right h

theorem sint_Z_neg {n : Nat} (x : BitVec n) (h : ¬(2 * x.toNat < 2 ^ n ∧ x.toInt = (x.toNat : Int))) :
    2 ^ n ≤ 2 * x.toNat ∧ x.toInt = (x.toNat : Int) - (2 ^ n : Nat) := (sint_Z_cases x).resolve_left h

/-- Sign extension: `sint.Z (W64 (sint.Z (x : w32))) = sint.Z x`. -/
theorem toInt_ofInt_toInt {m n : Nat} (x : BitVec m) (h : m ≤ n) :
    (BitVec.ofInt n x.toInt).toInt = x.toInt := BitVec.toInt_signExtend_of_le h

/-- Signed division by a positive divisor, in terms of `Int` (floor) division. -/
theorem sdiv_cases {n : Nat} (x y : BitVec n) (hy : 0 < y.toInt) :
    (0 ≤ x.toInt ∧ (x.sdiv y).toInt = x.toInt / y.toInt) ∨
    (x.toInt < 0 ∧ (x.sdiv y).toInt = -((-x.toInt) / y.toInt)) := by
  rw [BitVec.toInt_sdiv]
  rcases n with _ | n
  · simp [BitVec.eq_nil y] at hy
  have hx1 := BitVec.le_toInt x
  have hx2 := BitVec.toInt_lt (x := x)
  simp only [Nat.add_sub_cancel] at hx1 hx2
  push_cast at hx1 hx2
  have hp : (2:Int) ^ (n + 1) = 2 * 2 ^ n := by rw [Int.pow_succ]; omega
  by_cases h : 0 ≤ x.toInt
  · left
    refine ⟨h, ?_⟩
    rw [Int.tdiv_eq_ediv_of_nonneg h]
    have := Int.ediv_le_self y.toInt h
    have := Int.ediv_nonneg h (Int.le_of_lt hy)
    rw [Int.bmod_eq_of_le] <;> push_cast <;> omega
  · right
    refine ⟨by omega, ?_⟩
    have h' : 0 ≤ -x.toInt := by omega
    rw [show x.toInt = -(-x.toInt) by omega, Int.neg_tdiv, Int.tdiv_eq_ediv_of_nonneg h', Int.neg_neg]
    have := Int.ediv_le_self y.toInt h'
    have := Int.ediv_nonneg h' (Int.le_of_lt hy)
    rw [Int.bmod_eq_of_le] <;> push_cast <;> omega

/-! ## Word literals -/

namespace word
open Lean Meta

/-- A word literal `BitVec.ofInt n z` / `BitVec.ofNat n k` (also through `W64`
and friends) as `(n, value)`. -/
def wordLit? (b : Expr) : MetaM (Option (Nat × Nat)) := do
  let b ← whnfR b
  if let some (n, z) ← (do
      let_expr BitVec.ofInt n z := b | return none
      let some n ← (Meta.evalNat n).run | return none
      let some z ← getIntValue? z | return none
      return some (n, z)) then
    return some (n, (BitVec.ofInt n z).toNat)
  if let some r ← (do
      let_expr BitVec.ofNat n k := b | return none
      let some n ← (Meta.evalNat n).run | return none
      let some k ← (Meta.evalNat k).run | return none
      return some (n, (BitVec.ofNat n k).toNat)) then
    return some r
  -- `OfNat` literals `7#64` / `(7 : w64)`
  let_expr OfNat.ofNat ty k _ := b | return none
  let ty ← whnfR ty
  let_expr BitVec n := ty | return none
  let some n ← (Meta.evalNat n).run | return none
  let some k ← (Meta.evalNat k).run | return none
  return some (n, (BitVec.ofNat n k).toNat)

/-- Evaluate `toInt`/`toNat` of a word literal (`sint.Z (W64 7) = 7`,
`uint.nat (W64 0) = 0`, `sint.nat (W64 3) = 3`, ...), by reduction. -/
def evalWordLitConv (e : Expr) : MetaM Simp.Step :=
  tryCatchRuntimeEx (evalWordLitConvCore e) fun _ => return .continue
where evalWordLitConvCore (e : Expr) : MetaM Simp.Step := do
  let e' ← whnfR e
  let r : Option Expr ← do
    match_expr e' with
    | NatCast.natCast _ _ x =>
      let x ← whnfR x
      let_expr BitVec.toNat _ b := x | pure none
      let some (_, v) ← wordLit? b | pure none
      pure (some (toExpr (v : Int)))
    | Nat.cast _ _ x =>
      let x ← whnfR x
      let_expr BitVec.toNat _ b := x | pure none
      let some (_, v) ← wordLit? b | pure none
      pure (some (toExpr (v : Int)))
    | BitVec.toInt _ b =>
      let some (n, v) ← wordLit? b | pure none
      pure (some (toExpr (BitVec.ofNat n v).toInt))
    | BitVec.toNat _ b =>
      let some (_, v) ← wordLit? b | pure none
      pure (some (mkNatLit v))
    | Int.ofNat x =>
      let x ← whnfR x
      let_expr BitVec.toNat _ b := x | pure none
      let some (_, v) ← wordLit? b | pure none
      pure (some (toExpr (v : Int)))
    | Int.toNat x =>
      let x ← whnfR x
      let_expr BitVec.toInt _ b := x | pure none
      let some (n, v) ← wordLit? b | pure none
      pure (some (mkNatLit (BitVec.ofNat n v).toInt.toNat))
    | _ => pure none
  let some rE := r | return .continue
  return .done { expr := rE, proof? := some (mkExpectedPropHint (← mkEqRefl rE) (← mkEq e rE)) }

/-- Evaluate `sint.Z`/`uint.Z`/`sint.nat`/`uint.nat` of word literals:
`sint.Z (W64 7) = 7`, `uint.nat 3#64 = 3` (used by `word_lit_simp`; not in the
default simp set). -/
simproc_decl word_lit_sintZ (sint.Z _) := fun e => evalWordLitConv e
simproc_decl word_lit_uintZ (uint.Z _) := fun e => evalWordLitConv e
simproc_decl word_lit_sintNat (sint.nat _) := fun e => evalWordLitConv e
simproc_decl word_lit_uintNat (uint.nat _) := fun e => evalWordLitConv e

end word

/-- `word_lit_simp` evaluates `sint.Z`/`uint.Z`/`sint.nat`/`uint.nat` of word
literals everywhere (e.g. `sint.Z (W64 7)` becomes `7`), keeping `W64 n` itself
(unlike a bare `simp`, which also rewrites `W64 n` to `n#64`, so that the result
no longer matches `W64 n` syntactically, e.g. for `iframe`). -/
macro "word_lit_simp" : tactic => `(tactic| simp only [word.word_lit_sintZ, word.word_lit_uintZ,
  word.word_lit_sintNat, word.word_lit_uintNat] at *)

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
/-- Fails unless the goal mentions a bitwise operation (where `bv_normalize` may help). -/
elab "word_bitwise_goal" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let ops := [``HAnd.hAnd, ``HOr.hOr, ``HXor.hXor, ``Complement.complement, ``HShiftLeft.hShiftLeft,
    ``HShiftRight.hShiftRight, ``BitVec.sshiftRight, ``BitVec.sdiv, ``BitVec.smod, ``BitVec.srem]
  unless (tgt.find? fun s => match s with
      | .const n _ => ops.contains n
      | _ => false).isSome do
    throwError "word: not a bitwise goal"

/-- Unfolding and literal evaluation of `word` (step 2 of the module docstring). -/
macro "word_unfold_lit" : tactic => `(tactic| (
  (try simp (disch := decide) only [uint.Z, uint.nat, sint.Z, sint.nat, W64, W32, W16, W8,
    word_unfold, toInt_ofInt_toInt] at *)
  (try simp only [BitVec.reduceOfInt, BitVec.reduceToInt, BitVec.reduceToNat, Int.reducePow,
    Nat.reducePow, Int.reduceNeg] at *)))

/-- `toNat` of BitVec operations to `Nat` arithmetic, shifts by literals to
division/multiplication, literal arithmetic evaluated (step 5). -/
macro "word_tonat" : tactic => `(tactic|
  (try simp -implicitDefEqProofs only [BitVec.toNat_ofNat, BitVec.toNat_ofFin,
    BitVec.toNat_setWidth, BitVec.toNat_neg, BitVec.ofNat_eq_ofNat, BitVec.toNat_eq,
    BitVec.toNat_ne, BitVec.toNat_ofInt, BitVec.toNat_not, BitVec.toNat_shiftLeft,
    BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_mul,
    BitVec.le_def, BitVec.lt_def, BitVec.toNat_udiv, BitVec.toNat_umod, BitVec.toNat_twoPow,
    BitVec.toNat_cast, BitVec.toNat_ofNatLT, BitVec.toNat_ofBool,
    BitVec.ushiftRight_eq', BitVec.shiftLeft_eq', Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
    Int.toNat_natCast, Int.natCast_pow, Nat.reduceMod, Nat.reducePow, Nat.reduceSub,
    Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Int.reduceMod, Int.reducePow, Int.reduceToNat,
    Int.reduceNeg, Int.reduceNatCast, implies_true, and_true, true_and, and_self, true_implies,
    not_true_eq_false, not_false_eq_true, false_implies, or_true, true_or] at *))

/-- `word_tonat` on the goal only. -/
macro "word_tonat_goal" : tactic => `(tactic|
  (try simp -implicitDefEqProofs only [BitVec.toNat_ofNat, BitVec.toNat_ofFin,
    BitVec.toNat_setWidth, BitVec.toNat_neg, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofInt,
    BitVec.toNat_not, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_add,
    BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_udiv, BitVec.toNat_umod,
    BitVec.toNat_twoPow, BitVec.toNat_cast, BitVec.toNat_ofNatLT, BitVec.toNat_ofBool,
    BitVec.ushiftRight_eq', BitVec.shiftLeft_eq', Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
    Int.toNat_natCast, Int.natCast_pow, Nat.reduceMod, Nat.reducePow, Nat.reduceSub,
    Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Int.reduceMod, Int.reducePow, Int.reduceToNat,
    Int.reduceNeg, Int.reduceNatCast, implies_true, and_true, true_and, and_self, true_implies,
    not_true_eq_false, not_false_eq_true, false_implies, or_true, true_or]))

namespace word
open Lean Elab Tactic Meta

/-- Could `omega` use a hypothesis of this type (after `word_tonat`)? -/
partial def isArithTy (e : Expr) : MetaM Bool := do
  let e ← whnfR e
  if e.isAppOfArity ``Not 1 then return ← isArithTy e.appArg!
  if [``And, ``Or, ``Iff].any (e.isAppOfArity · 2) then
    if ← isArithTy (e.getArg! 0) then return true
    return ← isArithTy (e.getArg! 1)
  if e.isArrow then
    unless ← isArithTy e.bindingDomain! do return false
    return ← isArithTy e.bindingBody!
  if e.isConstOf ``False then return true
  if e.isConstOf ``True then return true
  let ty? : Option Expr :=
    if [``Eq, ``Ne].any (e.isAppOfArity · 3) then some (e.getArg! 0)
    else if [``LE.le, ``LT.lt, ``GE.ge, ``GT.gt, ``Dvd.dvd].any (e.isAppOfArity · 4) then
      some (e.getArg! 0)
    else none
  let some ty := ty? | return false
  let ty ← whnfR ty
  if ty.isAppOf ``BitVec then return true
  return [``Nat, ``Int, ``Bool].any ty.isConstOf

/-- Variables that connect hypotheses (not types, functions or proofs). -/
def isDataVar (lctx : LocalContext) (x : FVarId) : MetaM Bool := do
  let some d := lctx.find? x | return false
  let ty ← whnfR d.type
  if ty.isForall then return false
  if ty.isSort then return false
  return !(← isProp ty)

/-- `word_filter iris` clears the hypotheses that mention Iris entailments.
`word_filter` clears the hypotheses `omega` cannot use (see `isArithTy`) and,
when the goal is arithmetic and mentions variables, the arithmetic hypotheses
not connected to the goal through shared variables (transitively). Clearing is best-effort (dependencies
are kept). -/
elab "word_filter" iris:(&" iris")? : tactic => withMainContext do
  let g ← getMainGoal
  let lctx ← getLCtx
  let tgt ← instantiateMVars (← g.getType)
  let mut drop := #[]
  let mut cands : Array (FVarId × Array FVarId) := #[]
  for h in lctx do
    if h.isImplementationDetail then continue
    let ty ← instantiateMVars h.type
    unless ← isProp ty do continue
    if mentionsEntailment ty then drop := drop.push h.fvarId; continue
    if iris.isSome then continue
    unless ← isArithTy ty do drop := drop.push h.fvarId; continue
    let fvs ← (collectFVars {} ty).fvarSet.toArray.filterM fun x => isDataVar lctx x
    cands := cands.push (h.fvarId, fvs)
  let tgtVars ← (collectFVars {} tgt).fvarSet.toArray.filterM fun x => isDataVar lctx x
  if iris.isNone && !tgtVars.isEmpty && (← isArithTy tgt) then
    let mut vars : Std.HashSet FVarId := {}
    for x in tgtVars do
      vars := vars.insert x
    let mut rel : Array Bool := cands.map fun (_, f) => f.isEmpty
    let mut changed := true
    while changed do
      changed := false
      for h : i in [:cands.size] do
        if rel[i]! then continue
        if cands[i].2.any vars.contains then
          rel := rel.set! i true
          changed := true
          for x in cands[i].2 do vars := vars.insert x
    for h : i in [:cands.size] do
      unless rel[i]! do drop := drop.push cands[i].1
  if drop.isEmpty then return
  replaceMainGoal [← g.tryClearMany drop]

/-- Does `e` contain something that makes `omega` case split (Nat subtraction,
`Int.toNat`, `min`/`max`, `≠`, `∨`, `↔`, `→`)? -/
def splitty (e : Expr) : MetaM Bool := do
  let e ← instantiateMVars e
  if e.isAppOfArity ``Not 1 then
    if e.appArg!.isAppOfArity ``Eq 3 then return true
  if e.isAppOfArity ``Ne 3 then return true
  if e.isAppOfArity ``Or 2 then return true
  if e.isAppOfArity ``Iff 2 then return true
  if e.isArrow then return true
  return (e.find? fun s =>
    if s.isAppOfArity ``HSub.hSub 6 then (s.getArg! 0).isConstOf ``Nat
    else if s.isConstOf ``Int.toNat then true
    else if s.isConstOf ``Min.min then true
    else s.isConstOf ``Max.max).isSome

/-- The conjuncts of `e`. -/
partial def conjuncts (e : Expr) : List Expr :=
  if e.isAppOfArity ``And 2 then conjuncts (e.getArg! 0) ++ conjuncts (e.getArg! 1) else [e]

/-- `MVarId.note` (add `h : t` with proof `v`), building the proof term as an
explicit redex `(fun h => ?body) v`. (`MVarId.assert` + `intro` builds `?m v`
with `?m := fun h => ?body`, which `instantiateMVars` beta-reduces, copying `v`
into every use of `h`; for chained facts this blows up the proof term.) -/
def noteNoBeta (g : MVarId) (n : Name) (t v : Expr) : MetaM (FVarId × MVarId) := g.withContext do
  let target ← g.getType
  let tag ← g.getTag
  withLocalDeclD n t fun h => do
    let new ← mkFreshExprSyntheticOpaqueMVar target tag
    g.assign (mkApp (← mkLambdaFVars #[h] new) v)
    return (h.fvarId!, new.mvarId!)

/-- Add the fact `sint_Z_cases t` for every `BitVec.toInt t` in the goal and
the context (rewritten by `word_tonat`). A case split is then resolved
(`Or.resolve_left/right`) when `omega` can refute one case from the context
without the other (unresolved) case splits; smaller terms first, so that their
resolved facts help with the larger ones. The equations `t.toInt = ...` of the
resolved cases are then used to rewrite `t.toInt` away everywhere. Run after
`word_tonat`. -/
elab "word_sint_resolve" : tactic => withMainContext do
  let mut ts : Array Expr := #[]
  for h in ← getLCtx do
    unless h.isImplementationDetail do
      let ty ← instantiateMVars h.type
      unless mentionsEntailment ty do ts := collectToInt ty ts
  ts := collectToInt (← instantiateMVars (← getMainTarget)) ts
  if ts.isEmpty then return
  ts := ts.qsort (fun a b => a.approxDepth < b.approxDepth)
  -- add all the case splits, with unique names
  let mut names : Array Name := #[]
  for t in ts do
    let n := Name.mkSimple s!"word_sint_{names.size}"
    names := names.push n
    let pf ← mkAppM ``sint_Z_cases #[t.appArg!]
    let ty ← inferType pf
    liftMetaTactic fun g => do
      let (_, g) ← (← g.assert n ty pf).intro1P
      return [g]
  let ids : Array (TSyntax `ident) := names.map mkIdent
  evalTactic (← `(tactic| (try simp -implicitDefEqProofs only [BitVec.toNat_ofNat,
    BitVec.toNat_ofFin, BitVec.toNat_setWidth, BitVec.toNat_neg, BitVec.ofNat_eq_ofNat,
    BitVec.toNat_ofInt, BitVec.toNat_not, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight,
    BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_udiv, BitVec.toNat_umod,
    BitVec.toNat_twoPow, BitVec.toNat_cast, BitVec.toNat_ofNatLT, BitVec.toNat_ofBool,
    BitVec.ushiftRight_eq', BitVec.shiftLeft_eq', Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
    Int.toNat_natCast, Int.natCast_pow, Nat.reduceMod, Nat.reducePow, Nat.reduceSub,
    Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Int.reduceMod, Int.reducePow, Int.reduceToNat,
    Int.reduceNeg, Int.reduceNatCast] at $ids*)))
  -- resolve them in order
  let mut eqs : Array Name := #[]
  for i in [:names.size] do
    let main ← getMainGoal
    let lctx := (← main.getDecl).lctx
    let some h := lctx.findFromUserName? names[i]! | continue
    let ty ← instantiateMVars h.type
    unless ty.isAppOfArity ``Or 2 do continue
    let a := ty.getArg! 0
    let b := ty.getArg! 1
    -- the other unresolved case splits (and this one), and the hypotheses that make
    -- `omega` case split, are not available to `omega` here (this keeps these
    -- proofs small; also, some `omega` proofs with `Int.toNat` of `toInt` atoms
    -- send the kernel into a deep recursion evaluating `x + 4294967295`)
    let mut others : Array FVarId := #[]
    for d in lctx do
      if d.isImplementationDetail then continue
      let dty ← instantiateMVars d.type
      if dty.isAppOfArity ``Or 2 && d.userName.toString.startsWith "word_sint_" then
        others := others.push d.fvarId
      else if ← isProp dty then
        if ← (conjuncts dty).anyM fun c => (splitty c : MetaM Bool) then others := others.push d.fvarId
    for (refute, keep, lem) in [(b, a, ``Or.resolve_right), (a, b, ``Or.resolve_left)] do
      let m ← main.withContext (mkFreshExprSyntheticOpaqueMVar (mkNot refute))
      let ok ← try
          let mg ← m.mvarId!.tryClearMany others
          setGoals [mg]
          evalTactic (← `(tactic| omega))
          pure true
        catch _ => pure false
      setGoals [main]
      if ok then
        let pf ← main.withContext (mkAppM lem #[h.toExpr, ← instantiateMVars m])
        -- `noteNoBeta`, not `assert`: see there (resolution proofs are chained)
        let (_, g) ← noteNoBeta main names[i]! keep pf
        let g ← g.clear h.fvarId
        -- split `bound ∧ eq`
        let (g, isEq) ← g.withContext do
          let some d := (← getLCtx).findFromUserName? names[i]! | pure (g, false)
          let dty ← instantiateMVars d.type
          unless dty.isAppOfArity ``And 2 do return (g, false)
          let (_, g) ← noteNoBeta g (Name.mkSimple s!"word_sint_eq_{i}") (dty.getArg! 1)
            (← mkAppM ``And.right #[d.toExpr])
          let (_, g) ← g.withContext do
            noteNoBeta g names[i]! (dty.getArg! 0) (← mkAppM ``And.left #[d.toExpr])
          let g ← g.clear d.fvarId
          pure (g, true)
        if isEq then eqs := eqs.push (Name.mkSimple s!"word_sint_eq_{i}")
        replaceMainGoal [g]
        break

  -- rewrite with the resolved equations `toInt t = ...`
  unless eqs.isEmpty do
    let args ← eqs.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
    evalTactic (← `(tactic| (try simp only [$args,*, Int.toNat_natCast] at *)))

/-- Clear the unresolved case splits added by `word_sint_resolve` (fails if there
are none). -/
elab "word_drop_cases" : tactic => withMainContext do
  let mut drop := #[]
  for h in ← getLCtx do
    if h.userName.toString.startsWith "word_sint_" && (← instantiateMVars h.type).isAppOfArity ``Or 2 then
      drop := drop.push h.fvarId
  if drop.isEmpty then throwError "nothing to drop"
  replaceMainGoal [← (← getMainGoal).tryClearMany drop]

/-- Clear the hypotheses that would make `omega` case split (see `splitty`);
fails if there are none. -/
elab "word_filter_simple" : tactic => withMainContext do
  let mut drop := #[]
  for h in ← getLCtx do
    if h.isImplementationDetail then continue
    let ty ← instantiateMVars h.type
    unless ← isProp ty do continue
    if ← ((conjuncts ty).anyM fun c => (splitty c : MetaM Bool)) then drop := drop.push h.fvarId
  if drop.isEmpty then throwError "word_filter_simple: nothing to drop"
  replaceMainGoal [← (← getMainGoal).tryClearMany drop]

/-- Collect the subterms `BitVec.sdiv x y` of `e` (without loose bound variables). -/
partial def collectSDiv (e : Expr) (acc : Array Expr) : Array Expr :=
  let acc :=
    if e.isAppOfArity ``BitVec.sdiv 3 && !e.hasLooseBVars && !acc.contains e then acc.push e
    else acc
  match e with
  | .app f a => collectSDiv a (collectSDiv f acc)
  | .lam _ t b _ => collectSDiv b (collectSDiv t acc)
  | .forallE _ t b _ => collectSDiv b (collectSDiv t acc)
  | .letE _ t v b _ => collectSDiv b (collectSDiv v (collectSDiv t acc))
  | .mdata _ b => collectSDiv b acc
  | .proj _ _ b => collectSDiv b acc
  | _ => acc

/-- For every `BitVec.sdiv x y` whose divisor is positive by `decide` (e.g. a
literal), add `sdiv_cases x y`. -/
elab "word_sdiv_facts" : tactic => withMainContext do
  let mut ts : Array Expr := #[]
  for h in ← getLCtx do
    unless h.isImplementationDetail do
      let ty ← instantiateMVars h.type
      unless mentionsEntailment ty do ts := collectSDiv ty ts
  ts := collectSDiv (← instantiateMVars (← getMainTarget)) ts
  for t in ts do
    let x := t.getArg! 1
    let y := t.getArg! 2
    let s ← saveState
    try
      let main ← getMainGoal
      let pf ← main.withContext (mkAppM ``sdiv_cases #[x, y])
      let .forallE _ hyp _ _ ← inferType pf | throwError "word_sdiv_facts"
      let hm ← main.withContext (mkFreshExprSyntheticOpaqueMVar hyp)
      setGoals [hm.mvarId!]
      evalTactic (← `(tactic| decide))
      setGoals [main]
      let pf := mkApp pf (← instantiateMVars hm)
      let ty ← inferType pf
      liftMetaTactic fun g => do
        let (_, g) ← (← g.assert `hsdiv ty pf).intro1P
        return [g]
    catch _ => s.restore

/-- `word_bounded n tac`: run `tac` with a fresh budget of `n` thousand heartbeats
(the unit of `maxHeartbeats`; 1000 is roughly 0.1s); running out is an ordinary
(catchable) failure. -/
elab "word_bounded " n:num t:tactic : tactic => do
  -- without error recovery: a failing step must be an error, not a logged error
  -- plus an admitted goal (the log would be lost when the exception is caught)
  withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := n.getNat * 1000 }) <|
    withCurrHeartbeats <| tryCatchRuntimeEx (withoutRecover (evalTactic t)) fun ex => do
      if ex.isRuntime then
        throwError "word: gave up (heartbeat limit {n.getNat})"
      throw ex

end word

/-- The main pipeline of `word` (steps 1-7 of the module docstring). -/
macro "word_fast" : tactic => `(tactic| (
  word_filter iris
  word_unfold_lit
  all_goals (
    word_filter
    word_sdiv_facts
    word_tonat
    all_goals first
      | (word_filter_simple; omega)
      | omega
      | (word_sint_resolve
         all_goals first
           | (word_drop_cases; omega)
           | omega))))

open Lean Elab Tactic in
/-- `no_sorry tac`: run `tac` without error recovery (so that a failure inside
`all_goals`/`<;>` is an error rather than an admitted goal), and fail if it closed
the goal with a proof containing a (synthetic) `sorry`. -/
elab "no_sorry " tac:tactic : tactic => do
  let g ← getMainGoal
  let hadSorry := (← instantiateMVars (← g.getType)).hasSorry ||
    (← g.withContext getLCtx).any (fun d => d.type.hasSorry)
  withoutRecover (evalTactic tac)
  unless hadSorry do
    if (← instantiateMVars (mkMVar g)).hasSorry then
      throwError "{tac}: the proof would contain `sorry`"

/-- Internal: the alternatives of `word`. -/
macro "word_core" : tactic => `(tactic| first
      | word_fast
      | word_bounded 50000 (word_filter iris; word_prep; omega)
      | word_bounded 50000 (word_filter iris; word_prep; word_lit_reduce; (try omega); done)
      | word_bounded 20000 omega
      | word_bounded 50000 (bv_normalize; done))

/-- Solve word-arithmetic goals (Rocq `word`). See the module docstring. Closes
the goal or fails (never admits it). -/
syntax "word" : tactic
macro_rules
  | `(tactic| word) => `(tactic| no_sorry word_core)

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
/-- `word` fails instead of leaving an admitted goal (it used to close this
unprovable-by-`word` goal with `sorry` via the error recovery of `all_goals`). -/
example (x : w8) (n : w64)
    (h1 : [x, x, x, x, x, x, x, x, x, x, x, x, x, x, x, x, x, x, x, x].length = sint.nat n)
    (h2 : 0 ≤ sint.Z n) : sint.Z n = 20 ∨ True := by
  fail_if_success (left; word)
  right; trivial


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

example (r : w32) : sint.Z (W64 (sint.Z r)) = sint.Z r := by word

example (r : w32) (h : 0 ≤ sint.Z r) : uint.Z (W64 (sint.Z r)) = sint.Z r := by word

example (r : w32) (h : 0 ≤ sint.Z r) : uint.Z (W64 (sint.Z r)) = sint.Z r := by word

example (x : w64) (h : uint.Z x < 100) : uint.Z (x >>> W64 1) = uint.Z x / 2 := by word

example (x : w64) (h : uint.Z x < 100) : uint.Z (W64 2 * x) = 2 * uint.Z x := by word

example (i j : w64) (h : 0 ≤ sint.Z i) (h2 : sint.Z i < sint.Z j) :
    sint.Z i ≤ sint.Z ((i + j) >>> W64 1) := by word

example (a b c : w64) (ha : 0 ≤ sint.Z a) (hb : sint.Z a < sint.Z b) (hc : sint.Z b ≤ 100)
    (hc' : sint.Z c = sint.Z b - 1) : sint.Z (b - a - W64 1) = sint.Z b - sint.Z a - 1 := by word

end tests

end Perennial
