/-
Local workarounds for gaps in the GooseLang WP tactics, used by the goose
testdata proofs (no Rocq counterpart). Each should eventually move into
`Perennial/Golang/Theory`.

* `go.struct_field_type` (the field type lookup in keyed struct literals,
  `CompositeLiteral (go.StructType fds)`) is not in `goose_wp_simp`, so struct
  literals get stuck at `Convert t (struct_field_type f fds)`.
* The resulting `if f = f' then .. else ..` on `go_string` literals is not
  reduced: `goose_reduceDecide` only reduces `decide p`, not `ite p`.
  `goose_reduceIte` reduces an `ite` whose condition evaluates by `whnf`
  (also when it mentions section variables such as the `GoGlobalContext`, e.g.
  `go.is_interface_type «SquareStructⁱᵐᵖˡ» = true` from conversions to
  interfaces; `goose_reduceDecide` skips conditions with free variables).
* `if t = t then ..` on `go.type` (decided classically) is not reduced; we add
  `eq_self` to `goose_wp_simp`.
* Equalities `t1 = t2` of `go.type`s (decided classically, so not by
  reduction) are not simplified, e.g. `if go.int.PointerType = go.string.PointerType`
  from comparing a `*int` to a `*string` converted to `any`, or the type
  comparison in `TypesEqual`. `goose_reduceTypeEq` decides them: equal if
  definitionally equal (unfolding named types such as `go.int` and
  package-level types), different if a computable fingerprint (`go.type_fp`)
  differs.
* `wp_alloc_anon` (Rocq `wp_alloc x as "?"` inside `steps`): an allocation that
  is not bound by a `let:` (e.g. `&S{..}`), with inaccessible names.
* A store of a function literal (`x.fn = func(..) {..}`) gets stuck: the stored
  value is a raw `RecV f x e`, which `wp_store` does not recognize as
  `#(func.mk f x e)`. `recv_eq_func` rewrites it.
* `zero_val interface.t` is not reduced to `interface.nil`, so e.g. comparisons
  of zero-valued interfaces get stuck on a `match`.
-/
import Perennial.Golang.Theory

namespace Perennial

open Lean Meta in
/-- Reduce `if p then a else b` when the (closed) decidable proposition `p`
evaluates to `true`/`false` by reduction (e.g. equality of `go_string`
literals). -/
simproc [goose_wp_simp] goose_reduceIte (@ite _ _ _ _ _) := fun e => do
  let_expr f@ite α p inst a b := e | return .continue
  if p.hasMVar then return .continue
  let d := mkApp2 (mkConst ``Decidable.decide) p inst
  let r ← withTransparency .default <| whnf d
  let u := f.constLevels!
  if r.isConstOf ``Bool.true then
    let h := mkApp3 (mkConst ``of_decide_eq_true) p inst (← mkEqRefl (mkConst ``Bool.true))
    let pf := mkApp6 (mkConst ``if_pos u) p inst h α a b
    return .done { expr := a, proof? := some pf }
  if r.isConstOf ``Bool.false then
    let h := mkApp3 (mkConst ``of_decide_eq_false) p inst (← mkEqRefl (mkConst ``Bool.false))
    let pf := mkApp6 (mkConst ``if_neg u) p inst h α a b
    return .done { expr := b, proof? := some pf }
  return .continue

attribute [goose_wp_simp] go.struct_field_type eq_self

namespace go

/-- A computable fingerprint of a Go type (injective in practice: a
length-prefixed encoding), used to prove `go.type` disequalities. -/
def str_fp (s : go_string) : List Nat := s.length :: s.map BitVec.toNat

mutual
def type_fp : go.type → List Nat
  | .Named n args => [0] ++ str_fp n ++ types_fp args
  | .ArrayType n t => [1, n.natAbs, if n < 0 then 1 else 0] ++ type_fp t
  | .StructType fds => [2] ++ fields_fp fds
  | .PointerType t => [3] ++ type_fp t
  | .FunctionType sig => [4] ++ sig_fp sig
  | .InterfaceType elems => [5] ++ elems_fp elems
  | .SliceType t => [6] ++ type_fp t
  | .MapType k v => [7] ++ type_fp k ++ type_fp v
  | .ChannelType d t =>
    [8, match d with | .sendrecv => 0 | .sendonly => 1 | .recvonly => 2] ++ type_fp t
  | .UntypedType n => [9] ++ str_fp n
def types_fp : List go.type → List Nat
  | [] => [0]
  | t :: ts => [1] ++ type_fp t ++ types_fp ts
def fields_fp : List go.field_decl → List Nat
  | [] => [0]
  | .FieldDecl n t :: fds => [1] ++ str_fp n ++ type_fp t ++ fields_fp fds
  | .EmbeddedField n t :: fds => [2] ++ str_fp n ++ type_fp t ++ fields_fp fds
def sig_fp : go.signature → List Nat
  | .Signature args variadic results =>
    types_fp args ++ [if variadic then 1 else 0] ++ types_fp results
def elems_fp : List go.interface_elem → List Nat
  | [] => [0]
  | .MethodElem m sig :: es => [1] ++ str_fp m ++ sig_fp sig ++ elems_fp es
  | .TypeElem terms :: es => [2] ++ terms_fp terms ++ elems_fp es
def terms_fp : List go.type_term → List Nat
  | [] => [0]
  | .TypeTerm t :: ts => [1] ++ type_fp t ++ terms_fp ts
  | .TypeTermUnderlying t :: ts => [2] ++ type_fp t ++ terms_fp ts
end

theorem type_ne_of_fp {a b : go.type} (h : decide (type_fp a = type_fp b) = false) : a ≠ b :=
  fun e => by subst e; simp at h

end go

open Lean Meta in
/-- Decide `t1 = t2` for `go.type`s: `True` if definitionally equal (unfolding
everything), `False` if the fingerprints differ. -/
simproc [goose_wp_simp] goose_reduceTypeEq (@Eq go.type _ _) := fun e => do
  let_expr Eq _ a b := e | return .continue
  if a.hasMVar || b.hasMVar then return .continue
  -- never fail: errors (including runtime ones such as deep recursion) leave
  -- the equation alone
  tryCatchRuntimeEx (do
    if ← withTransparency .all <| isDefEq a b then
      let h ← mkExpectedTypeHint (← mkEqRefl a) (← mkEq a b)
      return .done { expr := mkConst ``True, proof? := some (← mkAppM ``eq_true #[h]) }
    let fa := mkApp (mkConst ``go.type_fp) a
    let fb := mkApp (mkConst ``go.type_fp) b
    let d ← mkDecide (← mkEq fa fb)
    let r ← withTransparency .all <| whnf d
    if r.isConstOf ``Bool.false then
      let h := mkApp3 (mkConst ``go.type_ne_of_fp) a b (← mkEqRefl (mkConst ``Bool.false))
      return .done { expr := mkConst ``False, proof? := some (← mkAppM ``eq_false #[h]) }
    return .continue)
    (fun _ => return .continue)

section func
variable [ffi_syntax] [GoLocalContext] [GoGlobalContext] [GoSemanticsFunctions] [go.PreSemantics]

theorem recv_eq_func (f x : binder) (e : expr) : (RecV f x e : val) = #(func.mk f x e) := by
  rw [go.into_val_unfold func.t]

end func

open Lean Elab Tactic Meta Qq Iris.ProofMode in
/-- `wp_alloc_anon`: perform an allocation `GoAlloc t #v` in evaluation
position (not necessarily bound by `let:`), with inaccessible names. -/
elab "wp_alloc_anon" : tactic =>
  runTacticGooseWp `wp_alloc_anon fun mvar g wp => do
    let l ← mkFreshUserName `l
    let H ← mkFreshUserName `H
    mvar.assign (← iWpAllocStep g.hyps wp false (some (l, H)) fun hyps' wp' => iWpFinish hyps' wp')

@[goose_wp_simp] theorem zero_val_interface [ffi_syntax] :
    (zero_val interface.t) = interface.nil := rfl

end Perennial
