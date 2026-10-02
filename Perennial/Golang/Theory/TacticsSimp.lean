/-
The `goose_wp_simp_extra` simp set: extensions of `goose_wp_simp` used by
`wp_pures`/`wp_auto` to normalize the expression of a WP goal when
`goose.wp.extras` (on by default). No Rocq counterpart: in Rocq these
reductions are done by `simpl`/`vm_compute`/`bool_decide` hints.

* `goose_reduceIteDecide`: `if p then a else b` whose (metavariable-free)
  decidable condition evaluates by `whnf` (e.g. `go_string` literal equalities in
  keyed struct literals, `go.is_interface_type t = true`), even when other parts of
  the term mention free variables.
* `go.struct_field_type` and `eq_self`.
* `goose_reduceGoTypeEq`: equalities of `go.type`s (decided classically, so not
  by reduction) are decided: `True` when definitionally equal (unfolding named
  types), `False` when the fingerprints `go.type_fingerprint` differ.
* `zero_val_interface_nil`: `zero_val interface.t = interface.nil`.
* `decide_*_any`, `into_val_eq_iff`: `decide` with arbitrary (classical)
  `Decidable` instances, `#a = #b ↔ a = b`.
* `goose_replicateArrayLiteral`, list lemmas: the zero array of a slice literal
  is a literal list, so `[]T{a}` gives `[a]`; `sint.nat`/`uint.nat` of literals.
* `Option.getD_some`/`_none` (map lookups).

These were first written as local workarounds in a goose testdata
file (`TacticWorkarounds.lean`, now removed).
-/
import Perennial.Golang.Theory.Pkg

namespace Perennial

open Lean Meta in
/-- Reduce `if p then a else b` when the decidable proposition `p` (without
metavariables) evaluates to `true`/`false` by reduction (default transparency).
Errors (including runtime ones) leave the term alone. -/
simproc [goose_wp_simp_extra] goose_reduceIteDecide (@ite _ _ _ _ _) := fun e => do
  let_expr f@ite α p inst a b := e | return .continue
  if p.hasMVar then return .continue
  tryCatchRuntimeEx (do
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
    return .continue)
    (fun _ => return .continue)

attribute [goose_wp_simp_extra] go.struct_field_type eq_self

namespace go

/-- A computable fingerprint of a `go_string` (length-prefixed). -/
def str_fingerprint (s : go_string) : List Nat := s.length :: s.map BitVec.toNat

mutual
/-- A computable fingerprint of a Go type (a length-prefixed encoding, injective in
practice), used to prove `go.type` disequalities. -/
def type_fingerprint : go.type → List Nat
  | .Named n args => [0] ++ str_fingerprint n ++ types_fingerprint args
  | .ArrayType n t => [1, n.natAbs, if n < 0 then 1 else 0] ++ type_fingerprint t
  | .StructType fds => [2] ++ fields_fingerprint fds
  | .PointerType t => [3] ++ type_fingerprint t
  | .FunctionType sig => [4] ++ sig_fingerprint sig
  | .InterfaceType elems => [5] ++ elems_fingerprint elems
  | .SliceType t => [6] ++ type_fingerprint t
  | .MapType k v => [7] ++ type_fingerprint k ++ type_fingerprint v
  | .ChannelType d t =>
    [8, match d with | .sendrecv => 0 | .sendonly => 1 | .recvonly => 2] ++ type_fingerprint t
  | .UntypedType n => [9] ++ str_fingerprint n
def types_fingerprint : List go.type → List Nat
  | [] => [0]
  | t :: ts => [1] ++ type_fingerprint t ++ types_fingerprint ts
def fields_fingerprint : List go.field_decl → List Nat
  | [] => [0]
  | .FieldDecl n t :: fds => [1] ++ str_fingerprint n ++ type_fingerprint t ++ fields_fingerprint fds
  | .EmbeddedField n t :: fds =>
    [2] ++ str_fingerprint n ++ type_fingerprint t ++ fields_fingerprint fds
def sig_fingerprint : go.signature → List Nat
  | .Signature args variadic results =>
    types_fingerprint args ++ [if variadic then 1 else 0] ++ types_fingerprint results
def elems_fingerprint : List go.interface_elem → List Nat
  | [] => [0]
  | .MethodElem m sig :: es => [1] ++ str_fingerprint m ++ sig_fingerprint sig ++ elems_fingerprint es
  | .TypeElem terms :: es => [2] ++ terms_fingerprint terms ++ elems_fingerprint es
def terms_fingerprint : List go.type_term → List Nat
  | [] => [0]
  | .TypeTerm t :: ts => [1] ++ type_fingerprint t ++ terms_fingerprint ts
  | .TypeTermUnderlying t :: ts => [2] ++ type_fingerprint t ++ terms_fingerprint ts
end

theorem type_ne_of_fingerprint {a b : go.type}
    (h : decide (type_fingerprint a = type_fingerprint b) = false) : a ≠ b :=
  fun e => by subst e; simp at h

end go

open Lean Meta in
/-- Decide `t1 = t2` for `go.type`s: `True` if definitionally equal (unfolding
everything), `False` if the fingerprints differ. Errors (including runtime ones
such as deep recursion) leave the equation alone. -/
simproc [goose_wp_simp_extra] goose_reduceGoTypeEq (@Eq go.type _ _) := fun e => do
  let_expr Eq _ a b := e | return .continue
  if a.hasMVar || b.hasMVar then return .continue
  tryCatchRuntimeEx (do
    if ← withTransparency .all <| isDefEq a b then
      let h ← mkExpectedTypeHint (← mkEqRefl a) (← mkEq a b)
      return .done { expr := mkConst ``True, proof? := some (← mkAppM ``eq_true #[h]) }
    let fa := mkApp (mkConst ``go.type_fingerprint) a
    let fb := mkApp (mkConst ``go.type_fingerprint) b
    let d ← mkDecide (← mkEq fa fb)
    let r ← withTransparency .all <| whnf d
    if r.isConstOf ``Bool.false then
      let h := mkApp3 (mkConst ``go.type_ne_of_fingerprint) a b (← mkEqRefl (mkConst ``Bool.false))
      return .done { expr := mkConst ``False, proof? := some (← mkAppM ``eq_false #[h]) }
    return .continue)
    (fun _ => return .continue)

/-! ### Booleans and `decide` with arbitrary `Decidable` instances

Equality on `val` (and on other GooseLang types) is decided classically, so the
usual `decide_true`/`decide_eq_true` simp lemmas (stated for specific instances)
do not apply. These are stated for any instance. -/

@[goose_wp_simp_extra] theorem decide_True_any {h : Decidable True} : @decide True h = true :=
  decide_eq_true trivial
@[goose_wp_simp_extra] theorem decide_False_any {h : Decidable False} : @decide False h = false :=
  decide_eq_false id
@[goose_wp_simp_extra] theorem decide_eq_self_any {α : Sort _} {a : α} {h : Decidable (a = a)} :
    @decide (a = a) h = true := decide_eq_true rfl
@[goose_wp_simp_extra] theorem decide_not_any {p : Prop} {h : Decidable p} {h' : Decidable (¬p)} :
    @decide (¬p) h' = !(@decide p h) := by
  by_cases hp : p <;> simp [hp]

section into_val_eq
variable [ffi_syntax] [GoGlobalContext]

/-- `#a = #b` iff `a = b`, for a Go type with an injective `into_val` (e.g.
`decide (#false = #true)` becomes `false`). -/
@[goose_wp_simp_extra] theorem into_val_eq_iff {V : Type} [go.IntoValInj V] {a b : V} :
    (#a : val) = #b ↔ a = b := ⟨fun h => go.into_val_inj h, fun h => h ▸ rfl⟩

end into_val_eq

/-! ### Array (slice) literal sizes and word literals -/

section array_lit
open Lean Meta

/-- The value of `go.array_literal_size kvs` for a literal list `kvs` whose keys
are all `none` (the elements themselves are not inspected). -/
def arrayLiteralSize? (kvs : Expr) : MetaM (Option Int) := do
  let mut n : Int := 0
  let mut l ← whnfR kvs
  repeat
    if l.isAppOfArity ``List.nil 1 then break
    unless l.isAppOfArity ``List.cons 3 do return none
    let ke ← whnfR (l.getArg! 1)
    unless ke.isAppOfArity ``keyed_element.KeyedElement 3 do return none
    unless (← whnfR (ke.getArg! 1)).isAppOfArity ``Option.none 1 do return none
    n := n + 1
    l ← whnfR (l.getArg! 2)
  return some n

/-- The zero array of a slice (or array) composite literal, `List.replicate
(go.array_literal_size kvs).toNat x` (from `(zero_val (array.t V n)).arr`), is
evaluated to a literal list when the size can be computed, so that the list of a
slice literal `[]T{a, b}` comes out as `[a, b]`. The size itself (also in the
`slice.mk` of `wp_slice_literal`'s postcondition) is left alone, so that the WP
expression and the hypotheses of the spec agree. -/
simproc [goose_wp_simp_extra] goose_replicateArrayLiteral
    (List.replicate (Int.toNat (@go.array_literal_size ?inst _)) _) := fun e => do
  let_expr List.replicate α nE x := e | return .continue
  let_expr Int.toNat sz := nE | return .continue
  let_expr go.array_literal_size _ kvs := sz | return .continue
  let some n ← arrayLiteralSize? kvs | return .continue
  let us := e.getAppFn.constLevels!
  let lit := (List.range n.toNat).foldr (fun _ acc => mkApp3 (mkConst ``List.cons us) α x acc)
    (mkApp (mkConst ``List.nil us) α)
  return .done { expr := lit, proof? := some (mkExpectedPropHint (← mkEqRefl lit) (← mkEq e lit)) }

end array_lit

/-- In WP expressions only the `Nat` conversions (list indices, e.g. the
`sint.nat (W64 0)` of a slice literal) are evaluated by the extras;
`sint.Z (W64 n)` is evaluated by `simp` (`word_lit_*` simprocs) but kept in WP
expressions, as proofs refer to it. -/
simproc [goose_wp_simp_extra] goose_sintNatLit (sint.nat _) := fun e => word.evalWordLitConv e
simproc [goose_wp_simp_extra] goose_uintNatLit (uint.nat _) := fun e => word.evalWordLitConv e

attribute [goose_wp_simp_extra] Option.getD_some Option.getD_none
attribute [goose_wp_simp_extra] Int.reduceToNat List.replicate_succ List.replicate_zero
  List.set_cons_zero List.set_cons_succ List.set_nil

@[goose_wp_simp_extra] theorem zero_val_interface_nil [ffi_syntax] [GoLocalContext] :
    (zero_val interface.t) = interface.nil := rfl


end Perennial
