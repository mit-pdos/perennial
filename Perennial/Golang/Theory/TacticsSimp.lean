/-
The `goose_wp_simp_extra` simp set: extensions of `goose_wp_simp` used by
`wp_pures`/`wp_auto` to normalize the expression of a WP goal when
`set_option goose.wp.extras true` (off by default, so that existing proofs that do
these simplifications by hand keep working). No Rocq counterpart: in Rocq these
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

These were first written as local workarounds in
`Perennial/Proof/github_com/mit_pdos/perennial/goose/testdata/examples/TacticWorkarounds.lean`
(with different names, so both can coexist).
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

@[goose_wp_simp_extra] theorem zero_val_interface_nil [ffi_syntax] [GoLocalContext] :
    (zero_val interface.t) = interface.nil := rfl


end Perennial
