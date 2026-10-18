/-
Deciding type-set membership, `go.typeSetContains t t'` (does the type `t` implement
the interface type `t'`?), from the method-set facts (`Golang/Defn/MethodSet.lean`):
those of a package's `Assumptions` for its named types (`T.TypeAssumptions.method_set`,
`ptr_method_set`) and those of the semantics for the types without methods.

* `go.typeSetContains_underlying`: `typeSetContains t t'` is the membership of `t` in each
  element of the underlying interface type of `t'` (found by `t' ↓u go.InterfaceType elems`,
  for a named interface type through its `UnderlyingDirectedEq`).
* `go.typeSetElemContains_method`: `t` has the method `m` with signature `sig` iff the
  entry of `m` in `t`'s method set (`MethodSetIs t ms`, found by typeclass search) has the
  signature `sig` (`false` if there is no entry; left as `methodSet t !! m = some sig` if
  the entry's signature is not known).
* `go_type_set`: the tactic that rewrites a goal (or `at h`) with these and evaluates the
  lookups and the signature comparisons, e.g.
  ```
  example [errors.Assumptions] :
      go.typeSetContains (go.GoType.PointerType errors.errorString.ty) go.error = true := by
    go_type_set
  ```
  It decides membership in an interface made of methods whenever the method sets of the
  types involved are known (`Perennial/ProgramLogic/TypeSetTest.lean` has examples,
  including non-membership).
-/
module

public import Perennial.Golang.Defn.Pre
public import Perennial.Golang.Theory.TacticsSimp
public import Perennial.Golang.Theory.TypeSetSimpAttr

@[expose] public section

namespace Perennial

namespace go
section lemmas
variable [FfiSyntax] [GoLocalContext] [GoGlobalContext] [GoSemanticsFunctions]

@[go_type_set_simp] theorem typeSetContains_underlying {t t' : go.GoType} {elems : List go.InterfaceElem}
    [t' ↓u go.InterfaceType elems] :
    typeSetContains t t' = typeSetElemsContains t elems := by
  simp only [typeSetContains, is_underlying]

@[go_type_set_simp] theorem typeSetElemsContains_nil (t : go.GoType) : typeSetElemsContains t [] = true := rfl

@[go_type_set_simp] theorem typeSetElemsContains_cons (t : go.GoType) (e : go.InterfaceElem) (es : List go.InterfaceElem) :
    typeSetElemsContains t (e :: es) = (typeSetElemContains t e && typeSetElemsContains t es) := rfl

@[go_type_set_simp] theorem typeSetElemContains_method {t : go.GoType} {ms : List (GoString × Option go.signature)}
    [MethodSetIs t ms] (m : GoString) (sig : go.signature) :
    typeSetElemContains t (go.MethodElem m sig) =
      (match methodSetLookup ms m with
       | none => false
       | some (some s) => decide (s = sig)
       | some none => decide (methodSet t !! m = some sig)) := by
  have h := MethodSetIs.method_set_is (t := t) (ms := ms) m
  simp only [typeSetElemContains]
  revert h
  cases methodSetLookup ms m with
  | none => intro h; simp [h]
  | some o =>
    cases o with
    | none => intro _; rfl
    | some s => intro h; simp only [h, Option.some.injEq]

@[go_type_set_simp] theorem methodSetLookup_nil (m : GoString) : methodSetLookup [] m = none := rfl

@[go_type_set_simp] theorem methodSetLookup_cons (k m : GoString) (s : Option go.signature)
    (ms : List (GoString × Option go.signature)) :
    methodSetLookup ((k, s) :: ms) m = if k = m then some s else methodSetLookup ms m := rfl

/-- A `false` membership from a method of `t'`'s that `t` lacks: the form a proof of
non-membership takes when the method set of `t` is only partly known (its signatures). -/
theorem typeSetElemContains_method_none {t : go.GoType} {ms : List (GoString × Option go.signature)}
    [MethodSetIs t ms] {m : GoString} (sig : go.signature) (h : methodSetLookup ms m = none) :
    typeSetElemContains t (go.MethodElem m sig) = false := by
  rw [typeSetElemContains_method, h]

end lemmas
end go

/- The other rewrites of `go_type_set`: the method-set lookups' conditions (`if k = m`)
and the signature comparisons (`gooseReduceGoTypeEq`), and the boolean and
propositional connectives they leave. -/
attribute [go_type_set_simp] gooseReduceIteDecide gooseReduceGoTypeEq
  go.signature.Signature.injEq List.cons.injEq List.nil_eq decide_True_any decide_False_any
  decide_eq_self_any and_true true_and and_false false_and Bool.and_true Bool.true_and
  Bool.and_false Bool.false_and Bool.and_self

/-- `reduceCtorEq` in `go_type_set_simp` (distinct constructors of the signatures' types
and of `List`): a core simproc can only be added to a simp set from a `module` through a
declaration of this module. -/
simproc [go_type_set_simp] goTypeSetReduceCtorEq (_ = _) := reduceCtorEq

/-- `go_type_set` (also `go_type_set at h`): decide `go.typeSetContains t t'` (whether
`t` implements the interface type `t'`) from the method-set facts of the packages'
`Assumptions` and of the semantics (`Golang/Theory/TypeSet.lean`): `simp only` with the
simp set `go_type_set_simp`, which rewrites with `go.typeSetContains_underlying` (the
instance `t' ↓u u`), `go.typeSetElemContains_method` (the instance `MethodSetIs t ms`),
evaluates the method-set lookups and compares the signatures (`gooseReduceGoTypeEq`);
add a lemma to the set with `attribute [go_type_set_simp]`. What it cannot decide (a type
whose method set is not known, an entry whose signature is not known) is left in the
goal. -/
syntax "go_type_set" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| go_type_set $[$loc]?) => `(tactic|
      simp only [go_type_set_simp] $[$loc]?)

end Perennial
