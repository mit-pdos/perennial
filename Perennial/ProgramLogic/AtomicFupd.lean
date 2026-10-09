/-
Sugar for TaDA-style logically atomic
specs whose linearization point is witnessed by a plain fancy update, without
iris's `atomic_update` (`AU`) fixpoint.

  `{{ P }} <<{ ∀∀ x, α }>> e @@ Eo <<{ ∃∃ y, β }>> {{ z, RET v; Q }}`

unfolds to

  `□ ∀ Φ, P -∗ (▷ |={⊤∖Eo,∅}=> ∃ x, α ∗ ∀ y, β -∗ |={∅,⊤∖Eo}=> ∀ z, Q -∗ Φ v) -∗
     WP e @ ⊤ {{ Φ }}`

The `{{ P }}` precondition, the `∃∃ y,` binders and the `z,` return binders may
each be omitted, giving eight variants. As for Texan
triples, at term level the notation means `⊢ ∀ Φ, ...` (the `□` is dropped).

Notes:
* The fancy update is the plain `|={E1,E2}=>`, since there is no crash logic
  (see README.md).
* The brackets are `<<{ … }>>` (as in iris-lean's `atomic_wp` notation) rather
  than `<<< … >>>`, because `>>>` is Lean's right-shift operator.
-/
module

public import Iris.BI.WeakestPre
public import Iris.BI.Lib.Atomic
public import Iris.ProgramLogic.WeakestPre

@[expose] public section

noncomputable section

namespace Perennial

open Lean Iris Iris.BI

/-- `{{ P }} <<{ ∀∀ x, α }>> e @@ Eo <<{ ∃∃ y, β }>> {{ z, RET v; Q }}`: a
logically atomic spec whose linearization point is a fancy update. -/
syntax (name := atomicFupdTriple)
  ppGroup((texanPrecond ppSpace)? "<<{ " (auAllBinders)? term " }>>" ppSpace term:max
    " @@ " term:max ppSpace "<<{ " (auExBinders)? term " }>>" ppSpace texanPostcond) : term

/-- Expand the atomic-fupd notation to a separation-logic proposition, without
the outer `□`. -/
meta def expandAtomicFupd : Syntax → MacroM Term
  | `($[$pre?:texanPrecond]? <<{ $[$xs?]? $α }>> $e @@ $Eo <<{ $[$ys?]? $β }>>
      $post:texanPostcond) => do
    let P? ← pre?.mapM fun
      | `(texanPrecond| {{ $P }}) => pure P
      | _ => Macro.throwUnsupported
    expand P? xs? α e Eo ys? β post
  | _ => Macro.throwUnsupported
where
  expand (P? : Option Term) (xs? : Option (TSyntax ``auAllBinders)) (α e Eo : Term)
      (ys? : Option (TSyntax ``auExBinders)) (β : Term) (post : TSyntax `texanPostcond) :
      MacroM Term := do
    let k ← match post with
      | `(texanPostcond| {{ $[$[$zs]* ,]? RET $v ; $Q }}) =>
        match zs with
        | some zs =>
          let zs : TSyntaxArray [`ident, `Lean.Parser.Term.hole,
              `Lean.Parser.Term.bracketedBinder] ← zs.mapM fun
            | `(binderIdent| _) => `(hole| _)
            | `(binderIdent| $i:ident) => `(ident| $i)
            | `(bracketedBinder| $x) => `(bracketedBinder| $x)
          `(iprop(∀ $zs*, $Q -∗ Φ $v))
        | none => `(iprop($Q -∗ Φ $v))
      | _ => Macro.throwUnsupported
    let close : Term ← `(iprop($β -∗ |={∅, ⊤ \ $Eo}=> $k))
    let close : Term ← match ys? with
      | some ys => pure ⟨← expandExplicitBinders ``BIBase.forall ys.raw[1] close⟩
      | none => pure close
    let body : Term ← `(iprop($α ∗ $close))
    let body : Term ← match xs? with
      | some xs => pure ⟨← expandExplicitBinders ``BIBase.exists xs.raw[1] body⟩
      | none => pure body
    let cont : Term ← `(iprop((▷ |={⊤ \ $Eo, ∅}=> $body) -∗ WP $e:term @ ⊤ {{ Φ }}))
    match P? with
    | some P => `(iprop(∀ Φ, $P -∗ $cont))
    | none => `(iprop(∀ Φ, $cont))

@[macro Iris.BI.iprop]
meta def atomicFupdIprop : Macro
  | `(iprop($P)) => do `(iprop(□ $(← expandAtomicFupd P)))
  | _ => Macro.throwUnsupported

@[macro atomicFupdTriple]
meta def atomicFupdTerm : Macro
  | P => do `(⊢ $(← expandAtomicFupd P))



end Perennial
