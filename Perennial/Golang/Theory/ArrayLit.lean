/-
Array literals whose elements are all values take one pure step (`PureWp`) to
the array value: `pure_wp_array_lit`, proved once by induction over the element
list. `wp_pures`/`wp_auto` use it (`arrayLitPureWp?` in `ProofMode.lean`), instead
of stepping through the `ArraySet` chain that `go.composite_literal_array`
unfolds to, which re-simplified the partly built array (and its index arithmetic
`0 + 1 + ... + 1`) at every element: quadratic in the length of the literal.
-/
module

public import Perennial.Golang.Theory.PostLifting

@[expose] public section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

/-- The keyed element of an array literal element that is the value `#x` of type `t`. -/
def arrayLitKE [FfiSyntax] [GoGlobalContext] (t : go.GoType) {V : Type} (x : V) : keyed_element :=
  KeyedElement none (ElementExpression t (Val #x))

/-- Set `acc` at indices `i, i+1, ...` to `xs`, as the steps of an array literal do. -/
def arrayLitSets {V : Type} : List V → Int → List V → List V
  | acc, _, [] => acc
  | acc, i, x :: xs => arrayLitSets (acc.set (sint.nat (W64 i)) x) (i + 1) xs

theorem arrayLitSets_eq {V : Type} (z : V) :
    ∀ (xs ys : List V) (m : Nat), xs.length ≤ m → ys.length + m < 2 ^ 63 →
      arrayLitSets (ys ++ List.replicate m z) (ys.length : Int) xs =
        ys ++ xs ++ List.replicate (m - xs.length) z
  | [], ys, m, _, _ => by simp [arrayLitSets]
  | x :: xs, ys, m, hle, hlt => by
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by simp at hle; omega⟩
    have hi : sint.nat (W64 (ys.length : Int)) = ys.length := by
      simp only [sint.nat]
      rw [BitVec.toInt_ofInt, Int.bmod_eq_of_le (by omega) (by omega)]
      omega
    have hset : (ys ++ List.replicate (m' + 1) z).set ys.length x =
        (ys ++ [x]) ++ List.replicate m' z := by
      rw [List.set_append_right _ _ (by omega)]
      simp [List.replicate_succ]
    have := arrayLitSets_eq z xs (ys ++ [x]) m' (by simp at hle; omega) (by simp; omega)
    simp only [arrayLitSets, hi, hset]
    simp only [List.length_append, List.length_singleton, Int.natCast_add, Int.natCast_one] at this
    rw [this]
    simp

section array_lit
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable [GoSemanticsFunctions] [go.PreSemantics]

theorem wp_arrayLit_set {s : Stuckness} {E : CoPset} (n : Int) (t : go.GoType) {V : Type} (e0 : Expr)
    (acc : List V) (i : Int) (x : V)
    (he0 : ∀ Ψ : val → IProp GF, Ψ #(array.mk n acc) ⊢ WP e0 @ s; E {{ Ψ }})
    (Φ : val → IProp GF) :
    Φ #(array.mk n (acc.set (sint.nat (W64 i)) x)) ⊢
      WP gl(ArraySet (e0, (#(W64 i), Convert t t (Val #x)))) @ s; E {{ Φ }} := by
  refine .trans ?_ (wp_bind (fill [EctxItem.PairLCtx (Pair (Val #(W64 i))
    (App (Val (GoInstruction (GoInstruction.Convert t t))) (Val #x))),
    EctxItem.AppRCtx (Val (GoInstruction GoInstruction.ArraySet))]))
  refine .trans ?_ (he0 _)
  change _ ⊢ WP gl(ArraySet (Val #(array.mk n acc), (#(W64 i), Convert t t (Val #x)))) @ s; E {{ Φ }}
  iintro HΦ
  wp_pures
  iexact HΦ

theorem wp_arrayLit_fold {s : Stuckness} {E : CoPset} (n : Int) (t : go.GoType) {V : Type}
    (F : Int × Expr → keyed_element → Int × Expr)
    (hF : ∀ (i : Int) (e : Expr) (x : V), F (i, e) (arrayLitKE t x) =
      (i + 1, gl(ArraySet (e, (#(W64 i), Convert t t (Val #x)))))) :
    ∀ (xs : List V) (i : Int) (e0 : Expr) (acc : List V),
      (∀ Ψ : val → IProp GF, Ψ #(array.mk n acc) ⊢ WP e0 @ s; E {{ Ψ }}) →
      ∀ Φ : val → IProp GF, Φ #(array.mk n (arrayLitSets acc i xs)) ⊢
        WP (List.foldl F (i, e0) (xs.map (arrayLitKE t))).2 @ s; E {{ Φ }}
  | [], _, _, _, he0, Φ => he0 Φ
  | x :: xs, i, e0, acc, he0, Φ => by
    simp only [List.map_cons, List.foldl_cons, hF, arrayLitSets]
    exact wp_arrayLit_fold n t F hF xs (i + 1) _ _
      (fun Ψ => wp_arrayLit_set n t e0 acc i x he0 Ψ) Φ

/-- An array literal whose elements are all values (of the element type) takes a
single step (in fact many) to the array value. -/
theorem pure_wp_array_lit (n : Int) (t : go.GoType) {V : Type} {zv : ZeroVal V} [TypeRepr t V]
    (xs : List V) (m : Nat) (kvs : List keyed_element) (hkvs : kvs = xs.map (arrayLitKE t))
    (hlen : xs.length + m = n.toNat) (hn : n.toNat < 2 ^ 63) :
    PureWp (G := G) (L := L) True
      (App (Val (GoInstruction (CompositeLiteral (go.ArrayType n t)))) (Val (LiteralValueV kvs)))
      (Val #(array.mk n (xs ++ List.replicate m (zero_val V)))) := by
  subst hkvs
  refine pure_wp_val _ _ _ fun s E Φ _ => ?_
  refine .trans ?_ ((pure_wp_go_step_det (G := G) (L := L) _ _ _).pure_wp_wp s E Φ [] trivial)
  have he0 : ∀ Ψ : val → IProp GF,
      Ψ #(array.mk n (List.replicate n.toNat (zero_val V))) ⊢
        WP (GoZeroVal (go.ArrayType n t) #() : Expr) @ s; E {{ Ψ }} := by
    intro Ψ
    iintro H
    wp_pures
    iexact H
  have hfin : arrayLitSets (List.replicate n.toNat (zero_val V)) 0 xs =
      xs ++ List.replicate m (zero_val V) := by
    have := arrayLitSets_eq (zero_val V) xs [] n.toNat (by omega) (by simp; omega)
    simp only [List.nil_append, List.length_nil, Int.natCast_zero] at this
    rw [this]; congr 2; omega
  refine later_mono (wand_mono_right ?_)
  rw [← hfin]
  exact wp_arrayLit_fold n t _ (fun _ _ _ => rfl) xs 0 _ _ he0 Φ

/-- `pure_wp_array_lit` for a literal that gives every element. -/
theorem pure_wp_array_lit_full (n : Int) (t : go.GoType) {V : Type} {zv : ZeroVal V}
    [TypeRepr t V] (xs : List V) (kvs : List keyed_element) (hkvs : kvs = xs.map (arrayLitKE t))
    (hlen : xs.length = n.toNat) (hn : n.toNat < 2 ^ 63) :
    PureWp (G := G) (L := L) True
      (App (Val (GoInstruction (CompositeLiteral (go.ArrayType n t)))) (Val (LiteralValueV kvs)))
      (Val #(array.mk n xs)) := by
  have := pure_wp_array_lit (G := G) (L := L) n t xs 0 kvs hkvs (by omega) hn
  rwa [List.replicate_zero, List.append_nil] at this

end array_lit

end Perennial
