/-
Shared definitions of the proofs of the stateless `github.com/tchajed/marshal` encoding
helpers: the package's `isPkgInit`, the encoding predicates (`Uint64HasEncoding`, ...,
`Encodes`), and the lemmas about words and slices that the proofs use.

Notes on the statements (in `Perennial/Spec/github_com/tchajed/marshal/`):
* `reserve.spec`: hypothesis `Hbound : length vs + uint.Z extra ≤ 2^62`.
  Without it the spec is false: `reserve` grows to
  `new_cap = max(2 * cap b, len b + extra)` and `make3` panics when
  `new_cap ≥ 2^63` (e.g. `cap b = 2^62`, `len b + extra = 2^62 + 1`).
  The bound is tight: for `extra ≥ 1` and any `len b + extra` in
  `(2^62, 2^64)` there is a capacity (`len b + extra - 1` or `len b`) that
  makes `make3` panic. (If `len b + extra` overflows,
  `SumAssumeNoOverflow` diverges, which is safe.)
* `WriteInt.spec` / `WriteInt32.spec` / `WriteLenPrefixedBytes.spec`:
  hypothesis `length vs + 8 ≤ 2^62` (`+ 4` for `WriteInt32`), inherited from
  `reserve.spec` (tight for the same reason). `WriteBytes.spec` and
  `WriteBool.spec` use `append` and need no bound.
* `compute_new_cap.spec`: the postcondition includes
  `⌜new_cap = min_cap ∨ new_cap = old_cap * W64 2⌝` (needed to bound the
  capacity passed to `make3`).
-/
module

public import Perennial.Proof.github_com.goose_lang.std.Base
public import Perennial.Proof.github_com.goose_lang.primitive.Base
public import Perennial.Proof.encoding.binary.Base
public import Perennial.Code.github_com.tchajed.marshal
public import Perennial.GeneratedProof.github_com.tchajed.marshal
public import Perennial.Std.Word.LittleEndian

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

namespace github_com.tchajed.marshal

/-! Some helper definitions for working with slices of primitive values. -/

def Uint64HasEncoding (encoded : List w8) (x : w64) : Prop := encoded = u64Le x

def Uint32HasEncoding (encoded : List w8) (x : w32) : Prop := encoded = u32Le x

def BoolHasEncoding (encoded : List w8) (x : Bool) : Prop :=
  encoded = [if x then W8 1 else W8 0]

def StringHasEncoding (encoded : List w8) (x : GoString) : Prop := encoded = x

def ByteHasEncoding (encoded : List w8) (x : List w8) : Prop := encoded = x

def Encodes {A : Type} (enc : List w8) (xs : List A) (has_encoding : List w8 → A → Prop) : Prop :=
  match xs with
  | [] => enc = []
  | x :: xs' => ∃ bs bs', xs = x :: xs' ∧ enc = bs ++ bs' ∧ has_encoding bs x ∧
      Encodes bs' xs' has_encoding

theorem drop_succ {A : Type} (l : List A) (x : A) (l' : List A) (n : Nat)
    (_Helem : l[n]? = some x) (Hd : l.drop n = x :: l') : l.drop (n + 1) = l' := by
  rw [← List.drop_drop, Hd]; rfl

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.tchajed.marshal.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.tchajed.marshal :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.tchajed.marshal :=
  build_get_is_pkg_init_wf

theorem sint_lt_2_63 (x : w64) : sint.Z x < 2 ^ 63 := by word

theorem sint_of_uint_le (x : w64) (y : Int) (h : uint.Z x ≤ y) (hy : y < 2 ^ 63) :
    sint.Z x = uint.Z x := by word

theorem room8 (l c : w64) (hroom : uint.Z (W64 8) ≤ uint.Z c - uint.Z l)
    (hwf : 0 ≤ sint.Z l ∧ sint.Z l ≤ sint.Z c) :
    sint.Z (l + W64 8) = sint.Z l + 8 ∧ sint.Z (l + W64 8) ≤ sint.Z c := by
  constructor <;> word

theorem room4 (l c : w64) (hroom : uint.Z (W64 4) ≤ uint.Z c - uint.Z l)
    (hwf : 0 ≤ sint.Z l ∧ sint.Z l ≤ sint.Z c) :
    sint.Z (l + W64 4) = sint.Z l + 4 ∧ sint.Z (l + W64 4) ≤ sint.Z c := by
  constructor <;> word

theorem ownSlice_split_app (k : w64) (s : GoSlice) (dq : DFrac) (head tail : List w8)
    (hk : sint.nat k = head.length) (hk0 : 0 ≤ sint.Z k)
    (hlen : (head ++ tail).length = sint.nat s.len) (hs : 0 ≤ sint.Z s.len) :
    (s ↦*{dq} (head ++ tail) : IProp GF) ⊢
      slice.slice s w8 (W64 0) k ↦*{dq} head ∗ slice.slice s w8 k s.len ↦*{dq} tail := by
  have hb : 0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z s.len ∧ sint.Z s.len ≤ sint.Z s.len := by
    simp only [List.length_append, sint.nat, sint.Z] at hlen hk hk0 hs ⊢
    refine ⟨hk0, ?_, Int.le_refl _⟩; omega
  refine (ownSlice_slice k s.len s dq _ hb).1.trans ?_
  have h1 : (head ++ tail).take (sint.nat k) = head := by rw [hk]; simp
  have h2 : subslice (sint.nat k) (sint.nat s.len) (head ++ tail) = tail := by
    simp only [subslice]; rw [← hlen, List.take_length, hk]; simp
  rw [h1, h2]
  iintro ⟨H1, H2, _⟩
  iframe

theorem arr_set_1 (x : w8) (kvs : List keyed_element) (h : go.arrayLiteralSize kvs = 1) :
    (zero_val (GoArray w8 (go.arrayLiteralSize kvs))).arr.set (sint.nat (W64 0)) x = [x] := by
  revert h
  generalize go.arrayLiteralSize kvs = n
  intro h; subst h; rfl

end wps

end github_com.tchajed.marshal

end Perennial
end
