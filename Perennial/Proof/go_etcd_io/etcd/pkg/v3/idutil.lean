/-
Port of `new/proof/go_etcd_io/etcd/pkg/v3/idutil.v`.

The specs are Rocq's (`isGenerator g R`, `Generator.wp_Next` without
precondition, `wp_NewGenerator`), except that `Next`'s postcondition gives the
token `R i` under a premise on the time-receipt bound:
`⌜receiptBound GF ≤ 2 ^ 48⌝ -∗ R i` (Rocq: `R i`). Calling `Next` and
`NewGenerator` is always safe (the specs hold for every bound); only the token
is conditional. Deviation from Rocq: `Generator.wp_Next`, admitted in Rocq
(after `2^48` calls the IDs wrap around and the invariant has no `R` tokens
left), is proved using *time receipts* (`Perennial/GooseLang/Receipts.lean`):
every call of `Next` collects one exclusive receipt `⧗ 1` (from its first Go
instruction) into the invariant of `isGenerator`, so the invariant owns
`⧗ num_used`, and `⧗ (num_used + 1)` bounds `num_used + 1 < receiptBound GF`.
The bound is an unspecified parameter `N` of the program logic; when
`N ≤ 2^48` a token is left, and otherwise (no token left) the premise of the
postcondition is contradictory. A client of the adequacy theorem
(`goose_adequacy N ...`) discharges the premise by choosing some `N ≤ 2^48`,
and the conclusion is then about executions of fewer than `N` steps.
-/
import Perennial.Proof.ProofPrelude
import Perennial.Code.go_etcd_io.etcd.pkg.v3.idutil
import Perennial.GeneratedProof.go_etcd_io.etcd.pkg.v3.idutil
import Perennial.Proof.time
import Perennial.Proof.math
import Perennial.Proof.sync.atomic

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace go_etcd_io.etcd.pkg.v3.idutil

/-- The IDs handed out by a fresh `Generator` (prefix `p`, initial suffix `s`)
are distinct values in `[0, 2^64)`. -/
theorem ids_subperm (p s : Int) (hp : 0 ≤ p ∧ p < 2 ^ 16) :
    ((seqZ (s + 1) (2 ^ 48)).map (fun i => p * 2 ^ 48 + i % 2 ^ 48)).Subperm (seqZ 0 (2 ^ 64)) := by
  have h48 : (2 : Int) ^ 48 = 281474976710656 := by decide
  have h64 : (2 : Int) ^ 64 = 18446744073709551616 := by decide
  have h16 : (2 : Int) ^ 16 = 65536 := by decide
  apply List.subperm_of_subset
  · unfold List.Nodup
    rw [List.pairwise_map]
    refine (NoDup_seqZ (s + 1) (2 ^ 48)).imp_of_mem ?_
    intro a b ha hb hne heq
    rw [elem_of_seqZ] at ha hb
    rw [h48] at ha hb heq
    omega
  · intro x hx
    rw [List.mem_map] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    rw [elem_of_seqZ]
    rw [h48, h64]; rw [h16] at hp
    omega

theorem bigSepL_subperm {GF : BundledGFunctors} {A : Type _} (Φ : A → IProp GF) {l₁ l₂ : List A}
    (h : l₁.Subperm l₂) : ([∗list] x ∈ l₂, Φ x) ⊢ [∗list] x ∈ l₁, Φ x := by
  obtain ⟨l, hperm, hsub⟩ := h
  obtain ⟨rest, hrest⟩ := hsub.exists_perm_append
  have h1 : ([∗list] x ∈ l₂, Φ x) ⊢ [∗list] x ∈ l, Φ x := BigSepL.bigSepL_submseteq hrest.symm
  have h2 : ([∗list] x ∈ l, Φ x) ⊢ [∗list] x ∈ l₁, Φ x := (BigSepL.bigSepL_perm hperm).1
  exact h1.trans h2

/-- `2^48` is abstracted as `N`: elaborating or kernel-checking terms whose
types mention `seqZ _ (2^48)` may evaluate `List.range (2^48)`. -/
theorem ids_bigSepL_sub {GF : BundledGFunctors} (R : w64 → IProp GF) (p s : Int)
    (hp : 0 ≤ p ∧ p < 2 ^ 16) (L : List Int) (hL : L = seqZ 0 (2 ^ 64)) (N : Int)
    (hN : N = 2 ^ 48) :
    ([∗list] i ∈ L, R (W64 i)) ⊢
      [∗list] i ∈ seqZ (s + 1) N, R (W64 (p * N + i % N)) := by
  subst hN
  have hs := ids_subperm p s hp
  rw [← hL] at hs
  generalize seqZ (s + 1) (2 ^ 48) = L1 at hs ⊢
  have h := bigSepL_subperm (fun i => R (W64 i)) hs
  rw [BigSepL.bigSepL_map] at h
  exact h

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : idutil.Assumptions]

local notation "pkg" => pkg_id.go_etcd_io.etcd.pkg.v3.idutil

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg :=
  build_get_is_pkg_init_wf

/-! ### Time receipts for `Next` (Lean addition)

Rocq's `isGenerator g R` lets any number of callers run `Next`, but its
invariant owns only `2^48` of the `R` tokens. Here the invariant also owns one
time receipt per call made so far; since `receiptBound GF` receipts are
contradictory, under the premise `receiptBound GF ≤ 2^48` fewer than
`2^48 - 1` calls have completed when a new one starts, so a token is left
(`take_token`). Without the premise `Next` still runs; the invariant then
just keeps an empty token list. -/

/-- (Rocq FIXME:) id.go says that the overflowing of cnt into timestamp is
intentional "to extend the event window to 2^56". However, there are only 48
bits in the suffix, and the documentation is a typo from an older version of
the code.

Lean deviation: the invariant additionally owns the time receipts of the
`num_used` calls made so far (`"Hused"`, with `"%Hnum_used" : 0 ≤ num_used`).
Rocq: invariant `suffix ∗ HR` only. -/
def isGeneratorDef (g : Loc) (R : w64 → IProp GF) : IProp GF :=
  iprop(∃ («prefix» : Int),
    "#prefix" ∷ g.[Generator, go!"prefix"] ↦□ (W64 («prefix» * 2^48)) ∗
    "#Hinv" ∷
      inv nroot iprop(∃ (init num_used : Int),
          "suffix" ∷ g.[Generator, go!"suffix"] ↦ W64 (init + num_used) ∗
          "%Hnum_used" ∷ ⌜0 ≤ num_used⌝ ∗
          "Hused" ∷ ⧗ num_used.toNat ∗
          "HR" ∷ ([∗list] i ∈ seqZ (init + num_used + 1) (2^48 - num_used),
                    R (W64 («prefix» * 2^48 + i % 2^48)))) ∗
    "_" ∷ True)
/-- (Rocq: `Opaque isGenerator`) -/
@[irreducible] def isGenerator (g : Loc) (R : w64 → IProp GF) : IProp GF :=
  isGeneratorDef g R
theorem isGenerator_unseal : @isGenerator = @isGeneratorDef := by
  funext; with_unfolding_all rfl

instance isGenerator_pers (g : Loc) (R : w64 → IProp GF) :
    Persistent (isGenerator g R) := by
  rw [isGenerator_unseal]; unfold isGeneratorDef; infer_instance

theorem lowbit_eq (x n : w64) (H : 0 < uint.Z n ∧ uint.Z n < 64) :
    x &&& (W64 18446744073709551615 >>> (W64 64 - n)) = W64 (uint.Z x % 2 ^ uint.nat n) := by
  have hk : 0 < n.toNat ∧ n.toNat < 64 := by simp only [uint.Z] at H; omega
  apply BitVec.eq_of_toNat_eq
  have h1 : (W64 18446744073709551615 >>> (W64 64 - n)).toNat = 2 ^ n.toNat - 1 := by
    rw [BitVec.ushiftRight_eq', BitVec.toNat_ushiftRight]
    have : (W64 64 - n).toNat = 64 - n.toNat := by
      rw [BitVec.toNat_sub]; simp [W64]; omega
    rw [this]
    have : (W64 18446744073709551615).toNat = 2^64 - 1 := by decide
    rw [this, Nat.shiftRight_eq_div_pow]
    have hp : 2^64 = 2^n.toNat * 2^(64 - n.toNat) := by rw [← Nat.pow_add]; congr 1; omega
    have hQ : 0 < 2^(64 - n.toNat) := Nat.two_pow_pos _
    have hP : 0 < 2^n.toNat := Nat.two_pow_pos _
    rw [hp]
    apply Nat.div_eq_of_lt_le
    · rw [Nat.sub_mul, Nat.one_mul]; omega
    · generalize 2^n.toNat = P at *
      generalize 2^(64 - n.toNat) = Q at *
      rw [Nat.sub_add_cancel hP]
      have : P * Q ≥ 1 := Nat.mul_pos hP hQ
      omega
  rw [BitVec.toNat_and, h1, Nat.and_two_pow_sub_one_eq_mod]
  simp only [W64, uint.Z, uint.nat]
  have hlt : x.toNat % 2 ^ n.toNat < 2^64 :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
      (Nat.pow_le_pow_right (by decide) (by omega))
  rw [show ((x.toNat : Int) % 2 ^ n.toNat) = ((x.toNat % 2 ^ n.toNat : Nat) : Int) by push_cast; rfl]
  rw [BitVec.ofInt_natCast, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]

/-- Specialized to 48 low bits. (NOTE (Rocq): need `0 < uint.Z n` because
there's no guarantees about `word.sru` when the shift amount is the width.) -/
theorem wp_lowbit (x n : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ ⌜0 < uint.Z n ∧ uint.Z n < 64⌝ }}
      (App (App (Val (@! lowbit)) (Val #x)) (Val #n))
    {{ RET #(W64 (uint.Z x % 2 ^ uint.nat n)); True }} := by
  wp_start as %H
  wp_auto
  rw [lowbit_eq x n H]
  wp_end

theorem or_prefix (p : Int) (x : Int) :
    W64 (p * 2^48) ||| W64 (x % 2^48) = W64 (p * 2^48 + x % 2^48) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or]
  have hx0 : 0 ≤ x % 2^48 := Int.emod_nonneg _ (by decide)
  have hx1 : x % 2^48 < 2^48 := Int.emod_lt_of_pos _ (by decide)
  have e1 : (W64 (p * 2^48)).toNat = 2^48 * (p % 2^16).toNat := by
    simp only [W64, BitVec.toNat_ofInt]
    omega
  have e2 : (W64 (x % 2^48)).toNat = (x % 2^48).toNat := by
    simp only [W64, BitVec.toNat_ofInt]
    omega
  have e3 : (W64 (p * 2^48 + x % 2^48)).toNat = 2^48 * (p % 2^16).toNat + (x % 2^48).toNat := by
    simp only [W64, BitVec.toNat_ofInt]
    omega
  rw [e1, e2, e3, Nat.two_pow_add_eq_or_of_lt (by omega)]

/-- Taking the token of the next ID out of the invariant's token list, given
`n + 1 < M` for the number `n` of completed calls (from the receipts) and the
receipt bound `M`: when `n < 2^48` the list is nonempty and the token is
returned unconditionally; otherwise the list is empty and the premise
`M ≤ 2^48` is contradictory. -/
theorem take_token (Φ : Int → IProp GF) (a n : Int) (M : Nat) (hlt : n.toNat + 1 < M) :
    ([∗list] i ∈ seqZ (a + 1) (2 ^ 48 - n), Φ i) ⊢
      (⌜M ≤ 2 ^ 48⌝ -∗ Φ (a + 1)) ∗ [∗list] i ∈ seqZ (a + 1 + 1) (2 ^ 48 - (n + 1)), Φ i := by
  by_cases h : n < 2 ^ 48
  · rw [seqZ_cons _ _ (by omega), show 2 ^ 48 - n - 1 = 2 ^ 48 - (n + 1) by omega]
    iintro ⟨Hi, HR⟩
    iframe HR
    iintro _
    iexact Hi
  · rw [seqZ_nil (a + 1 + 1) (2 ^ 48 - (n + 1)) (by omega)]
    iintro -
    isplitl []
    · iintro %hM
      exfalso
      omega
    · iapply BigSepL.bigSepL_nil.2
      iempintro

/-- Lean deviation: proved (Rocq: admitted) using time receipts, for every
time-receipt bound; the postcondition gives `R i` under the premise
`receiptBound GF ≤ 2^48` (Rocq: `R i`), see the module docstring. -/
theorem Generator.wp_Next (g : Loc) (R : w64 → IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ isGenerator g R }}
      (App (Val (g @!! go.GoType.PointerType Generator.ty @!! go!"Next")) (Val #()))
    {{ (i : w64), RET #i; ⌜receiptBound GF ≤ 2 ^ 48⌝ -∗ R i }} := by
  wp_start as H
  rw [isGenerator_unseal]; unfold isGeneratorDef
  icases H with ⟨%pfx, #Hpfx, #Hinv, -⟩
  wp_alloc g_ptr as Hg
  wp_pure
  wp_pure
  -- a time receipt from a Go instruction (the zero value of `suffix`)
  wp_bind (App (Val (GoInstruction (GoZeroVal _))) (Val _))
  iapply wp_go_step_receipt'
  inext
  iintro Htk _
  wp_auto
  wp_apply_core sync.atomic.wp_AddUint64 $$ [] [-]
  · iPkgInit
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  icases Hi with ⟨%init, %num_used, suffix', %Hnum_used, Hused, HR⟩
  icases receipt_add_one_lt _ $$ [Htk Hused] with ⟨%Hlt, Hused⟩
  · iframe
  iexists _
  iframe suffix'
  iintro suffix'
  icases take_token (fun i => R (W64 (pfx * 2 ^ 48 + i % 2 ^ 48))) (init + num_used) num_used
    (receiptBound GF) Hlt $$ HR with ⟨HRi, HR⟩
  imod Hmask with -
  imod Hclose $$ [suffix' Hused HR] with -
  · inext
    iexists init, num_used + 1
    rw [show W64 (init + num_used) + W64 1 = W64 (init + (num_used + 1)) by word,
      show (num_used + 1).toNat = num_used.toNat + 1 by omega,
      show init + num_used + 1 + 1 = init + (num_used + 1) + 1 by omega]
    iframe
    ipureintro; omega
  imodintro
  wp_auto
  wp_apply wp_lowbit
  · ipureintro; word
  have e : uint.Z (W64 (init + num_used) + W64 1) % 2 ^ 48 = (init + num_used + 1) % 2 ^ 48 := by
    rw [show W64 (init + num_used) + W64 1 = W64 (init + num_used + 1) by word]
    simp only [uint.Z, W64, BitVec.toNat_ofInt]
    omega
  rw [e, or_prefix]
  iapply HΦ $$ HRi

/-- Allocating the invariant of `isGenerator` (`2^48` is kept abstract as `N`,
see `ids_bigSepL_sub`). -/
theorem isGenerator_alloc (R : w64 → IProp GF) (L : List Int) (hL : L = seqZ 0 (2^64)) (g : Loc)
    (memberID : w16) (sv : w64) :
    ⊢ g.[Generator, go!"prefix"] ↦ W64 (uint.Z memberID * 2 ^ 48) -∗
      g.[Generator, go!"suffix"] ↦ sv -∗
      ([∗list] i ∈ L, R (W64 i)) ={⊤}=∗
      isGenerator g R := by
  iintro prefix' suffix HR
  imod receipt_zero (GF := GF) with H0
  have hp : 0 ≤ uint.Z memberID ∧ uint.Z memberID < 2 ^ 16 := by word
  ipersist prefix'
  obtain ⟨N, hN⟩ : ∃ N : Int, N = 2 ^ 48 := ⟨_, rfl⟩
  rw [← hN]
  imod inv_alloc nroot ⊤ iprop(∃ (init num_used : Int),
          "suffix" ∷ g.[Generator, go!"suffix"] ↦ W64 (init + num_used) ∗
          "%Hnum_used" ∷ ⌜0 ≤ num_used⌝ ∗
          "Hused" ∷ ⧗ num_used.toNat ∗
          "HR" ∷ ([∗list] i ∈ seqZ (init + num_used + 1) (N - num_used),
                    R (W64 (uint.Z memberID * N + i % N)))) $$ [suffix HR H0] with #Hinv
  · inext
    iexists (uint.Z sv), 0
    have hw : ∀ x : w64, W64 (uint.Z x) = x := fun x => by word
    simp only [Int.add_zero, Int.sub_zero, hw, Int.toNat_zero]
    iframe suffix
    isplitr
    · ipureintro; omega
    iframe H0
    iapply (ids_bigSepL_sub R _ _ hp L hL N hN)
    iexact HR
  imodintro
  rw [isGenerator_unseal]; unfold isGeneratorDef
  rw [← hN]
  iexists (uint.Z memberID)
  iframe #

/-- `wp_NewGenerator` with the list `seqZ 0 (2^64)` abstracted as `L`. -/
theorem wp_NewGenerator' (R : w64 → IProp GF)
    (memberID : w16) (now : time.Time) (L : List Int) (hL : L = seqZ 0 (2^64)) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗
        ([∗list] i ∈ L, R (W64 i)) }}
      (App (App (Val (@! NewGenerator)) (Val #memberID)) (Val #now))
    {{ (g : Loc), RET #g; isGenerator g R }} := by
  wp_start as HR
  wp_auto
  wp_apply time.Time.wp_UnixNano $$ [$now] as %nowNano now
  wp_apply wp_lowbit
  · ipureintro; word
  wp_alloc g as Hg
  iapply wp_fupd
  wp_auto
  iStructNamed Hg
  have hpre : (W64 (uint.Z memberID) <<< W64 48 : w64) = W64 (uint.Z memberID * 2 ^ 48) := by
    word
  rw [hpre]
  imod isGenerator_alloc R L hL g memberID
    (W64 (uint.Z (nowNano / BitVec.sdiv (W64 1000000) (W64 1)) % 2 ^ 40) <<< W64 8 : w64)
    $$ prefix' suffix HR with Hgen
  iapply HΦ $$ Hgen

/-- (Rocq TODO:) this is overly conservative. Really should only demand `R` for
the range of IDs with future timestamps, since the old ones might've been used
before a crash+restart. -/
theorem wp_NewGenerator (R : w64 → IProp GF)
    (memberID : w16) (now : time.Time) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗
        ([∗list] i ∈ seqZ 0 (2^64), R (W64 i)) }}
      (App (App (Val (@! NewGenerator)) (Val #memberID)) (Val #now))
    {{ (g : Loc), RET #g; isGenerator g R }} :=
  wp_NewGenerator' R memberID now _ rfl

end wps

end go_etcd_io.etcd.pkg.v3.idutil

end Perennial
end
