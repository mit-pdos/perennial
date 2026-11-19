/-
Iris reasoning principles for the SHA-256 extension.

* `sha256IsHash ok hG data h`: `h` is the hash of `data`, `sha256Hash data`; and, if the run's
  filter allows no collision (`Sha256NoCollision ok`), the persistent element `h.arr ↦ data` of
  a ghost map from the hashes recorded so far to their inputs, whose authority is in the
  interpretation of the hash's state. Persistent.
* `sha256IsHash_det`, `sha256IsHash_len`: a hash is a function of the input, of 32 bytes; and
  `sha256IsHash_inj`, under `Sha256NoCollision ok`: two inputs with the same hash are equal.
* `wp_Sha256Sum`: the hash step returns some `h` with `sha256IsHash ok hG data h`, or exits
  angelically.
-/
module

public import Perennial.GooseLang.Lifting
public import Perennial.GooseLang.Ext.Sha256.Impl
public import Perennial.Golang.Theory.PostLifting
public import Perennial.Ghost.GhostMap

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Classical

private theorem sha256_ite_pos {α : Sort _} {p : Prop} [Decidable p] (h : p) (a b : α) :
    (if p then a else b) = a := by simp [h]

private theorem sha256_ite_neg {α : Sort _} {p : Prop} [Decidable p] (h : ¬ p) (a b : α) :
    (if p then a else b) = b := by simp [h]

/-- The filter of exactly the steps without a collision allows no collision. -/
theorem sha256NoCollisionFilter_noCollision : Sha256NoCollision sha256NoCollisionFilter :=
  fun _ _ _ hok d hd => hok d hd

/-- The ghost state of the hash: a ghost map from each recorded hash to its input. -/
structure Sha256GS (GF : BundledGFunctors) where
  allG : AllG GF
  hashName : GName

section ghost
variable {GF : BundledGFunctors}

/-- The interpretation of the hash's state `m`, with the filter `ok`: every recorded hash is its
input's `sha256Hash`; if `ok` allows no collision, the authority of the ghost map `r` from each
recorded hash to its input (so that `m` is injective), with `r`'s persistent elements. -/
def sha256Ctx (ok : Sha256Filter) (hG : Sha256GS GF) (m : Sha256State) : IProp GF :=
  letI := hG.allG
  iprop(⌜∀ d h, m !! d = some h → h = (sha256Hash d).val⌝ ∗
    if Sha256NoCollision ok then
      iprop(∃ r : GMap (List w8) GoString,
        ghostMapAuth hG.hashName 1 r ∗ ([∗map] h ↦ d ∈ r, h ↪[hG.hashName]□ d) ∗
        ⌜∀ d h, m !! d = some h ↔ r !! h = some d⌝)
    else iprop(True))

/-- `h` is the hash of `data`, and, if `ok` allows no collision, `data` is the input recorded
with the hash `h`. -/
def sha256IsHash (ok : Sha256Filter) (hG : Sha256GS GF) (data : GoString) (h : GoArray w8 32) :
    IProp GF :=
  letI := hG.allG
  iprop(⌜h.arr = (sha256Hash data).val⌝ ∗
    if Sha256NoCollision ok then iprop(h.arr ↪[hG.hashName]□ data)
    else iprop(True))

instance sha256IsHash_persistent (ok : Sha256Filter) (hG : Sha256GS GF) (data : GoString)
    (h : GoArray w8 32) : Persistent (sha256IsHash ok hG data h) := by
  letI := hG.allG
  unfold sha256IsHash
  split <;> infer_instance

theorem sha256IsHash_det (ok : Sha256Filter) (hG : Sha256GS GF) (data : GoString)
    (h1 h2 : GoArray w8 32) :
    sha256IsHash ok hG data h1 ∗ sha256IsHash ok hG data h2 ⊢ ⌜h1 = h2⌝ := by
  unfold sha256IsHash
  iintro ⟨⟨%H1, -⟩, ⟨%H2, -⟩⟩
  ipureintro
  cases h1; cases h2
  simp only at H1 H2
  rw [H1, H2]

theorem sha256IsHash_len (ok : Sha256Filter) (hG : Sha256GS GF) (data : GoString)
    (h : GoArray w8 32) :
    sha256IsHash ok hG data h ⊢ ⌜h.arr.length = 32⌝ := by
  unfold sha256IsHash
  iintro ⟨%H, -⟩
  ipureintro
  rw [H]; exact (sha256Hash data).property

theorem sha256IsHash_inj (ok : Sha256Filter) (Hok : Sha256NoCollision ok) (hG : Sha256GS GF)
    (data1 data2 : GoString) (h : GoArray w8 32) :
    sha256IsHash ok hG data1 h ∗ sha256IsHash ok hG data2 h ⊢ ⌜data1 = data2⌝ := by
  letI := hG.allG
  unfold sha256IsHash
  rw [sha256_ite_pos Hok, sha256_ite_pos Hok]
  iintro ⟨⟨-, H1⟩, ⟨-, H2⟩⟩
  iapply ghostMapElem_agree $$ H1 H2

/-- Recording `data`'s hash keeps every recorded hash its input's. -/
theorem sha256_recorded_insert {m : Sha256State} (data : GoString)
    (Hm : ∀ d h, m !! d = some h → h = (sha256Hash d).val) :
    ∀ d h, (<[data := (sha256Hash data).val]> m : Sha256State) !! d = some h →
      h = (sha256Hash d).val := by
  intro d h Hd
  rcases (GMap.lookup_insert_Some _ _ _ _ _).mp Hd with ⟨rfl, rfl⟩ | ⟨-, Hd⟩
  · rfl
  · exact Hm d h Hd

/-- Recording `data`'s hash, new in `r`, keeps `r` the inverse of `m`. -/
theorem sha256_inverse_insert {m : Sha256State} {r : GMap (List w8) GoString} (data : GoString)
    (Hm : ∀ d h, m !! d = some h → h = (sha256Hash d).val)
    (Hr : ∀ d h, m !! d = some h ↔ r !! h = some d)
    (Hnone : r !! (sha256Hash data).val = none) :
    ∀ d h, (<[data := (sha256Hash data).val]> m : Sha256State) !! d = some h ↔
      (<[(sha256Hash data).val := data]> r) !! h = some d := by
  intro d h
  rw [GMap.lookup_insert_Some, GMap.lookup_insert_Some]
  constructor
  · rintro (⟨rfl, rfl⟩ | ⟨hd, Hd⟩)
    · exact .inl ⟨rfl, rfl⟩
    · refine .inr ⟨?_, (Hr d h).mp Hd⟩
      rintro rfl
      rw [(Hr d _).mp Hd] at Hnone; cases Hnone
  · rintro (⟨rfl, rfl⟩ | ⟨hh, Hh⟩)
    · exact .inl ⟨rfl, rfl⟩
    · refine .inr ⟨?_, (Hr d h).mpr Hh⟩
      rintro rfl
      exact hh (Hm _ _ ((Hr _ h).mpr Hh)).symm

theorem sha256_global_init (ok : Sha256Filter) (hPre : AllG GF) :
    ⊢@{IProp GF} |==> ∃ hG : Sha256GS GF, sha256Ctx ok hG ∅ ∗ iprop(True) := by
  letI := hPre
  imod (ghost_map_alloc_empty (GF := GF) (K := List w8) (V := GoString)) with ⟨%γ, Ha⟩
  imodintro
  iexists (⟨hPre, γ⟩ : Sha256GS GF)
  isplitl [Ha]
  · unfold sha256Ctx
    isplitr
    · ipureintro; intro d h Hd; simp at Hd
    · split
      · iexists ∅
        iframe Ha
        isplitr
        · iapply BigSepM.bigSepM_empty.2; iempintro
        · ipureintro; intro d h; simp
      · itrivial
  · itrivial

end ghost

/-- The ghost state of the hash, with the filter `ok`. The run starts with nothing hashed. -/
instance sha256_interp (ok : Sha256Filter) : ExtInterp (sha256Ext ok) where
  LocalGS _ := Unit
  GlobalGS := Sha256GS
  localCtx _ _ := iprop(True)
  globalCtx := sha256Ctx ok
  PreG := AllG
  initgP m := @Eq Sha256State m ∅
  initP _ _ := True
  globalStart _ _ := iprop(True)
  localStart _ _ := iprop(True)
  global_init _ hPre m Hm := by
    change @Eq Sha256State m ∅ at Hm
    rw [show m = (∅ : Sha256State) from Hm]
    exact sha256_global_init ok hPre
  local_init _ _ _ _ _ := by
    iapply bupd_intro
    iexists ()
    isplitl [] <;> itrivial

/-! ## Specs -/

/-- The program's extensions include the SHA-256 extension, with the filter `ok` (an
`outParam`: a context with `[HasSha256 ok]` determines `ok`, so that `is_hash data h` and the
specs need not name it). -/
class HasSha256 [GooseExts] [GooseSemantics] [GooseInterp] (ok : outParam Sha256Filter) :
    Prop where
  hasExt : HasExt (sha256Ext ok)

attribute [instance] HasSha256.hasExt

section lifting
variable [GooseExts] [GooseSemantics] [GooseInterp] {ok : Sha256Filter}
  [HasSha256 ok] [GoGlobalContext] [go.IntoValInj GoString]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable [GoSemanticsFunctions] [go.PreSemantics]
variable {s : Stuckness} {E : CoPset}

/-- The ghost state of the program's hash. -/
abbrev gooseSha256GS : Sha256GS GF :=
  (extGlobalGS (sha256Ext ok) (G := G) : (sha256_interp ok).GlobalGS GF)

theorem sha256_global_ctx_eq (m : Sha256State) :
    ExtInterp.globalCtx (E := sha256Ext ok) (extGlobalGS (sha256Ext ok)) m ⊣⊢
      sha256Ctx ok (gooseSha256GS (ok := ok) (G := G)) m := .rfl

/-- The hash step: some `h` with `sha256IsHash`, or an angelic exit. -/
theorem wp_Sha256Sum (data : GoString) (Φ : val → IProp GF) :
    (∀ h : GoArray w8 32, sha256IsHash ok (gooseSha256GS (ok := ok) (G := G)) data h -∗ Φ (#h))
    ⊢ WP (ExternalOp sha256ExtName "Sum" (Val (#data))) @ s; E {{ Φ }} := by
  show _ ⊢ WP (ExternalOp (sha256Ext ok).name "Sum" (Val (#data))) @ s; E {{ Φ }}
  iintro HΦ
  iapply wp_extStep (X := sha256Ext ok) "Sum" (#data) Φ (GoGlobalContext.intoVal_not_panic _)
  iintro %hp %σ %m Hheap Hl Hg
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    by_cases Hok : ok m data (sha256Hash data).val
    · exact ⟨_, hp, σ, _, rfl, rfl, data, rfl, .inl ⟨Hok, rfl, rfl⟩⟩
    · exact ⟨_, hp, σ, _, rfl, rfl, data, rfl, .inr ⟨Hok, rfl, rfl⟩⟩
  inext
  iintro %e' %h' %σ' %m' %Hst _
  obtain ⟨rfl, rfl, data', Hv, Hcase⟩ := Hst
  obtain rfl := go.intoVal_inj (V := GoString) Hv
  imod Hclose
  rcases Hcase with ⟨Hok, rfl, rfl⟩ | ⟨-, rfl, rfl⟩
  · -- the hash is recorded and returned
    icases (sha256_global_ctx_eq (ok := ok) (G := G) m).mp $$ Hg with Hg
    letI := (gooseSha256GS (ok := ok) (G := G)).allG
    unfold sha256Ctx
    icases Hg with ⟨%Hm, Hr⟩
    have Hm' := sha256_recorded_insert data Hm
    by_cases Hnc : Sha256NoCollision ok
    · rw [sha256_ite_pos Hnc]
      icases Hr with ⟨%r, Ha, #Hrs, %Hr⟩
      cases Hget : r !! (sha256Hash data).val with
      | none =>
        imod ghost_map_insert_persist (sha256Hash data).val data Hget $$ Ha with ⟨Ha, #He⟩
        imodintro
        iframe Hheap Hl
        isplitl [Ha]
        · iapply (sha256_global_ctx_eq (ok := ok) (G := G) _).mpr
          unfold sha256Ctx
          isplitr
          · ipureintro; exact Hm'
          rw [sha256_ite_pos Hnc]
          iexists _
          iframe Ha
          isplitr
          · iapply (BigSepM.bigSepM_insert (Φ := fun h d =>
              iprop(h ↪[(gooseSha256GS (ok := ok) (G := G)).hashName]□ d)) Hget).2
            iframe He Hrs
          · ipureintro; exact sha256_inverse_insert data Hm Hr Hget
        iapply wp_value'
        iapply HΦ
        unfold sha256IsHash
        rw [sha256_ite_pos Hnc]
        iframe He
        ipureintro; rfl
      | some d =>
        -- the hash was recorded, with `data` (no collision): the state is unchanged
        have Hd : d = data := Hnc m data _ Hok d ((Hr d _).mpr Hget)
        subst Hd
        have Hin := (Hr d _).mpr Hget
        rw [GMap.insert_id _ _ _ Hin]
        ihave #He := BigSepM.bigSepM_lookup (Φ := fun h d =>
          iprop(h ↪[(gooseSha256GS (ok := ok) (G := G)).hashName]□ d)) Hget $$ Hrs
        imodintro
        iframe Hheap Hl
        isplitl [Ha]
        · iapply (sha256_global_ctx_eq (ok := ok) (G := G) m).mpr
          unfold sha256Ctx
          isplitr
          · ipureintro; exact Hm
          rw [sha256_ite_pos Hnc]
          iexists r
          iframe Ha Hrs
          ipureintro; exact Hr
        iapply wp_value'
        iapply HΦ
        unfold sha256IsHash
        rw [sha256_ite_pos Hnc]
        iframe He
        ipureintro; rfl
    · rw [sha256_ite_neg Hnc]
      imodintro
      iframe Hheap Hl
      isplitl [Hr]
      · iapply (sha256_global_ctx_eq (ok := ok) (G := G) _).mpr
        unfold sha256Ctx
        isplitr
        · ipureintro; exact Hm'
        rw [sha256_ite_neg Hnc]
        itrivial
      iapply wp_value'
      iapply HΦ
      unfold sha256IsHash
      rw [sha256_ite_neg Hnc]
      isplitr
      · ipureintro; rfl
      itrivial
  · -- the hash is refused: the run exits angelically
    imodintro
    iframe Hheap Hl Hg
    iapply wp_AngelicExit

end lifting

end Perennial
