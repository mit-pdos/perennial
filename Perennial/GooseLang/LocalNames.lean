/-
The generation's supply of ghost names.

A package-level fact (`isPkgInit`) is a proposition of the ghost state alone: it cannot take
a ghost name as an argument, and a ghost name fixed in a typeclass instance would be the same
for every generation, while ghost state allocated by one generation's proof is gone after a
crash. A library whose fact must name ghost state of the run (a table behind a package
variable, a ghost model of a package variable whose resources are handed out before the
package initializes) names it through this supply instead: a ghost map from keys (strings, by
convention the Go package path of the library) to ghost names, one per generation
(`GoStateGS.localNamesName`, part of the generation's package state, allocated with the rest of
its local ghost state).

* `ownLocalNames m`: the authority of the generation's map (exclusive). The adequacy theorems
  hand `ownLocalNames ∅` to the generation's program (`goose_adequacy_localNames`,
  `goose_crash_adequacy_localNames`, ...), so a proof knows that no key is set at the start of
  a run.
* `localName k γ`: the generation records `γ` under `k` (persistent). Two records of a key
  agree (`localName_agree`), and a key absent from the map can be set once (`localName_set`).

So a proof allocates the library's ghost state at the start of the run, records its name
(`localName_set`), and the package's fact says `∃ γ, localName k γ ∗ ...`: every reader of the
fact in the same generation agrees on `γ`. A record of a crashed generation is over that
generation's map, not the new one's.
-/
module

public import Perennial.GooseLang.Lifting

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI ProofMode

section local_names
variable {GF : BundledGFunctors} [hG : GoStateGS GF]

/-- The authority of the generation's map from keys to ghost names (exclusive); the
adequacy theorems hand `ownLocalNames ∅` to the generation's program. -/
def ownLocalNames (m : GMap GoString GName) : IProp GF :=
  letI := hG.package_mono_allG
  ghostMapAuth hG.localNamesName 1 m

/-- The generation records the ghost name `γ` under the key `k` (persistent). -/
def localName (k : GoString) (γ : GName) : IProp GF :=
  letI := hG.package_mono_allG
  k ↪[hG.localNamesName]□ γ

instance localName_persistent (k : GoString) (γ : GName) :
    Persistent (localName (GF := GF) k γ) := by
  letI := hG.package_mono_allG
  unfold localName; infer_instance

instance localName_timeless (k : GoString) (γ : GName) :
    Timeless (localName (GF := GF) k γ) := by
  letI := hG.package_mono_allG
  unfold localName; infer_instance

instance ownLocalNames_timeless (m : GMap GoString GName) :
    Timeless (ownLocalNames (GF := GF) m) := by
  letI := hG.package_mono_allG
  unfold ownLocalNames; infer_instance

/-- Two records of a key name the same ghost name. -/
theorem localName_agree (k : GoString) (γ γ' : GName) :
    ⊢ localName (GF := GF) k γ -∗ localName k γ' -∗ ⌜γ = γ'⌝ := by
  letI := hG.package_mono_allG
  unfold localName
  exact ghostMapElem_agree k _ _ _ γ γ'

/-- Record `γ` under a key that has no name yet. -/
theorem localName_set {m : GMap GoString GName} {k : GoString} (h : m !! k = none)
    (γ : GName) :
    ⊢ ownLocalNames (GF := GF) m ==∗ ownLocalNames (<[k := γ]> m) ∗ localName k γ := by
  letI := hG.package_mono_allG
  unfold ownLocalNames localName
  exact ghost_map_insert_persist k γ h

end local_names

/-- Allocate a generation's supply (for the adequacy theorems): a ghost name `γn`, with the
authority of the empty map, which is `ownLocalNames ∅` of a package state whose supply is `γn`
(`goStateGSUpdatePre … γn`, `ownLocalNames_goStateGSUpdatePre`). -/
theorem localNames_init {GF : BundledGFunctors} (hA : AllG GF) :
    ⊢@{IProp GF} |==> ∃ γn : GName, letI := hA; ghostMapAuth γn 1 (∅ : GMap GoString GName) :=
  letI := hA
  ghost_map_alloc_empty

theorem ownLocalNames_goStateGSUpdatePre {GF : BundledGFunctors} (hT : GoStatePreG GF)
    (hA : AllG GF) (γ γm γn : GName) (m : GMap GoString GName) :
    ownLocalNames (hG := goStateGSUpdatePre GF hT hA γ γm γn) m =
      (letI := hA; ghostMapAuth γn 1 m) := rfl

end Perennial
