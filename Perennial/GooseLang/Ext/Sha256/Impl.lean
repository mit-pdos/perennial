/-
The SHA-256 extension of GooseLang [Trusted definitions!].

The hash primitive of Go's `crypto/sha256` (the model of `Sum256`,
`Perennial/TrustedCode/crypto/sha256.lean`, calls it on the input's bytes). Its
global state is every input hashed so far, with its hash.

* `sha256Hash` is SHA-256: an opaque function from byte strings to 32 bytes,
  so that a proof knows of it only that it is a function.
* `Sum (data)` hashes `data`: `h := sha256Hash data`. If the run's filter
  allows it (`ok m data h`, with `m` the inputs hashed so far), the step
  records `data ↦ h` and returns `h` as a `[32]byte`; otherwise the step is an
  `AngelicExit`: the run is not one the program's theorem covers.
* The filter `ok` is the extension's parameter, fixed for the run. With
  `sha256NoFilter`, which allows every step, the model removes no execution.
  A theorem that assumes `Sha256NoCollision ok` covers only the runs in which
  no hash of the run equals the hash of a different input of the run.
* Initial states (`ExtSemantics.initGlobal`): nothing hashed.
-/
module

public import Perennial.GooseLang.Lang

@[expose] public section

namespace Perennial

instance : Inhabited {h : List w8 // h.length = 32} := ⟨⟨List.replicate 32 0, by simp⟩⟩

/-- SHA-256. -/
opaque sha256Hash : GoString → {h : List w8 // h.length = 32}

/-- The inputs hashed so far, each with its hash. -/
abbrev Sha256State := GMap GoString (List w8)

instance : Inhabited Sha256State := ⟨∅⟩

/-- Which steps of the hash a run allows: `ok m data h`, for the inputs `m`
hashed so far, an input `data` and its hash `h`. -/
abbrev Sha256Filter := Sha256State → GoString → List w8 → Prop

/-- The filter that allows every step: the faithful model. -/
def sha256NoFilter : Sha256Filter := fun _ _ _ => True

/-- **The no-collision assumption.** The filter `ok` allows the hash step to
return a hash `h` for an input `data` only if no other input hashed before
has the hash `h`. -/
def Sha256NoCollision (ok : Sha256Filter) : Prop :=
  ∀ m data h, ok m data h → ∀ d, m !! d = some h → d = data

/-- The filter that allows exactly the steps that cause no collision: the hash `h` of `data`
is not the hash of another input hashed before. -/
def sha256NoCollisionFilter : Sha256Filter := fun m data h => ∀ d, m !! d = some h → d = data

/-- The name of the SHA-256 extension: the path of the Go package it implements. -/
abbrev sha256ExtName : String := "crypto/sha256"

/-- The SHA-256 extension, with the filter `ok`. It has no values or local
state of its own. -/
def sha256Ext (_ok : Sha256Filter) : GooseExt where
  name := sha256ExtName
  Val := Empty
  LocalState := Unit
  GlobalState := Sha256State

section sha256
variable [GooseExts] [GoGlobalContext]

/-- The step relation of the hash, with the filter `ok`. -/
def Sha256Step (ok : Sha256Filter) (op : String) (v : val) (h : GMap Loc (NonAtomic val))
    (s : Unit) (m : Sha256State) (e' : Expr) (h' : GMap Loc (NonAtomic val)) (s' : Unit)
    (m' : Sha256State) : Prop :=
  h' = h ∧ s' = s ∧
  match op with
  | "Sum" => ∃ data : GoString, v = #data ∧
      ((ok m data (sha256Hash data).val ∧
          e' = Val (#(⟨(sha256Hash data).val⟩ : GoArray w8 32)) ∧
          m' = <[data := (sha256Hash data).val]> m) ∨
        (¬ ok m data (sha256Hash data).val ∧
          e' = App (Val (GoInstruction AngelicExit)) (Val (#())) ∧ m' = m))
  | _ => False

end sha256

/-- The semantics of the hash, with the filter `ok`. A run starts with nothing hashed
(`initGlobal`): the global state records the inputs hashed by the run. -/
instance sha256_semantics (ok : Sha256Filter) : ExtSemantics (sha256Ext ok) where
  step := Sha256Step ok
  crash _ _ := True
  initGlobal m := @Eq Sha256State m ∅

end Perennial
