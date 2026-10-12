/-
Rob Pike's "Google search" example, using the future channel idiom.

This file: the expected results and the contracts of
the three searches.
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.channel.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

namespace github_com.mit_pdos.perennial.goose.testdata.examples.channel

/-! ### Pure part -/

def googleExpected (q : GoString) : List GoString :=
  [q ++ go!".html", q ++ go!".png", q ++ go!".mp4"]

inductive Kind where
  | KWeb | KImg | KVid
  deriving DecidableEq

open Kind

def valueOf (q : GoString) (k : Kind) : GoString :=
  match k with
  | KWeb => q ++ go!".html"
  | KImg => q ++ go!".png"
  | KVid => q ++ go!".mp4"

def PureContractOf (q : GoString) (k : Kind) : GoString → Prop :=
  fun v => v = valueOf q k

theorem valueOf_inj (q : GoString) (k1 k2 : Kind) (h : valueOf q k1 = valueOf q k2) :
    k1 = k2 := by
  cases k1 <;> cases k2 <;> simp only [valueOf, List.append_cancel_left_eq] at h <;>
    first | rfl | exact absurd h (by decide)

theorem pureContractOf_inj (q : GoString) (k1 k2 : Kind) :
    PureContractOf q k1 = PureContractOf q k2 → k1 = k2 := by
  intro Heq
  have h := congrFun Heq (valueOf q k1)
  simp only [PureContractOf, eq_iff_iff, true_iff] at h
  exact valueOf_inj q k1 k2 h

def pendingk : List Kind := [KWeb, KImg, KVid]

theorem pendingk_nodup : pendingk.Nodup := by decide

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.channel.Assumptions]

def contractOf (q : GoString) (k : Kind) : GoString → IProp GF :=
  fun v => iprop(⌜PureContractOf q k v⌝)

theorem contractOf_sound (q : GoString) (k : Kind) (v : GoString) :
    contractOf (GF := GF) q k v ⊢ ⌜v = valueOf q k⌝ := by
  unfold contractOf PureContractOf
  iintro %Hv
  ipureintro
  exact Hv

theorem mem_map_contract_of (q : GoString) (remk : List Kind) (P : GoString → IProp GF) :
    P ∈ remk.map (contractOf q) → ∃ k, k ∈ remk ∧ P = contractOf q k := by
  intro HP
  obtain ⟨k, Hk, rfl⟩ := List.mem_map.1 HP
  exact ⟨k, Hk, rfl⟩

end proof

end github_com.mit_pdos.perennial.goose.testdata.examples.channel

end Perennial
