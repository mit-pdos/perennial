/-
Port of `new/proof/github_com/mit_pdos/perennial/goose/testdata/examples/channel_search_replace.v`:
a parallel search-and-replace over a slice, with work items sent over a channel
(bag idiom) and completion tracked by a `sync.WaitGroup` (join idiom).
-/
import Perennial.Proof.ProofPrelude
import Perennial.Golang.Theory.Chan
import Perennial.Golang.Theory.Chan.Idioms.Bag
import Perennial.Proof.sync_proof.waitgroup_join
import Perennial.Proof.time
import Perennial.GeneratedProof.github_com.mit_pdos.perennial.goose.testdata.examples.channel.parallel_search_replace

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

namespace github_com.mit_pdos.perennial.goose.testdata.examples.channel.parallel_search_replace

section init
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [sem : go.Semantics] [package_sem : parallel_search_replace.Assumptions]

instance is_pkg_init_inst :
    IsPkgInit (IProp GF)
      pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel.parallel_search_replace :=
  define_is_pkg_init iprop(True)
instance get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF)
      pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel.parallel_search_replace :=
  build_get_is_pkg_init_wf

end init

/-- Ghost state over channels of slices needs `Pos.Countable slice.t` (Rocq derives it). -/
instance slice_countable : Pos.Countable slice.t :=
  .ofInjective (fun s => Pos.Countable.encode (s.ptr, s.len, s.cap))
    (by rintro ⟨a, b, c⟩ ⟨d, e, f⟩ h; have h := Pos.encode_inj h; simp_all)

structure SearchReplace_names where
  wg : sync.WaitGroup_names
  wg_added : GName

def search_replace (x y : w64) (l : List w64) : List w64 :=
  l.map (fun a => if a = x then y else a)

@[simp] theorem search_replace_length (x y : w64) (l : List w64) :
    (search_replace x y l).length = l.length := by
  simp [search_replace]

section proof
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : heapGS HasLC.hasLC GF] [allG GF]
variable [sem : go.Semantics] [package_sem : parallel_search_replace.Assumptions]

local notation "pkg" =>
  pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel.parallel_search_replace

def chanP (wg : loc) (x y : w64) (s : slice.t) : IProp GF :=
  iprop(∃ xs : List w64,
    "Hxs" ∷ s ↦* xs ∗
    "Hwg_done" ∷ sync.join.own_Done wg (s ↦* (search_replace x y xs)))

def waitgroupN : Namespace := nroot.@"waitgroup"

set_option goose.wp.extras true

theorem wp_worker (γs : chan_names) (ch : loc) (wg : loc) (x y : w64) :
    {{ is_pkg_init (PROP := IProp GF) pkg ∗
        "#Hchan" ∷ is_chan_bag γs ch (chanP wg x y) }}
      (App (App (App (App (Val (@! worker)) (Val #ch)) (Val #wg)) (Val #x)) (Val #y))
    {{ RET #(); True }} := by
  wp_start as #Hchan
  wp_auto
  sorry

end proof

end github_com.mit_pdos.perennial.goose.testdata.examples.channel.parallel_search_replace

end Perennial
