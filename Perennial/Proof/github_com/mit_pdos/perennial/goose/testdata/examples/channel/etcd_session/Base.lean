/-
An etcd-style session monitor, using a broadcast channel (`sessionc`) that is
closed (and replaced) whenever the session expires.

This file: the invariant of the package (`muInv`, `isInv`, the package's
`isPkgInit` instances) and helper lemmas.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Proof.errors.Base
public import Perennial.Proof.time.Base
public import Perennial.Proof.sync.Base
public import Perennial.Proof.github_com.goose_lang.primitive.Base
public import Perennial.Golang.Theory.Chan
public import Perennial.Golang.Theory.Chan.Idioms.Bag
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast
public import Perennial.GeneratedProof.github_com.mit_pdos.perennial.goose.testdata.examples.channel.etcd_session

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

namespace github_com.mit_pdos.perennial.goose.testdata.examples.channel.etcd_session

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.channel.etcd_session.Assumptions]

local notation "pkg" =>
  pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel.etcd_session

/-- The resources protected by `mu`: half of `sessionc` and the current
broadcast channel. -/
abbrev muInv : IProp GF :=
  iprop(∃ (ch : GoChan) (γch : ChanNames),
    "sessionc" ∷ typedPointsto (globalAddr sessionc) ch (DFrac.own (1 : Qp).half) ∗
    "#Hsessionc" ∷ ownBroadcastChan ch γch iprop(True) Broadcast.Unknown ∗
    "#Hsessionc_is" ∷ isChan ch γch Unit)

abbrev isInv : IProp GF :=
  iprop("#Hmu" ∷ sync.isMutex (globalAddr mu) muInv)

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg := define_is_pkg_init isInv
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg := build_get_is_pkg_init_wf

theorem isInv_access :
    isPkgInit (PROP := IProp GF) pkg ⊢ sync.isMutex (globalAddr mu) muInv := by
  with_unfolding_all exact isPkgInit_access (PROP := IProp GF) pkg

theorem pointsto_halves {V : Type} [TypedPointsto (GF := GF) V] (l : Loc) (v : V) :
    typedPointsto (GF := GF) l v (DFrac.own 1) ⊣⊢
      typedPointsto l v (DFrac.own (1 : Qp).half) ∗ typedPointsto l v (DFrac.own (1 : Qp).half) := by
  have h := (typedPointsto_dfractional (GF := GF) l v).dfractional
    (DFrac.own (1 : Qp).half) (DFrac.own (1 : Qp).half)
  rwa [DFrac.op_own, Qp.half_add_half] at h

/-- The postcondition of the nonblocking `select` in `monitorSession`. -/
abbrev monitorSelectPost (v : val) : IProp GF :=
  iprop(⌜v = executeVal⌝ ∗
    ∃ (ch : GoChan) (γch : ChanNames),
      "sessionc" ∷ typedPointsto (globalAddr sessionc) ch (DFrac.own 1) ∗
      "Hsessionc" ∷ ownBroadcastChan ch γch iprop(True) Broadcast.Pending ∗
      "#Hsessionc_is" ∷ isChan ch γch Unit)

end wps

end github_com.mit_pdos.perennial.goose.testdata.examples.channel.etcd_session

end Perennial
