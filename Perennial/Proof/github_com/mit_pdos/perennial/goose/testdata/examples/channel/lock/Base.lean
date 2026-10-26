/-
Shared definitions of the proof of the goose lock example, a lock implemented with a
buffered channel of capacity 1 (the lock channel idiom): the package's `isPkgInit`
instances and the lock predicate `isLock`.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Golang.Theory.Chan
public import Perennial.Golang.Theory.Chan.Idioms.Lock
public import Perennial.Golang.Theory.Chan.Idioms.Bag
public import Perennial.Proof.strings.Base
public import Perennial.Proof.time.Base
public import Perennial.GeneratedProof.github_com.mit_pdos.perennial.goose.testdata.examples.channel.lock

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

namespace github_com.mit_pdos.perennial.goose.testdata.examples.channel.lock

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [package_sem : lock.Assumptions]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel.lock :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel.lock :=
  build_get_is_pkg_init_wf

end init

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.channel.lock.Assumptions]

def isLock (γ : LockChannelNames) (l : Lock) (R : IProp GF) : IProp GF :=
  iprop("#Hlock_chan" ∷ isLockChannel Unit γ l.ch' R)

instance isLock_persistent (γ : LockChannelNames) (l : Lock) (R : IProp GF) :
    Persistent (isLock γ l R) := by
  unfold isLock; infer_instance

end proof

end github_com.mit_pdos.perennial.goose.testdata.examples.channel.lock

end Perennial
