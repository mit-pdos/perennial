/-
Shared definitions of the proofs of the Go `io` package: its `isPkgInit` (the fixed
`Discard` writer and the `errors.New` errors, `EOF`, ...).
-/
module

public import Perennial.Proof.sync.Base
public import Perennial.Proof.errors.Base
public import Perennial.Proof.errors.NewVar
public import Perennial.Code.io
public import Perennial.GeneratedProof.io

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace io

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : io.Assumptions]

/-- The package-initialized state (persistent; Go never writes these variables after
initialization):
* `"#HDiscard"`: `Discard` holds a fixed `Writer` (`go.etcd.io/raft/v3`'s initializer loads it);
* `"#HEOF"`, ...: each error variable made by `errors.New` holds that error, a fixed
  `*errorString` whose `Error()` returns its message (`errors.newVar`): what a client comparing
  an error against `io.EOF` (or `ErrUnexpectedEOF`, ...) needs of it. -/
abbrev isInit : IProp GF :=
  iprop("#HDiscard" ∷ (∃ w : GoInterface, typedPointsto (globalAddr Discard) w DFrac.discard) ∗
  "#HErrShortWrite" ∷ errors.newVar ErrShortWrite go!"short write" ∗
  "#HerrInvalidWrite" ∷ errors.newVar errInvalidWrite go!"invalid write result" ∗
  "#HErrShortBuffer" ∷ errors.newVar ErrShortBuffer go!"short buffer" ∗
  "#HEOF" ∷ errors.newVar EOF go!"EOF" ∗
  "#HErrUnexpectedEOF" ∷ errors.newVar ErrUnexpectedEOF go!"unexpected EOF" ∗
  "#HErrNoProgress" ∷
    errors.newVar ErrNoProgress go!"multiple Read calls return no data or error" ∗
  "#HerrWhence" ∷ errors.newVar errWhence go!"Seek: invalid whence" ∗
  "#HerrOffset" ∷ errors.newVar errOffset go!"Seek: invalid offset" ∗
  "#HErrClosedPipe" ∷ errors.newVar ErrClosedPipe go!"io: read/write on closed pipe" ∗
  "_" ∷ True)

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.io :=
  define_is_pkg_init isInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.io :=
  build_get_is_pkg_init_wf

theorem isInit_access :
    isPkgInit (PROP := IProp GF) pkg_id.io ⊢ isInit (GF := GF) := by
  with_unfolding_all exact isPkgInit_access (PROP := IProp GF) pkg_id.io

/-- `io.EOF` holds `errors.New("EOF")`. -/
theorem eof_of_init :
    isPkgInit (PROP := IProp GF) pkg_id.io ⊢ errors.newVar (GF := GF) EOF go!"EOF" := by
  iintro Hinit
  ihave Hi := isInit_access $$ Hinit
  icases Hi with ⟨-, -, -, -, HEOF, -⟩
  iexact HEOF

end wps

end io

end Perennial
