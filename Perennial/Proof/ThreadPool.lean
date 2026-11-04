/-
A **thread pool** of a resource `R`: a thread may exchange its thread token
(`threadTok`, `GooseLang/Threads.lean`) for one copy of `R`, and exchange it
back later, provided the pool was given at least `threadBound GF - 1` copies of
`R`.

The intended use is a resource of which a structure has a finite stock but of
which, in the real execution, only the *live threads* hold a copy at any time:
an `RWMutex`'s reader token (`sync.rwmutex.ownRLockToken`, of which the lock has
`actualMaxReaders`), which Go counts only while the reader is inside
`RLock`..`RUnlock`. A goroutine that holds such a token for its whole life
leaks it when it is abandoned (never joined); with a pool, it holds only its
thread token between its critical sections, borrows `R` for each one
(`borrow`) and gives it back after (`giveBack`), so no copy is ever lost.

Why the pool cannot run dry: it holds the `b` thread tokens of the copies lent
out (`threadToks b`) and the `m` copies left, with `threadBound GF ≤ b + m + 1`.
A borrower brings one more thread token, and `b + 1` thread tokens give
`b + 1 < threadBound GF` (`threadToks_add_one_lt`), so `m ≥ 1`. That is, the
copies lent out at one time are fewer than the live threads, which are fewer
than `threadBound GF`.

Each thread token borrows one copy at a time: a thread that needs two copies at
once (of the same pool, or of two pools) needs two thread tokens.

* `isThreadPool N γ R`: the pool (persistent).
* `ownThreadLoan γ`: a copy of `R` lent out; returned with the copy for the
  thread token.
* `init`: a pool from `n` copies, `threadBound GF ≤ n + 1`.
* `borrow` (`▷ R`), `borrow_timeless`, `borrow_lc` (with a later credit; for
  `HeapGS .hasLC GF`), and `giveBack`.
* The cancelable form, `isThreadPoolC N γ γc R` (`initC`, `borrowC`, `giveBackC`): a borrower
  holds a share of the pool's open half (`poolOpen γc q`); `cancel`, with the whole half, returns
  what the pool holds, and `reclaim` takes back a loan outstanding at the cancel. For a resource
  whose owner must get every copy back at the end of its life (a database's readers at its close).
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Proof.TokSet
public import Perennial.Golang.Theory.Pre

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

namespace threadPool

section pool
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

/-- The pool's invariant: `b` copies lent out, backed by their borrowers' thread tokens and
counted by `ownTokAuth γ b`, and `m` copies left, with `threadBound GF ≤ b + m + 1`. -/
def poolInv (γ : GName) (R : IProp GF) : IProp GF :=
  iprop(∃ (b m : Nat), ownTokAuth γ b ∗ threadToks b ∗
    ([∗list] _x ∈ List.replicate m (), R) ∗ ⌜threadBound GF ≤ b + m + 1⌝)

/-- A pool of copies of `R`, any of which a thread token borrows. -/
def isThreadPool (N : Namespace) (γ : GName) (R : IProp GF) : IProp GF :=
  inv N (poolInv γ R)

instance isThreadPool_persistent (N : Namespace) (γ : GName) (R : IProp GF) :
    Persistent (isThreadPool N γ R) := by
  unfold isThreadPool; infer_instance

/-- A copy of `R` lent out by the pool `γ`, for which the pool holds a thread token. -/
def ownThreadLoan (γ : GName) : IProp GF := ownToks γ 1

instance ownThreadLoan_timeless (γ : GName) : Timeless (ownThreadLoan (GF := GF) γ) := by
  unfold ownThreadLoan; infer_instance

/-- A pool from `n` copies of `R`, enough for every thread but one: `threadBound GF ≤ n + 1`. -/
theorem init (N : Namespace) (R : IProp GF) (E : CoPset) (n : Nat)
    (Hn : threadBound GF ≤ n + 1) :
    ([∗list] _x ∈ List.replicate n (), R) ⊢ |={E}=> ∃ γ, isThreadPool N γ R := by
  iintro HR
  imod ownTokAuth_alloc (GF := GF) with ⟨%γ, Hauth⟩
  imod inv_alloc N E (poolInv γ R) $$ [Hauth HR] with #Hinv
  · inext
    unfold poolInv
    iexists 0, n
    iframe
    isplitr
    · iapply threadToks_zero
    · ipureintro; omega
  imodintro
  iexists γ
  unfold isThreadPool
  iexact Hinv

/-- Borrow a copy of `R` with a thread token. -/
theorem borrow (N : Namespace) (γ : GName) (R : IProp GF) (E : CoPset) (HN : ↑N ⊆ E) :
    isThreadPool N γ R ∗ threadTok ⊢ |={E}=> ▷ R ∗ ownThreadLoan γ := by
  iintro ⟨#Hinv, Htok⟩
  unfold isThreadPool
  iinv Hinv with Hi Hclose
  unfold poolInv
  icases Hi with ⟨%b, %m, >Hauth, >Htoks, HR, >%Hle⟩
  icases threadToks_add_one_lt b $$ [Htok Htoks] with ⟨%Hlt, Htoks⟩
  · iframe
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  simp only [List.replicate]
  icases HR with ⟨HR, HRs⟩
  imod ownTokAuth_S γ b $$ Hauth with ⟨Hauth, Hloan⟩
  imod Hclose $$ [Hauth Htoks HRs] with _
  · inext
    iexists b + 1, m'
    iframe
    ipureintro; omega
  imodintro
  unfold ownThreadLoan
  iframe

/-- `borrow`, for a timeless `R`. -/
theorem borrow_timeless (N : Namespace) (γ : GName) (R : IProp GF) [Timeless R] (E : CoPset)
    (HN : ↑N ⊆ E) :
    isThreadPool N γ R ∗ threadTok ⊢ |={E}=> R ∗ ownThreadLoan γ := by
  iintro H
  imod borrow N γ R E HN $$ H with ⟨>HR, Hl⟩
  imodintro
  iframe

/-- Give a borrowed copy back, for the thread token. -/
theorem giveBack (N : Namespace) (γ : GName) (R : IProp GF) (E : CoPset) (HN : ↑N ⊆ E) :
    isThreadPool N γ R ∗ ownThreadLoan γ ∗ R ⊢ |={E}=> threadTok := by
  iintro ⟨#Hinv, Hloan, HR⟩
  unfold isThreadPool ownThreadLoan
  iinv Hinv with Hi Hclose
  unfold poolInv
  icases Hi with ⟨%b, %m, >Hauth, >Htoks, HRs, >%Hle⟩
  icombine Hauth Hloan gives %Hb
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  imod ownTokAuth_delete_S γ b' $$ Hauth Hloan with Hauth
  icases (threadToks_add b' 1).1 $$ Htoks with ⟨Htoks, Htok⟩
  imod Hclose $$ [Hauth Htoks HR HRs] with _
  · inext
    iexists b', m + 1
    simp only [List.replicate]
    iframe
    ipureintro; omega
  imodintro
  iexact Htok

/-! ### A cancelable pool

A pool whose copies can be taken back, once: `cancel`, with the whole of the pool's open half
(`poolOpen γc (1 : Qp).half`), returns what the pool holds, the copies left and the loans' count and
thread tokens. A borrower shows the pool is not canceled with a share of the open half (`poolOpen γc
q`), which it keeps. A loan outstanding at the cancel comes back with `reclaim`: its copy is the
borrower's, its thread token the pool's. -/

/-- The cancelable pool's invariant: open, with half of `γc` at `true` and the pool's invariant;
or canceled, with half of `γc` at `false`. -/
def poolInvC (γ γc : GName) (R : IProp GF) : IProp GF :=
  iprop((ghostVar γc (1 : Qp).half true ∗ poolInv γ R) ∨ ghostVar γc (1 : Qp).half false)

/-- A cancelable pool of copies of `R` (persistent). -/
def isThreadPoolC (N : Namespace) (γ γc : GName) (R : IProp GF) : IProp GF :=
  inv N (poolInvC γ γc R)

instance isThreadPoolC_persistent (N : Namespace) (γ γc : GName) (R : IProp GF) :
    Persistent (isThreadPoolC N γ γc R) := by
  unfold isThreadPoolC; infer_instance

/-- A share `q` of the pool's open half: the pool is not canceled. The whole half cancels. -/
def poolOpen (γc : GName) (q : Qp) : IProp GF := ghostVar γc q true

instance poolOpen_timeless (γc : GName) (q : Qp) : Timeless (poolOpen (GF := GF) γc q) := by
  unfold poolOpen; infer_instance

theorem poolOpen_split (γc : GName) (q1 q2 : Qp) :
    poolOpen (GF := GF) γc (q1 + q2) ⊣⊢ poolOpen γc q1 ∗ poolOpen γc q2 := by
  unfold poolOpen; exact (ghostVar_fractional γc true).fractional q1 q2

/-- A cancelable pool from `n` copies of `R`, with its whole open half. -/
theorem initC (N : Namespace) (R : IProp GF) (E : CoPset) (n : Nat)
    (Hn : threadBound GF ≤ n + 1) :
    ([∗list] _x ∈ List.replicate n (), R) ⊢
      |={E}=> ∃ γ γc, isThreadPoolC N γ γc R ∗ poolOpen γc (1 : Qp).half := by
  iintro HR
  imod ownTokAuth_alloc (GF := GF) with ⟨%γ, Hauth⟩
  imod ghostVar_alloc (GF := GF) true with ⟨%γc, Hc⟩
  icases (ghostVar_split_half γc 1 true).1 $$ Hc with ⟨Hc, Hc'⟩
  imod inv_alloc N E (poolInvC γ γc R) $$ [Hauth HR Hc] with #Hinv
  · inext
    unfold poolInvC poolInv
    ileft
    iframe Hc
    iexists 0, n
    iframe
    isplitr
    · iapply threadToks_zero
    · ipureintro; omega
  imodintro
  iexists γ, γc
  unfold isThreadPoolC poolOpen
  iframe Hc'
  iexact Hinv

/-- Borrow a copy of `R` with a thread token, from a pool not canceled. -/
theorem borrowC (N : Namespace) (γ γc : GName) (R : IProp GF) (q : Qp) (E : CoPset)
    (HN : ↑N ⊆ E) :
    isThreadPoolC N γ γc R ∗ poolOpen γc q ∗ threadTok ⊢
      |={E}=> ▷ R ∗ ownThreadLoan γ ∗ poolOpen γc q := by
  iintro ⟨#Hinv, Ho, Htok⟩
  unfold isThreadPoolC poolOpen
  iinv Hinv with Hi Hclose
  unfold poolInvC
  icases Hi with (⟨>Hc, Hi⟩ | >Hc)
  · unfold poolInv
    icases Hi with ⟨%b, %m, >Hauth, >Htoks, HR, >%Hle⟩
    icases threadToks_add_one_lt b $$ [Htok Htoks] with ⟨%Hlt, Htoks⟩
    · iframe
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [List.replicate]
    icases HR with ⟨HR, HRs⟩
    imod ownTokAuth_S γ b $$ Hauth with ⟨Hauth, Hloan⟩
    imod Hclose $$ [Hc Hauth Htoks HRs] with _
    · inext
      ileft
      iframe Hc
      iexists b + 1, m'
      iframe
      ipureintro; omega
    imodintro
    unfold ownThreadLoan
    iframe
  · icombine Ho Hc gives %Hft
    exact absurd Hft.2 (by decide)

/-- Give a borrowed copy back to a pool not canceled, for the thread token. -/
theorem giveBackC (N : Namespace) (γ γc : GName) (R : IProp GF) (q : Qp) (E : CoPset)
    (HN : ↑N ⊆ E) :
    isThreadPoolC N γ γc R ∗ poolOpen γc q ∗ ownThreadLoan γ ∗ R ⊢
      |={E}=> threadTok ∗ poolOpen γc q := by
  iintro ⟨#Hinv, Ho, Hloan, HR⟩
  unfold isThreadPoolC ownThreadLoan poolOpen
  iinv Hinv with Hi Hclose
  unfold poolInvC
  icases Hi with (⟨>Hc, Hi⟩ | >Hc)
  · unfold poolInv
    icases Hi with ⟨%b, %m, >Hauth, >Htoks, HRs, >%Hle⟩
    icombine Hauth Hloan gives %Hb
    obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    imod ownTokAuth_delete_S γ b' $$ Hauth Hloan with Hauth
    icases (threadToks_add b' 1).1 $$ Htoks with ⟨Htoks, Htok⟩
    imod Hclose $$ [Hc Hauth Htoks HR HRs] with _
    · inext
      ileft
      iframe Hc
      iexists b', m + 1
      simp only [List.replicate]
      iframe
      ipureintro; omega
    imodintro
    iframe
  · icombine Ho Hc gives %Hft
    exact absurd Hft.2 (by decide)

/-- **Cancel the pool**, with its whole open half: what it holds, the `m` copies left, and the
count of the `b` loans out with their thread tokens, `threadBound GF ≤ b + m + 1`. -/
theorem cancel (N : Namespace) (γ γc : GName) (R : IProp GF) (E : CoPset) (HN : ↑N ⊆ E) :
    isThreadPoolC N γ γc R ∗ poolOpen γc (1 : Qp).half ⊢
      |={E}=> ▷ ∃ (b m : Nat), ownTokAuth γ b ∗ threadToks b ∗
        ([∗list] _x ∈ List.replicate m (), R) ∗ ⌜threadBound GF ≤ b + m + 1⌝ := by
  iintro ⟨#Hinv, Ho⟩
  unfold isThreadPoolC poolOpen
  iinv Hinv with Hi Hclose
  unfold poolInvC
  icases Hi with (⟨>Hc, Hi⟩ | >Hc)
  · imod ghostVar_update_halves false γc true true $$ Ho Hc with ⟨Ho, Hc⟩
    imod Hclose $$ [Hc] with _
    · inext
      iright
      iexact Hc
    imodintro
    unfold poolInv
    iexact Hi
  · icombine Ho Hc gives %Hft
    exact absurd Hft.2 (by decide)

/-- **A loan outstanding at the cancel comes back**: its count goes down and its thread token is
returned (its copy of `R` is the borrower's). -/
theorem reclaim (γ : GName) (b : Nat) :
    ownTokAuth γ (b + 1) ∗ threadToks (b + 1) ∗ ownThreadLoan γ ⊢
      |==> ownTokAuth (GF := GF) γ b ∗ threadToks b ∗ threadTok := by
  iintro ⟨Hauth, Htoks, Hloan⟩
  unfold ownThreadLoan
  icases (threadToks_add b 1).1 $$ Htoks with ⟨Htoks, Htok⟩
  iframe Htoks Htok
  iapply ownTokAuth_delete_S γ b $$ Hauth Hloan

/-- With no loan out (`b = 0`), the copies left are at least `threadBound GF - 1`. -/
theorem canceled_none (m : Nat) (Hle : threadBound GF ≤ 0 + m + 1) : threadBound GF ≤ m + 1 := by
  omega

end pool

section lc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]

/-- `borrow`, the later taken off with a later credit. -/
theorem borrow_lc (N : Namespace) (γ : GName) (R : IProp GF) (E : CoPset) (HN : ↑N ⊆ E) :
    £ 1 ∗ isThreadPool N γ R ∗ threadTok ⊢ |={E}=> R ∗ ownThreadLoan γ := by
  iintro ⟨Hlc, H⟩
  imod borrow N γ R E HN $$ H with ⟨HR, Hl⟩
  imod lc_fupd_elim_later (E := E) $$ Hlc HR with HR
  imodintro
  iframe

end lc

end threadPool

end Perennial
