/-
The "join" idiom for `WaitGroup` with its counter backed by **thread tokens**
(`sync.tokJoin`): as `WaitGroupJoin` (`Add` hands out permission to call
`Done` with a chosen proposition, `Wait` collects all of them), except that
the counter's bound comes from the goroutines running, not from the number of
`Add`s since the last `Wait`.

* `WaitGroupJoin`'s `Add` needs `num_added < 2^31 - 1`, the `Add`s since the
  last `Wait`. A program that runs `wg.Add(1); go f()` once per element of a
  collection of unknown size, or for as long as requests come, has no such
  bound; what bounds its counter is that each unit of it is a goroutine that
  has not yet called `Done`, and the model bounds the goroutines alive
  (`threadBound GF ≤ 2^31`, a premise).
* Here each `Add(1)` deposits the caller's thread token in the counter's
  slot for the goroutine about to start (the caller gets a fresh one at its
  `go` statement, `wp_fork_tok_self`), and each `Done` takes one back (the one
  the goroutine exits with). The counter is the number of deposited tokens,
  so below `threadBound GF`.
* A goroutine may **lend** its slot's token (`lend_acc`): take the token out
  (to spend it on another thread-token-backed structure, e.g. the `Add` of a
  wait group of goroutines it starts) and leave a receipt `L` in the slot,
  and later refill the slot with a thread token and take the receipt back
  (`unlend_acc`). What `L` is, and why the lent slots still bound the counter,
  is the client's: a persistent **lending law** (`lendLaw N L`, given at
  `init`) says that `n` thread tokens and `b` receipts satisfy
  `n + b < threadBound GF`, at a mask outside the join's namespace `N` (e.g.
  by opening the invariant that holds the lent tokens). With no lending,
  `L := False` (`lendLaw_false`).

The specs are proved from `WaitGroup`'s specs, taken as hypotheses
(`WaitGroup.wp_Add_of`, ...), as in `WaitGroupJoin`; `Results` applies them to
the linked results (`sync.tokJoin.WaitGroup.wp_Add`, `wp_Done`, `wp_Wait`).
-/
module

public import Perennial.Proof.sync.Base
public import Perennial.Proof.sync.WaitGroupDefs
public import Perennial.Proof.sync.WaitGroupJoin
public import Perennial.Spec.sync.WaitGroup__Add
public import Perennial.Spec.sync.WaitGroup__Done
public import Perennial.Spec.sync.WaitGroup__Wait

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

namespace sync

namespace tokJoin

structure TokJoinNames where
  wgGn : WaitGroupNames
  /-- The propositions of the `Done`s (`ownAprop`). -/
  apGn : GName
  /-- The goroutines added and not done. -/
  ndGn : GName
  /-- The slots holding their thread token. -/
  depGn : GName
  /-- The slots lent out (holding a receipt). -/
  lentGn : GName

section waitgroup_tok_join_idiom
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

/-- `b` receipts `L`. -/
def receipts (L : IProp GF) : Nat → IProp GF
  | 0 => iprop(emp)
  | b + 1 => iprop(L ∗ receipts L b)

instance receipts_timeless (L : IProp GF) [Timeless L] (b : Nat) : Timeless (receipts L b) := by
  induction b with
  | zero => simp only [receipts]; infer_instance
  | succ b ih => simp only [receipts]; infer_instance

/-- **The lending law**: `n` thread tokens and `b` receipts `L` (in the slots lent out) satisfy
`n + b < threadBound GF`; at a mask outside the join's namespace `N`, so that it may open the
invariant where the lent tokens are. -/
def lendLaw (N : Namespace) (L : IProp GF) : IProp GF :=
  iprop(□ ∀ (n b : Nat), threadToks n -∗ receipts L b ={⊤ \ ↑N}=∗
    ⌜n + b < threadBound GF⌝ ∗ threadToks n ∗ receipts L b)

instance lendLaw_persistent (N : Namespace) (L : IProp GF) : Persistent (lendLaw N L) := by
  unfold lendLaw; infer_instance

/-- The body of the internal invariant: the counter is the goroutines added and not done
(`added - done`), each with its slot's thread token (`j` of them, tickets `depGn`) or a receipt
(`b`, tickets `lentGn`); the propositions of the `Done`s so far. -/
def tjInv (γ : TokJoinNames) (L : IProp GF) : IProp GF :=
  iprop(∃ (ctr : w32) (added done j b : Nat) (Pdone : IProp GF),
    ownWaitGroup γ.wgGn ctr ∗
    ownTokAuthDfrac γ.ndGn (DFrac.own (1 : Qp).half) added ∗ ownToks γ.ndGn done ∗
    ownApropFrag γ.apGn Pdone done ∗ Pdone ∗
    threadToks j ∗ ownTokAuth γ.depGn j ∗ receipts L b ∗ ownTokAuth γ.lentGn b ∗
    ⌜0 ≤ sint.Z ctr ∧ sint.Z ctr = (added : Int) - done ∧ (added : Int) - done = j + b⌝)

/-- The join's wait group, invariant and lending law (persistent). -/
def isTokJoin (N : Namespace) (L : IProp GF) (wg : Loc) (γ : TokJoinNames) : IProp GF :=
  iprop(isWaitGroup wg γ.wgGn (N.@"wg") ∗ inv (N.@"inv") (tjInv γ L) ∗ lendLaw N L ∗
    ⌜threadBound GF ≤ 2 ^ 31⌝)

instance isTokJoin_persistent (N : Namespace) (L : IProp GF) (wg : Loc) (γ : TokJoinNames) :
    Persistent (isTokJoin N L wg γ) := by
  unfold isTokJoin; infer_instance

/-- **Permission to call `Add` or `Wait`** (`n` added since the last `Wait`): `Add` extends `P`
with a caller-chosen proposition, `Wait` gives `P` and resets the permission. -/
def ownAdder (N : Namespace) (L : IProp GF) (wg : Loc) (n : Nat) (P : IProp GF) : IProp GF :=
  iprop(∃ (γ : TokJoinNames) (P' : IProp GF),
    ownWaitGroupWaiters γ.wgGn 0 ∗ ownApropAuth γ.apGn P' n ∗
    ownTokAuthDfrac γ.ndGn (DFrac.own (1 : Qp).half) n ∗ (P' -∗ P) ∗ isTokJoin N L wg γ)

/-- **Permission to call `Done` with `P`**, the slot's thread token deposited. -/
def ownDone (N : Namespace) (L : IProp GF) (wg : Loc) (P : IProp GF) : IProp GF :=
  iprop(∃ γ : TokJoinNames,
    ownAprop γ.apGn P ∗ ownToks γ.ndGn 1 ∗ ownToks γ.depGn 1 ∗ isTokJoin N L wg γ)

/-- **The same, the slot's thread token lent out** (a receipt `L` in its place). -/
def ownLent (N : Namespace) (L : IProp GF) (wg : Loc) (P : IProp GF) : IProp GF :=
  iprop(∃ γ : TokJoinNames,
    ownAprop γ.apGn P ∗ ownToks γ.ndGn 1 ∗ ownToks γ.lentGn 1 ∗ isTokJoin N L wg γ)

/-- No lending: the receipt `False`. -/
theorem lendLaw_false (N : Namespace) : ⊢ lendLaw (GF := GF) N iprop(False) := by
  unfold lendLaw
  imodintro
  iintro %n %b Hn Hr
  cases b with
  | zero =>
    ihave %Hlt := threadToks_lt n $$ Hn
    imodintro
    iframe
    ipureintro; omega
  | succ b =>
    simp only [receipts]
    icases Hr with ⟨Hf, -⟩
    iexfalso; iexact Hf

theorem init (N : Namespace) (L : IProp GF) (wg : Loc) (γwg : WaitGroupNames) (E : CoPset)
    (Hb : threadBound GF ≤ 2 ^ 31) :
    isWaitGroup (GF := GF) wg γwg (N.@"wg") ∗ ownWaitGroup γwg (W32 0) ∗
      ownWaitGroupWaiters γwg 0 ∗ lendLaw N L ⊢ |={E}=> ownAdder N L wg 0 iprop(True) := by
  iintro ⟨#His, Hctr, Hwait, #Hlaw⟩
  imod ownApropAuth_alloc (GF := GF) with ⟨%γap, Hap⟩
  imod ownTokAuth_alloc (GF := GF) with ⟨%γnd, Hnd⟩
  icases (join.ownTokAuth_halves γnd 0).1 $$ Hnd with ⟨Hnd1, Hnd2⟩
  imod ownToks_0 (GF := GF) γnd with Hnd0
  ihave Hfrag := ownApropFrag_0 (GF := GF) γap
  imod ownTokAuth_alloc (GF := GF) with ⟨%γdep, Hdep⟩
  imod ownTokAuth_alloc (GF := GF) with ⟨%γlent, Hlent⟩
  let γ : TokJoinNames := ⟨γwg, γap, γnd, γdep, γlent⟩
  imod inv_alloc (N.@"inv") E (tjInv (GF := GF) γ L) $$ [Hctr Hnd1 Hnd0 Hfrag Hdep Hlent]
    with #Hinv
  · inext
    unfold tjInv
    iexists W32 0, 0, 0, 0, 0, iprop(True)
    simp only [γ, receipts]
    iframe
    isplitr
    · iexact Hfrag
    isplitr
    · iapply threadToks_zero
    ipureintro
    exact ⟨by decide, by decide, by simp⟩
  imodintro
  unfold ownAdder
  iexists γ, iprop(True)
  simp only [γ]
  iframe Hwait Hap Hnd2
  isplitr
  · iintro _; itrivial
  unfold isTokJoin
  iframe #
  ipureintro; exact Hb

theorem ownAdder_wand (P' : IProp GF) (N : Namespace) (L : IProp GF) (wg : Loc) (n : Nat)
    (P : IProp GF) :
    ⊢ (P -∗ P') -∗ ownAdder N L wg n P -∗ ownAdder N L wg n P' := by
  iintro Hw Ha
  unfold ownAdder
  icases Ha with ⟨%γ, %P0, Hwait, Hap, Hadded, Himp, #Hj⟩
  iexists γ, P0
  iframe Hwait Hap Hadded Hj
  iintro H
  iapply Hw
  iapply Himp $$ H

/-- **Lending a slot's thread token**: the token out, and (at the same mask, when the receipt is
there) the receipt `L` into the slot. An accessor, so that the token can be spent inside an atomic
update that produces the receipt. -/
theorem lend_acc (N : Namespace) (L : IProp GF) (wg : Loc) (P : IProp GF) (E : CoPset)
    (HE : ↑(N.@"inv") ⊆ E) :
    ownDone N L wg P ⊢ |={E, E \ ↑(N.@"inv")}=>
      threadTok ∗ (L ={E \ ↑(N.@"inv"), E}=∗ ownLent N L wg P) := by
  iintro Hd
  unfold ownDone
  icases Hd with ⟨%γ, Hap, Hnd, Hdep_tok, #Hj⟩
  ihave #Hj2 := Hj
  iunfold isTokJoin at Hj2
  icases Hj2 with ⟨-, #Hinv, -⟩
  imod inv_acc (E := E) HE $$ Hinv with ⟨Hi, Hclose⟩
  iunfold tjInv at Hi
  icases Hi with ⟨%ctr, %added, %done, %j, %b, %Pdone, Hwgo, Hadded, Hdone_toks, Hdone_ap,
    HPdone, >Hjt, >Hdep, Hrc, >Hlent, >%Hctr⟩
  icombine Hdep Hdep_tok gives %Hj1
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  icases (threadToks_add j' 1).1 $$ Hjt with ⟨Hjt, Htok⟩
  imod ownTokAuth_delete_S γ.depGn j' $$ Hdep Hdep_tok with Hdep
  imod ownTokAuth_S γ.lentGn b $$ Hlent with ⟨Hlent, Hlent_tok⟩
  imodintro
  iframe Htok
  iintro HL
  imod Hclose $$ [Hwgo Hadded Hdone_toks Hdone_ap HPdone Hjt Hdep Hrc HL Hlent] with -
  · inext
    unfold tjInv
    iexists ctr, added, done, j', b + 1, Pdone
    simp only [receipts]
    iframe
    ipureintro
    obtain ⟨h0, h1, h2⟩ := Hctr
    refine ⟨h0, h1, by push_cast at h2 ⊢; omega⟩
  imodintro
  unfold ownLent
  iexists γ
  iframe Hap Hnd Hlent_tok Hj

/-- **Refilling a lent slot**: the receipt `L` out, and (at the same mask, when the token is
there) a thread token into the slot. An accessor, so that the receipt can be handed on and the slot
refilled at once, e.g. at a fork (`wp_fork_tok_upd`). -/
theorem unlend_acc (N : Namespace) (L : IProp GF) [Timeless L] (wg : Loc) (P : IProp GF)
    (E : CoPset) (HE : ↑(N.@"inv") ⊆ E) :
    ownLent N L wg P ⊢ |={E, E \ ↑(N.@"inv")}=>
      L ∗ (threadTok ={E \ ↑(N.@"inv"), E}=∗ ownDone N L wg P) := by
  iintro Hd
  unfold ownLent
  icases Hd with ⟨%γ, Hap, Hnd, Hlent_tok, #Hj⟩
  ihave #Hj2 := Hj
  iunfold isTokJoin at Hj2
  icases Hj2 with ⟨-, #Hinv, -⟩
  imod inv_acc (E := E) HE $$ Hinv with ⟨Hi, Hclose⟩
  iunfold tjInv at Hi
  icases Hi with ⟨%ctr, %added, %done, %j, %b, %Pdone, Hwgo, Hadded, Hdone_toks, Hdone_ap,
    HPdone, >Hjt, >Hdep, >Hrc, >Hlent, >%Hctr⟩
  icombine Hlent Hlent_tok gives %Hb1
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  simp only [receipts]
  icases Hrc with ⟨HL, Hrc⟩
  imod ownTokAuth_delete_S γ.lentGn b' $$ Hlent Hlent_tok with Hlent
  imod ownTokAuth_S γ.depGn j $$ Hdep with ⟨Hdep, Hdep_tok⟩
  imodintro
  iframe HL
  iintro Htok
  ihave Hjt := (threadToks_add j 1).2 $$ [Hjt Htok]
  · iframe
  imod Hclose $$ [Hwgo Hadded Hdone_toks Hdone_ap HPdone Hjt Hdep Hrc Hlent] with -
  · inext
    unfold tjInv
    iexists ctr, added, done, j + 1, b', Pdone
    iframe
    ipureintro
    obtain ⟨h0, h1, h2⟩ := Hctr
    refine ⟨h0, h1, by push_cast at h2 ⊢; omega⟩
  imodintro
  unfold ownDone
  iexists γ
  iframe Hap Hnd Hdep_tok Hj

/-- Lending a slot's thread token, the receipt in hand. -/
theorem lend (N : Namespace) (L : IProp GF) (wg : Loc) (P : IProp GF) (E : CoPset)
    (HE : ↑(N.@"inv") ⊆ E) :
    ownDone N L wg P ∗ L ⊢ |={E}=> ownLent N L wg P ∗ threadTok := by
  iintro ⟨Hd, HL⟩
  imod lend_acc N L wg P E HE $$ Hd with ⟨Htok, Hclose⟩
  imod Hclose $$ HL with Hl
  imodintro
  iframe

/-- Refilling a lent slot, the thread token in hand. -/
theorem unlend (N : Namespace) (L : IProp GF) [Timeless L] (wg : Loc) (P : IProp GF)
    (E : CoPset) (HE : ↑(N.@"inv") ⊆ E) :
    ownLent N L wg P ∗ threadTok ⊢ |={E}=> ownDone N L wg P ∗ L := by
  iintro ⟨Hl, Htok⟩
  imod unlend_acc N L wg P E HE $$ Hl with ⟨HL, Hclose⟩
  imod Hclose $$ Htok with Hd
  imodintro
  iframe

/-- The thread-token join's `WaitGroup.Add(1)`, by the caller with its thread token, which the new
slot holds: a `Done` right for the goroutine about to start. From `WaitGroup.Add`'s spec (the
result `sync.tokJoin.WaitGroup.wp_Add` is this applied to `sync.WaitGroup.wp_Add`, in
`Results`). -/
theorem WaitGroup.wp_Add_of
    (wp_Add : sync.WaitGroup.Add.spec (GF := GF) (hG := hG))
    (P' : IProp GF) (N : Namespace) (L : IProp GF) [Timeless L] (wg : Loc) (n : Nat)
    (P : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ ownAdder N L wg n P ∗ threadTok }}
      (App (Val (wg @!! go.GoType.PointerType WaitGroup.ty @!! go!"Add")) (Val #(W64 1)))
    {{ RET #(); ownAdder N L wg (n + 1) iprop(P ∗ P') ∗ ownDone N L wg P' }} := by
  wp_start_folded as ⟨Had, Htok⟩
  unfold ownAdder
  icases Had with ⟨%γ, %P0, Hwait, Hap, Hadded, Himp, #Hj⟩
  ihave #Hj2 := Hj
  iunfold isTokJoin at Hj2
  icases Hj2 with ⟨#Hwg, #Hinv, #Hlaw, %Hb⟩
  wp_apply_core wp_Add wg (W64 1) γ.wgGn (N.@"wg") $$ [] [-]
  · iframe #
  imod inv_acc (E := ⊤) (fun _ _ => CoPset.mem_full) $$ Hinv with ⟨Hi, Hclose⟩
  iunfold tjInv at Hi
  icases Hi with ⟨%ctr, %added, %done, %j, %b, %Pdone, Hwgo, >Hadded_inv, Hdone_toks, Hdone_ap,
    HPdone, >Hjt, >Hdep, >Hrc, Hlent, >%Hctr⟩
  icases threadToks_add_one_lt j $$ [Htok Hjt] with ⟨-, Hjt⟩
  · iframe
  have Hm : (⊤ \ ↑N : CoPset) ⊆ ⊤ \ ↑(N.@"inv") := by
    intro p hp
    rw [LawfulSet.mem_diff] at hp ⊢
    exact ⟨hp.1, fun h => hp.2 (nclose_subseteq N "inv" p h)⟩
  imod fupd_mask_subseteq Hm with Hmask
  iunfold lendLaw at Hlaw
  imod Hlaw $$ %(j + 1) %b Hjt Hrc with ⟨%Hlt, Hjt, Hrc⟩
  imod Hmask with -
  iapply fupd_mask_intro (wg_mask_ndot_ne N "wg" "inv" (by decide))
  iintro Hmask
  inext
  icombine Hadded Hadded_inv gives %Hc
  obtain ⟨-, Heq⟩ := Hc
  subst Heq
  obtain ⟨Hc0, Hc1, Hc2⟩ := Hctr
  have h1 : sint.Z (W32 (sint.Z (W64 1))) = 1 := by decide
  have h2 : W32 (sint.Z (W64 1)) = W32 1 := by decide
  have hz : sint.Z (ctr + W32 1) = sint.Z ctr + 1 := by word
  iexists ctr
  iframe Hwgo
  isplitr
  · ipureintro; rw [h1]; omega
  iright
  iframe Hwait
  iintro Hwait Hwgo
  imod Hmask with -
  imod ownApropAuth_add P' γ.apGn P0 n $$ Hap with ⟨Hap, Hdone_ap'⟩
  ihave Hadded := (join.ownTokAuth_halves γ.ndGn n).2 $$ [Hadded Hadded_inv]
  · iframe
  imod ownTokAuth_S γ.ndGn _ $$ Hadded with ⟨Hadded, Hnd_tok⟩
  icases (join.ownTokAuth_halves γ.ndGn _).1 $$ Hadded with ⟨Hadded, Hadded_inv⟩
  imod ownTokAuth_S γ.depGn j $$ Hdep with ⟨Hdep, Hdep_tok⟩
  imod Hclose $$ [Hwgo Hadded_inv Hdone_toks Hdone_ap HPdone Hjt Hdep Hrc Hlent] with -
  · inext
    unfold tjInv
    iexists ctr + W32 (sint.Z (W64 1)), n + 1, done, j + 1, b, Pdone
    iframe
    ipureintro
    rw [h2, hz]
    refine ⟨by omega, by push_cast; omega, by push_cast; omega⟩
  imodintro
  iapply HΦ
  isplitl [Hwait Hap Hadded Himp]
  · iexists γ, iprop(P0 ∗ P')
    iframe Hwait Hap Hadded Hj
    iintro ⟨H1, H2⟩
    iframe H2
    iapply Himp $$ H1
  unfold ownDone
  iexists γ
  iframe Hdone_ap' Hnd_tok Hdep_tok Hj

/-- The thread-token join's `WaitGroup.Done()`, by a goroutine with its slot's token deposited:
`P` passed to the `Wait`, the slot's thread token back (the one the goroutine exits with). From
`WaitGroup.Done`'s spec (the result `sync.tokJoin.WaitGroup.wp_Done` is this applied to
`sync.WaitGroup.wp_Done`, in `Results`). -/
theorem WaitGroup.wp_Done_of
    (wp_Done : sync.WaitGroup.Done.spec (GF := GF) (hG := hG))
    (N : Namespace) (L : IProp GF) (wg : Loc) (P : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ ownDone N L wg P ∗ P }}
      (App (Val (wg @!! go.GoType.PointerType WaitGroup.ty @!! go!"Done")) (Val #()))
    {{ RET #(); threadTok }} := by
  wp_start_folded as ⟨Hd, HP⟩
  unfold ownDone
  icases Hd with ⟨%γ, Hap, Hnd_tok, Hdep_tok, #Hj⟩
  ihave #Hj2 := Hj
  iunfold isTokJoin at Hj2
  icases Hj2 with ⟨#Hwg, #Hinv, -⟩
  wp_apply_core wp_Done wg γ.wgGn (N.@"wg") $$ [] [-]
  · iframe #
  imod inv_acc (E := ⊤) (fun _ _ => CoPset.mem_full) $$ Hinv with ⟨Hi, Hclose⟩
  iapply fupd_mask_intro (wg_mask_ndot_ne N "wg" "inv" (by decide))
  iintro Hmask
  inext
  iunfold tjInv at Hi
  icases Hi with ⟨%ctr, %added, %done, %j, %b, %Pdone, Hwgo, Hadded_inv, Hdone_toks, Hdone_ap,
    HPdone, Hjt, Hdep, Hrc, Hlent, %Hctr⟩
  icombine Hdep Hdep_tok gives %Hj1
  icombine Hnd_tok Hdone_toks as Hdone_toks
  icombine Hadded_inv Hdone_toks gives %Hle
  icombine Hap Hdone_ap as Hdone_ap
  obtain ⟨Hc0, Hc1, Hc2⟩ := Hctr
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  icases (threadToks_add j' 1).1 $$ Hjt with ⟨Hjt, Htok⟩
  have hz : sint.Z (ctr - W32 1) = sint.Z ctr - 1 := by word
  iexists ctr
  iframe Hwgo
  isplitr
  · ipureintro; constructor <;> word
  iintro Hwgo
  imod Hmask with -
  imod ownTokAuth_delete_S γ.depGn j' $$ Hdep Hdep_tok with Hdep
  imod Hclose $$ [Hwgo Hadded_inv Hdone_toks Hdone_ap HP HPdone Hjt Hdep Hrc Hlent] with -
  · inext
    unfold tjInv
    iexists ctr - W32 1, added, 1 + done, j', b, iprop(P ∗ Pdone)
    iframe Hwgo Hadded_inv Hdone_ap Hjt Hdep Hrc Hlent
    rw [Nat.add_comm 1 done]
    iframe Hdone_toks
    isplitl [HP HPdone]
    · iframe
    ipureintro
    rw [hz]
    refine ⟨by omega, by push_cast; omega, by push_cast; omega⟩
  imodintro
  iapply HΦ
  iexact Htok

/-- The thread-token join's `WaitGroup.Wait()`: the propositions of every `Done` since the last
`Wait`. From `WaitGroup.Wait`'s spec (the result `sync.tokJoin.WaitGroup.wp_Wait` is this applied
to `sync.WaitGroup.wp_Wait`, in `Results`). -/
theorem WaitGroup.wp_Wait_of
    (wp_Wait : sync.WaitGroup.Wait.spec (GF := GF) (hG := hG))
    (N : Namespace) (L : IProp GF) (wg : Loc) (n : Nat) (P : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ ownAdder N L wg n P }}
      (App (Val (wg @!! go.GoType.PointerType WaitGroup.ty @!! go!"Wait")) (Val #()))
    {{ RET #(); ▷ P ∗ ownAdder N L wg 0 iprop(True) }} := by
  wp_start_folded as Ha
  iapply wp_fupd
  unfold ownAdder
  icases Ha with ⟨%γ, %P0, Hwait, Hap, Hadded, Himp, #Hj⟩
  ihave #Hj2 := Hj
  iunfold isTokJoin at Hj2
  icases Hj2 with ⟨#Hwg, #Hinv, -⟩
  iapply fupd_wp
  imod fupd_mask_subseteq (E1 := ⊤) (E2 := ↑(N.@"wg")) (fun _ _ => CoPset.mem_full) with Hmask
  imod alloc_wait_token wg γ.wgGn (N.@"wg") 0 (by decide) $$ Hwg Hwait with ⟨Hwaiter, Htok⟩
  imod Hmask with -
  imodintro
  wp_apply_core wp_Wait wg γ.wgGn (N.@"wg") $$ [Htok] [-]
  · iframe #; iframe
  imod inv_acc (E := ⊤ \ ↑(N.@"wg")) (wg_mask_ndot_ne N "inv" "wg" (by decide)) $$ Hinv
    with ⟨Hi, Hclose⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iunfold tjInv at Hi
  icases Hi with ⟨%ctr, %added, %done, %j, %b, %Pdone, Hwgo, Hadded_inv, Hdone_toks, Hdone_ap,
    HPdone, Hjt, Hdep, Hrc, Hlent, %Hctr⟩
  iexists ctr
  iframe Hwgo
  iintro %Hctr_zero Hwgo
  have hctr : ctr = W32 0 := by
    apply BitVec.eq_of_toInt_eq; simpa [sint.Z] using Hctr_zero
  subst hctr
  obtain ⟨-, Hc1, Hc2⟩ := Hctr
  have hdone : added = done := by simp only [show sint.Z (W32 0) = 0 from rfl] at Hc1; omega
  have hj : j = 0 := by omega
  have hb : b = 0 := by omega
  subst hdone hj hb
  icombine Hadded Hadded_inv gives %Hc
  obtain ⟨-, Heq⟩ := Hc
  rw [← Heq]
  icombine Hdone_ap Hap gives #HPeq
  imod ownApropAuth_reset γ.apGn P0 Pdone _ $$ Hap Hdone_ap with Hap
  ihave Hadded := (join.ownTokAuth_halves γ.ndGn _).2 $$ [Hadded Hadded_inv]
  · iframe
  imod ownTokAuth_sub _ γ.ndGn _ $$ Hadded Hdone_toks with Hadded
  rw [Nat.sub_self]
  icases (join.ownTokAuth_halves γ.ndGn 0).1 $$ Hadded with ⟨Hadded, Hadded_inv⟩
  imod Hmask with -
  ihave Hfrag := ownApropFrag_0 (GF := GF) γ.apGn
  imod ownToks_0 (GF := GF) γ.ndGn with Hdone_toks
  imod Hclose $$ [Hwgo Hadded_inv Hdone_toks Hfrag Hjt Hdep Hrc Hlent] with -
  · inext
    unfold tjInv
    iexists W32 0, 0, 0, 0, 0, iprop(True)
    iframe
    isplitr
    · itrivial
    ipureintro
    exact ⟨by decide, by decide, by simp⟩
  imodintro
  iintro Hwt
  imod fupd_mask_subseteq (E1 := ⊤) (E2 := ↑(N.@"wg")) (fun _ _ => CoPset.mem_full) with Hmask
  imod dealloc_wait_token wg γ.wgGn (N.@"wg") (0 + 1) (by decide) $$ Hwg Hwaiter Hwt with H
  imod Hmask with -
  imodintro
  iapply HΦ
  isplitl [HPdone Himp]
  · icases HPeq with ⟨HPa, HPb⟩
    ihave H : (▷ P0 : IProp GF) $$ [HPdone]
    · iapply HPa
      inext
      iexact HPdone
    inext
    iapply Himp $$ H
  iexists γ, iprop(True)
  rw [show (0 : Int) + 1 - 1 = 0 from rfl]
  iframe
  isplitr
  · iintro _; itrivial
  iexact Hj

end waitgroup_tok_join_idiom

end tokJoin

end sync

end Perennial
