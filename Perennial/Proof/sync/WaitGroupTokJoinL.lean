/-
The **leveled** thread-token join for `WaitGroup` (`sync.tokJoinL`): as `tokJoin`
(`WaitGroupTokJoin`), the counter bounded by thread tokens, except that the goroutines of the
group keep most of their thread token, so that they can themselves `Add` to such a group or
borrow from a thread pool (`threadPool.isThreadPoolL`).

Thread tokens come in levels (`levelTok l`, `GooseLang/Threads.lean`): a thread token is one
token of each of the `T = threadBound GF` levels, and each level has its own `T - 1` tokens.

* A group has a **pending level** `p`, chosen at `init`.
* `Add(1)` deposits the caller's level-`p` token as **pending**: the goroutine about to start
  (`ownPending`).
* At the `go` statement (`wp_fork`, or `start` with the fresh token of `wp_fork_tok_upd`), the
  fresh thread token's level-`0` token takes the pending token's place in the slot, and the
  pending token goes back to the caller, who has the level-`p` token it had before its `Add`.
  The goroutine runs with the rest of the fresh token, its levels from `1` (`threadTokFrom 1`),
  and the right to call `Done` (`ownDone`).
* `Done` gives the slot's level-`0` token back, so the goroutine exits with a whole thread token
  (`threadTok_level0`).

The counter is the `d` level-`0` tokens of the started goroutines plus the `q` pending level-`p`
tokens. Each level has fewer than `T` tokens, so `d < T` and `q < T`, and the counter stays below
`2 * T`: the premise is `2 * threadBound GF ≤ 2 ^ 31`. (With `p = 0` the two share level `0`, and
the counter stays below `T`.)

A goroutine of a group with pending level `p` holds levels `1` to `T - 1`: it can `Add` to a
group of pending level `1` (or any level it holds), and gets the token back at its `go`
statement; it can borrow from a pool at a level it holds. A thread that holds pending tokens of
two groups at once uses two levels.

The specs are proved from `WaitGroup`'s specs, taken as hypotheses (`WaitGroup.wp_Add_of`, ...),
as in `WaitGroupTokJoin`; `Results` applies them to the linked results
(`sync.tokJoinL.WaitGroup.wp_Add`, `wp_Done`, `wp_Wait`).
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

namespace tokJoinL

structure TokJoinLNames where
  wgGn : WaitGroupNames
  /-- The propositions of the `Done`s (`ownAprop`). -/
  apGn : GName
  /-- The goroutines added and not done. -/
  ndGn : GName
  /-- The started goroutines, whose slot holds their level-`0` token. -/
  depGn : GName
  /-- The goroutines added and not yet started, whose slot holds a pending level-`p` token. -/
  pendGn : GName

section waitgroup_tok_join_level_idiom
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

/-- The body of the internal invariant: the counter is the goroutines added and not done
(`added - done`), the `d` started ones with their level-`0` token (tickets `depGn`) and the `q`
pending ones with a level-`p` token (tickets `pendGn`); the propositions of the `Done`s so far. -/
def tjInv (γ : TokJoinLNames) (p : Nat) : IProp GF :=
  iprop(∃ (ctr : w32) (added done d q : Nat) (Pdone : IProp GF),
    ownWaitGroup γ.wgGn ctr ∗
    ownTokAuthDfrac γ.ndGn (DFrac.own (1 : Qp).half) added ∗ ownToks γ.ndGn done ∗
    ownApropFrag γ.apGn Pdone done ∗ Pdone ∗
    levelToks 0 d ∗ ownTokAuth γ.depGn d ∗ levelToks p q ∗ ownTokAuth γ.pendGn q ∗
    ⌜0 ≤ sint.Z ctr ∧ sint.Z ctr = (added : Int) - done ∧ (added : Int) - done = d + q⌝)

/-- The join's wait group and invariant (persistent), with pending level `p`. -/
def isTokJoin (N : Namespace) (p : Nat) (wg : Loc) (γ : TokJoinLNames) : IProp GF :=
  iprop(isWaitGroup wg γ.wgGn (N.@"wg") ∗ inv (N.@"inv") (tjInv (GF := GF) γ p) ∗
    ⌜2 * threadBound GF ≤ 2 ^ 31⌝)

instance isTokJoin_persistent (N : Namespace) (p : Nat) (wg : Loc) (γ : TokJoinLNames) :
    Persistent (isTokJoin (GF := GF) N p wg γ) := by
  unfold isTokJoin; infer_instance

/-- **Permission to call `Add` or `Wait`** (`n` added since the last `Wait`): `Add` extends `P`
with a caller-chosen proposition, `Wait` gives `P` and resets the permission. -/
def ownAdder (N : Namespace) (p : Nat) (wg : Loc) (n : Nat) (P : IProp GF) : IProp GF :=
  iprop(∃ (γ : TokJoinLNames) (P' : IProp GF),
    ownWaitGroupWaiters γ.wgGn 0 ∗ ownApropAuth γ.apGn P' n ∗
    ownTokAuthDfrac γ.ndGn (DFrac.own (1 : Qp).half) n ∗ (P' -∗ P) ∗ isTokJoin N p wg γ)

/-- **A goroutine added and not yet started**, its slot holding the adder's level-`p` token:
the `go` statement turns it into `ownDone` (`start`, `wp_fork`). -/
def ownPending (N : Namespace) (p : Nat) (wg : Loc) (P : IProp GF) : IProp GF :=
  iprop(∃ γ : TokJoinLNames,
    ownAprop γ.apGn P ∗ ownToks γ.ndGn 1 ∗ ownToks γ.pendGn 1 ∗ isTokJoin N p wg γ)

/-- **Permission to call `Done` with `P`**, the slot holding the goroutine's level-`0` token. -/
def ownDone (N : Namespace) (p : Nat) (wg : Loc) (P : IProp GF) : IProp GF :=
  iprop(∃ γ : TokJoinLNames,
    ownAprop γ.apGn P ∗ ownToks γ.ndGn 1 ∗ ownToks γ.depGn 1 ∗ isTokJoin N p wg γ)

theorem init (N : Namespace) (p : Nat) (wg : Loc) (γwg : WaitGroupNames) (E : CoPset)
    (Hb : 2 * threadBound GF ≤ 2 ^ 31) :
    isWaitGroup (GF := GF) wg γwg (N.@"wg") ∗ ownWaitGroup γwg (W32 0) ∗
      ownWaitGroupWaiters γwg 0 ⊢ |={E}=> ownAdder N p wg 0 iprop(True) := by
  iintro ⟨#His, Hctr, Hwait⟩
  imod ownApropAuth_alloc (GF := GF) with ⟨%γap, Hap⟩
  imod ownTokAuth_alloc (GF := GF) with ⟨%γnd, Hnd⟩
  icases (join.ownTokAuth_halves γnd 0).1 $$ Hnd with ⟨Hnd1, Hnd2⟩
  imod ownToks_0 (GF := GF) γnd with Hnd0
  ihave Hfrag := ownApropFrag_0 (GF := GF) γap
  imod ownTokAuth_alloc (GF := GF) with ⟨%γdep, Hdep⟩
  imod ownTokAuth_alloc (GF := GF) with ⟨%γpend, Hpend⟩
  let γ : TokJoinLNames := ⟨γwg, γap, γnd, γdep, γpend⟩
  imod inv_alloc (N.@"inv") E (tjInv (GF := GF) γ p) $$ [Hctr Hnd1 Hnd0 Hfrag Hdep Hpend]
    with #Hinv
  · inext
    unfold tjInv
    iexists W32 0, 0, 0, 0, 0, iprop(True)
    simp only [γ]
    iframe
    isplitr
    · iexact Hfrag
    isplitr
    · iapply levelToks_zero
    isplitr
    · iapply levelToks_zero
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

theorem ownAdder_wand (P' : IProp GF) (N : Namespace) (p : Nat) (wg : Loc) (n : Nat)
    (P : IProp GF) :
    ⊢ (P -∗ P') -∗ ownAdder N p wg n P -∗ ownAdder N p wg n P' := by
  iintro Hw Ha
  unfold ownAdder
  icases Ha with ⟨%γ, %P0, Hwait, Hap, Hadded, Himp, #Hj⟩
  iexists γ, P0
  iframe Hwait Hap Hadded Hj
  iintro H
  iapply Hw
  iapply Himp $$ H

/-- **Starting a pending goroutine**: a level-`0` token (the fresh token's, at the `go`
statement) takes the place of the pending level-`p` token, which comes back. -/
theorem start (N : Namespace) (p : Nat) (wg : Loc) (P : IProp GF) (E : CoPset)
    (HE : ↑(N.@"inv") ⊆ E) :
    ownPending N p wg P ∗ levelTok 0 ⊢ |={E}=> ownDone N p wg P ∗ levelTok p := by
  iintro ⟨Hpd, Htok0⟩
  unfold ownPending
  icases Hpd with ⟨%γ, Hap, Hnd, Hpend_tok, #Hj⟩
  ihave #Hj2 := Hj
  iunfold isTokJoin at Hj2
  icases Hj2 with ⟨-, #Hinv, -⟩
  imod inv_acc (E := E) HE $$ Hinv with ⟨Hi, Hclose⟩
  iunfold tjInv at Hi
  icases Hi with ⟨%ctr, %added, %done, %d, %q, %Pdone, Hwgo, Hadded, Hdone_toks, Hdone_ap,
    HPdone, >Hd0, >Hdep, >Hqp, >Hpend, >%Hctr⟩
  icombine Hpend Hpend_tok gives %Hq1
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  icases (levelToks_add p q' 1).1 $$ Hqp with ⟨Hqp, Htokp⟩
  imod ownTokAuth_delete_S γ.pendGn q' $$ Hpend Hpend_tok with Hpend
  imod ownTokAuth_S γ.depGn d $$ Hdep with ⟨Hdep, Hdep_tok⟩
  ihave Hd0 := (levelToks_add 0 d 1).2 $$ [Hd0 Htok0]
  · iframe
  imod Hclose $$ [Hwgo Hadded Hdone_toks Hdone_ap HPdone Hd0 Hdep Hqp Hpend] with -
  · inext
    unfold tjInv
    iexists ctr, added, done, d + 1, q', Pdone
    iframe
    ipureintro
    obtain ⟨h0, h1, h2⟩ := Hctr
    refine ⟨h0, h1, by push_cast at h2 ⊢; omega⟩
  imodintro
  iframe Htokp
  unfold ownDone
  iexists γ
  iframe Hap Hnd Hdep_tok Hj

/-- `start` with a whole thread token (the fresh one, at the `go` statement): the slot gets its
level `0`, the goroutine its levels from `1`, and the pending token comes back. -/
theorem start_threadTok (N : Namespace) (p : Nat) (wg : Loc) (P : IProp GF) (E : CoPset)
    (HE : ↑(N.@"inv") ⊆ E) :
    ownPending N p wg P ∗ threadTok ⊢
      |={E}=> (ownDone N p wg P ∗ threadTokFrom 1) ∗ levelTok p := by
  iintro ⟨Hpd, Htok⟩
  icases threadTok_level0.1 $$ Htok with ⟨Htok0, Hrest⟩
  imod start N p wg P E HE $$ [Hpd Htok0] with ⟨Hd, Htokp⟩
  · iframe
  imodintro
  iframe

/-- **The `go` statement of a pending goroutine**: the fresh thread token's level `0` goes into
the goroutine's slot, the pending level-`p` token back to the forking thread, and the goroutine
runs with the right to call `Done` and the fresh token's levels from `1`; it exits with a whole
thread token (its slot's level-`0` token, from `Done`, and its levels from `1`). -/
theorem wp_fork (N : Namespace) (p : Nat) (wg : Loc) (P : IProp GF) (s : Stuckness)
    (E : CoPset) (HE : ↑(N.@"inv") ⊆ E) (e : Expr) (Φ : val → IProp GF) :
    ⊢ ownPending N p wg P -∗
      ▷ (ownDone N p wg P -∗ threadTokFrom 1 -∗
          WP e @ s; ⊤ {{ v, ⌜v.isPanic = false⌝ ∗ threadTok }}) -∗
      ▷ (levelTok p -∗ Φ #()) -∗
      WP (Fork e) @ s; E {{ Φ }} := by
  iintro Hpd He HΦ
  iapply wp_fork_tok_upd
  inext
  iintro Htok _
  imod start_threadTok N p wg P E HE $$ [Hpd Htok] with ⟨⟨Hd, Hrest⟩, Htokp⟩
  · iframe
  imodintro
  isplitl [He Hd Hrest]
  · iapply He $$ Hd Hrest
  · iapply HΦ $$ Htokp

/-- The leveled join's `WaitGroup.Add(1)`, by the caller with a level-`p` token, which the new
slot holds as pending until the `go` statement (`wp_fork`, `start`). From `WaitGroup.Add`'s spec
(the result `sync.tokJoinL.WaitGroup.wp_Add` is this applied to `sync.WaitGroup.wp_Add`, in
`Results`). -/
theorem WaitGroup.wp_Add_of
    (wp_Add : sync.WaitGroup.Add.spec (GF := GF) (hG := hG))
    (P' : IProp GF) (N : Namespace) (p : Nat) (wg : Loc) (n : Nat) (P : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ ownAdder N p wg n P ∗ levelTok p }}
      (App (Val (wg @!! go.GoType.PointerType WaitGroup.ty @!! go!"Add")) (Val #(W64 1)))
    {{ RET #(); ownAdder N p wg (n + 1) iprop(P ∗ P') ∗ ownPending N p wg P' }} := by
  wp_start_folded as ⟨Had, Htok⟩
  unfold ownAdder
  icases Had with ⟨%γ, %P0, Hwait, Hap, Hadded, Himp, #Hj⟩
  ihave #Hj2 := Hj
  iunfold isTokJoin at Hj2
  icases Hj2 with ⟨#Hwg, #Hinv, %Hb⟩
  wp_apply_core wp_Add wg (W64 1) γ.wgGn (N.@"wg") $$ [] [-]
  · iframe #
  imod inv_acc (E := ⊤) (fun _ _ => CoPset.mem_full) $$ Hinv with ⟨Hi, Hclose⟩
  iunfold tjInv at Hi
  icases Hi with ⟨%ctr, %added, %done, %d, %q, %Pdone, Hwgo, >Hadded_inv, Hdone_toks, Hdone_ap,
    HPdone, >Hd0, >Hdep, >Hqp, >Hpend, >%Hctr⟩
  icases levelToks_add_one_lt p q $$ [Htok Hqp] with ⟨%Hqlt, Hqp⟩
  · iframe
  icases persistent_entails_left (levelToks_lt 0 d) $$ Hd0 with ⟨Hd0, %Hdlt⟩
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
  imod ownTokAuth_S γ.pendGn q $$ Hpend with ⟨Hpend, Hpend_tok⟩
  imod Hclose $$ [Hwgo Hadded_inv Hdone_toks Hdone_ap HPdone Hd0 Hdep Hqp Hpend] with -
  · inext
    unfold tjInv
    iexists ctr + W32 (sint.Z (W64 1)), n + 1, done, d, q + 1, Pdone
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
  unfold ownPending
  iexists γ
  iframe Hdone_ap' Hnd_tok Hpend_tok Hj

/-- The leveled join's `WaitGroup.Done()`, by a started goroutine: `P` passed to the `Wait`, the
slot's level-`0` token back (with the goroutine's levels from `1`, a whole thread token,
`threadTok_level0`). From `WaitGroup.Done`'s spec (the result `sync.tokJoinL.WaitGroup.wp_Done`
is this applied to `sync.WaitGroup.wp_Done`, in `Results`). -/
theorem WaitGroup.wp_Done_of
    (wp_Done : sync.WaitGroup.Done.spec (GF := GF) (hG := hG))
    (N : Namespace) (p : Nat) (wg : Loc) (P : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ ownDone N p wg P ∗ P }}
      (App (Val (wg @!! go.GoType.PointerType WaitGroup.ty @!! go!"Done")) (Val #()))
    {{ RET #(); levelTok 0 }} := by
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
  icases Hi with ⟨%ctr, %added, %done, %d, %q, %Pdone, Hwgo, Hadded_inv, Hdone_toks, Hdone_ap,
    HPdone, Hd0, Hdep, Hqp, Hpend, %Hctr⟩
  icombine Hdep Hdep_tok gives %Hd1
  icombine Hnd_tok Hdone_toks as Hdone_toks
  icombine Hadded_inv Hdone_toks gives %Hle
  icombine Hap Hdone_ap as Hdone_ap
  obtain ⟨Hc0, Hc1, Hc2⟩ := Hctr
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  icases (levelToks_add 0 d' 1).1 $$ Hd0 with ⟨Hd0, Htok⟩
  have hz : sint.Z (ctr - W32 1) = sint.Z ctr - 1 := by word
  iexists ctr
  iframe Hwgo
  isplitr
  · ipureintro; constructor <;> word
  iintro Hwgo
  imod Hmask with -
  imod ownTokAuth_delete_S γ.depGn d' $$ Hdep Hdep_tok with Hdep
  imod Hclose $$ [Hwgo Hadded_inv Hdone_toks Hdone_ap HP HPdone Hd0 Hdep Hqp Hpend] with -
  · inext
    unfold tjInv
    iexists ctr - W32 1, added, 1 + done, d', q, iprop(P ∗ Pdone)
    iframe Hwgo Hadded_inv Hdone_ap Hd0 Hdep Hqp Hpend
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

/-- The leveled join's `WaitGroup.Wait()`: the propositions of every `Done` since the last
`Wait`. From `WaitGroup.Wait`'s spec (the result `sync.tokJoinL.WaitGroup.wp_Wait` is this
applied to `sync.WaitGroup.wp_Wait`, in `Results`). -/
theorem WaitGroup.wp_Wait_of
    (wp_Wait : sync.WaitGroup.Wait.spec (GF := GF) (hG := hG))
    (N : Namespace) (p : Nat) (wg : Loc) (n : Nat) (P : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ ownAdder N p wg n P }}
      (App (Val (wg @!! go.GoType.PointerType WaitGroup.ty @!! go!"Wait")) (Val #()))
    {{ RET #(); ▷ P ∗ ownAdder N p wg 0 iprop(True) }} := by
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
  icases Hi with ⟨%ctr, %added, %done, %d, %q, %Pdone, Hwgo, Hadded_inv, Hdone_toks, Hdone_ap,
    HPdone, Hd0, Hdep, Hqp, Hpend, %Hctr⟩
  iexists ctr
  iframe Hwgo
  iintro %Hctr_zero Hwgo
  have hctr : ctr = W32 0 := by
    apply BitVec.eq_of_toInt_eq; simpa [sint.Z] using Hctr_zero
  subst hctr
  obtain ⟨-, Hc1, Hc2⟩ := Hctr
  have hdone : added = done := by simp only [show sint.Z (W32 0) = 0 from rfl] at Hc1; omega
  have hd : d = 0 := by omega
  have hq : q = 0 := by omega
  subst hdone hd hq
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
  imod Hclose $$ [Hwgo Hadded_inv Hdone_toks Hfrag Hd0 Hdep Hqp Hpend] with -
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

end waitgroup_tok_join_level_idiom

end tokJoinL

end sync

end Perennial
