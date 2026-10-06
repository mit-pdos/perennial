/-
Port of `new/golang/theory/chan/idioms/mpmc.v`: multiple-producer multiple-consumer (MPMC)
channels. Each producer/consumer tracks its OWN history using multisets:

* producer `i` has sent `sent_i`, consumer `j` has received `recv_j`;
* invariant: `⊎ sent_i = ⊎ recv_j ⊎ inflight`.

Uses the contribution theory (`Contrib.lean`) on multisets.

Lean notes / deviations:
* Multisets. Rocq uses `gmultiset V` (camera `gmultisetR V`). The `allG` camera codes
  (`Perennial/Ghost/All.lean`) cannot mention `V` and have no multiset code, so a multiset
  of `V` is `mset := gmap Pos positive` (untyped: a parameter `V` would break
  type class search for the `gmap` camera) (each `encode v` mapped to its positive
  multiplicity; canonical, so `=` is multiset equality), with union `•` and empty
  `UCMRA.unit`; `{[+ v +]}` is `msetSingleton v`, `list_to_set_disj` is `listToMset`, and
  `foldr (⊎) ∅` is `msetSum`. The contribution camera is used at
  `A := Auth (gmap Pos positive)` (code `authR (gmapUR pos positiveR)`), and only
  fragments `◯ m` are stored (`msetFrag`).
* `bulk_dealloc_all` / `auth_map_agree` are replaced by `clients_agree` (the server's total
  equals the sum of all `n` clients) and `clients_extra_false` (an `n+1`-st client
  contradicts a server with `n` clients), proved directly on the camera; Rocq's
  `delete_client*`/`bulk_*` lemmas (which use multiset difference) are not needed.
-/
import Perennial.Golang.Theory.Chan.Idioms.Base
import Perennial.Golang.Theory.Chan.Idioms.Contrib
import Perennial.Golang.Theory.Chan

set_option linter.iris.style.nameCheck false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE CMRA

/-! ## Multisets -/

/-- Multisets of `V` (see the file header). -/
abbrev MSet : Type := GMap Pos positive

section mset
variable {V : Type} [Pos.Countable V]

def msetSingleton (v : V) : MSet := {[Pos.Countable.encode v := positive.one]}

def listToMset (l : List V) : MSet := l.foldr (fun v acc => msetSingleton v • acc) UCMRA.unit

/-- `foldr (⊎) ∅`. -/
def msetSum (ys : List (MSet)) : MSet := ys.foldr (· • ·) UCMRA.unit

instance mset_assoc : Std.Associative (α := MSet) (· • ·) := ⟨fun _ _ _ => CMRA.assoc.symm⟩
instance mset_comm : Std.Commutative (α := MSet) (· • ·) := ⟨fun _ _ => CMRA.comm⟩

@[simp] theorem mset_unit_r (a : MSet) : a • UCMRA.unit = a := CMRA.unit_right_id
@[simp] theorem mset_unit_l (a : MSet) : UCMRA.unit • a = a := UCMRA.unit_left_id

omit [Pos.Countable V] in
@[simp] theorem msetSum_nil : msetSum ([] : List MSet) = UCMRA.unit := rfl
omit [Pos.Countable V] in
@[simp] theorem msetSum_cons (y : MSet) (ys : List MSet) : msetSum (y :: ys) = y • msetSum ys :=
  rfl

@[simp] theorem listToMset_nil : listToMset ([] : List V) = UCMRA.unit := rfl
@[simp] theorem listToMset_cons (v : V) (l : List V) :
    listToMset (v :: l) = msetSingleton v • listToMset l := rfl
@[simp] theorem listToMset_app (l1 l2 : List V) :
    listToMset (l1 ++ l2) = listToMset l1 • listToMset l2 := by
  induction l1 with
  | nil => simp
  | cons v l ih => simp only [List.cons_append, listToMset_cons, ih]; ac_rfl

theorem mset_valid (m : MSet) : ✓ m := fun k => by
  cases h : (Iris.Std.PartialMap.get? m k : Option positive) with
  | none => exact trivial
  | some x => exact trivial

/-- The contribution camera element of a multiset. -/
abbrev msetFrag (m : MSet) : Auth (GMap Pos positive) := Auth.frag m

theorem msetFrag_op (a b : MSet) : msetFrag (a • b) = msetFrag a • msetFrag b :=
  Auth.frag_op

theorem msetFrag_unit : msetFrag (UCMRA.unit : MSet) = UCMRA.unit := rfl

theorem msetFrag_inj {a b : MSet} (h : msetFrag a = msetFrag b) : a = b := Auth.frag_inj h

theorem msetFrag_valid (m : MSet) : ✓ msetFrag m := Auth.frag_valid.mpr (mset_valid m)

/-- `(X, Y) ~l~> (X ⊎ Z, Y ⊎ Z)` (Rocq `gmultiset_disj_union_local_update`). -/
theorem mset_local_update (X Y Z : MSet) :
    (msetFrag X, msetFrag Y) ~l~> (msetFrag (X • Z), msetFrag (Y • Z)) := by
  have h := LocalUpdate.op_discrete (msetFrag X) (msetFrag Y) (msetFrag Z)
    (fun _ => by rw [← msetFrag_op]; exact msetFrag_valid _)
  rwa [← msetFrag_op, ← msetFrag_op, CMRA.comm (x := Z), CMRA.comm (x := Z)] at h

end mset

/-! ## Contribution lemmas for all clients at once -/

section contrib_all
variable {GF : BundledGFunctors} [AllG GF]

theorem positive_of_nat_succ (n : Nat) (hn : n ≠ 0) :
    positive.ofNat (n + 1) = positive.one + positive.ofNat n := by
  ext; simp [positive.ofNat, positive.one]; omega

/-- All the clients `ys` together. -/
theorem clients_own (γ : GName) (ys : List MSet) (hne : ys ≠ []) :
    ([∗list] y ∈ ys, client (GF := GF) γ (msetFrag y)) ⊢
      own γ (Auth.frag (contribCl (positive.ofNat ys.length) (msetFrag (msetSum ys)))) := by
  induction ys with
  | nil => exact absurd rfl hne
  | cons y ys ih =>
    cases ys with
    | nil =>
      refine BigSepL.bigSepL_singleton.1.trans ?_
      unfold client
      simp only [msetSum, List.foldr, List.length_cons, List.length_nil, CMRA.unit_right_id]
      exact .rfl
    | cons y' ys' =>
      refine BigSepL.bigSepL_cons.1.trans ((sep_mono_right (ih (List.cons_ne_nil _ _))).trans ?_)
      unfold client
      refine (own_op γ _ _).2.trans (BiEntails.of_eq ?_).1
      have hp : positive.one + positive.ofNat (y' :: ys').length =
          positive.ofNat (y :: y' :: ys').length := by
        ext; simp [positive.ofNat, positive.one]
      rw [← Auth.frag_op, contribCl_op, hp, ← msetFrag_op]
      rfl

/-- The server's total is the sum of all `n` clients (replaces Rocq `auth_map_agree`). -/
theorem clients_agree (γ : GName) (X : MSet) (ys : List MSet) :
    server (GF := GF) γ ys.length (msetFrag X) ∗ ([∗list] y ∈ ys, client γ (msetFrag y)) ⊢
      ⌜X = msetSum ys⌝ := by
  cases ys with
  | nil =>
    iintro ⟨Hs, -⟩
    ihave H := server_0_empty γ _ $$ Hs
    icases discrete_eq_mp $$ H with %H
    ipureintro
    exact msetFrag_inj H
  | cons y ys =>
    iintro ⟨Hs, Hc⟩
    ihave Hc := clients_own γ (y :: ys) (by simp) $$ Hc
    unfold server
    simp only [List.length_cons, Nat.add_one_ne_zero, ↓reduceIte]
    icases (own_valid_pure_2 γ _ _) $$ Hs Hc with %Hv
    ipureintro
    obtain ⟨hinc, _⟩ := Auth.auth_both_valid_discrete.mp Hv
    rcases contribCl_inc _ _ _ _ hinc with ⟨_, h⟩ | ⟨r, hr, _⟩
    · exact msetFrag_inj h
    · exact absurd hr.symm (positive_add_ne_self _ _)

/-- An extra client contradicts a server with `n` clients (replaces the uses of Rocq
`bulk_dealloc_all` for contradictions). -/
theorem clients_extra_false (γ : GName) (X : MSet) (ys : List MSet) (y : MSet) :
    server (GF := GF) γ ys.length (msetFrag X) ∗ ([∗list] z ∈ ys, client γ (msetFrag z)) ∗
      client γ (msetFrag y) ⊢ False := by
  cases ys with
  | nil =>
    iintro ⟨Hs, -, Hc⟩
    icases server_agree γ _ _ _ $$ Hs Hc with %H
    exact absurd rfl H.1
  | cons z ys =>
    iintro ⟨Hs, Hcs, Hc⟩
    ihave Hcs := clients_own γ (z :: ys) (by simp) $$ Hcs
    unfold server client
    simp only [List.length_cons, Nat.add_one_ne_zero, ↓reduceIte]
    ihave Hc2 := (own_op γ _ _).2 $$ [Hc Hcs]
    · isplitl [Hc]
      · iexact Hc
      · iexact Hcs
    icases (own_valid_pure_2 γ _ _) $$ Hs Hc2 with %Hv
    ipureintro
    obtain ⟨hinc, _⟩ := Auth.auth_both_valid_discrete.mp Hv
    change contribCl positive.one (msetFrag y) • contribCl _ _ ≼ _ at hinc
    rw [contribCl_op] at hinc
    rcases contribCl_inc _ _ _ _ hinc with ⟨h, _⟩ | ⟨r, hr, _⟩
    · have := congrArg positive.pred h; simp [positive.ofNat, positive.one] at this
    · have := congrArg positive.pred hr; simp [positive.ofNat, positive.one] at this; omega

end contrib_all

/-! ## MPMC channels -/

structure MpmcNames where
  mpmcChanName : ChanNames
  mpmcSentName : GName
  mpmcRecvName : GName
  mpmcClosedName : GName

section mpmc
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable {V : Type} [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V] {t : go.GoType}
  [IntoValTyped (GF := GF) V t]

def isClosed (γ : MpmcNames) : IProp GF :=
  dghostVar γ.mpmcClosedName DFrac.discard true

instance isClosed_persistent (γ : MpmcNames) : Persistent (isClosed (GF := GF) γ) := by
  unfold isClosed; infer_instance

def mpmcProducer (γ : MpmcNames) (sent : MSet) : IProp GF :=
  client γ.mpmcSentName (msetFrag sent)

def mpmcConsumer (γ : MpmcNames) (received : MSet) : IProp GF :=
  client γ.mpmcRecvName (msetFrag received)

omit [ZeroVal V] [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V t] in
variable (V) in
def inflightMset (s : ChanState V) : MSet :=
  match s with
  | .Buffered buff => listToMset buff
  | .SndPending v | .SndCommit v => msetSingleton v
  | .Closed drain => listToMset drain
  | _ => UCMRA.unit

/-- The `"Hclosed"` part of the MPMC invariant. -/
def mpmcClosedPart (γ : MpmcNames) (s : ChanState V) : IProp GF :=
  match s with
  | .Closed [] => dghostVar γ.mpmcClosedName DFrac.discard true
  | _ => dghostVar γ.mpmcClosedName (DFrac.own 1) false

/-- The state-dependent resources of the MPMC invariant. -/
def mpmcInvMatch (γ : MpmcNames) (n_prod n_cons : Nat) (P : V → IProp GF)
    (R : MSet → IProp GF) (sent recv : MSet) (s : ChanState V) : IProp GF :=
  match s with
  | .Buffered buff => iprop([∗list] v ∈ buff, P v)
  | .SndPending v => P v
  | .SndCommit v => P v
  | .Closed [] =>
      iprop(⌜sent = recv⌝ ∗
        (∃ prods : List MSet, ⌜prods.length = n_prod⌝ ∗ [∗list] s_i ∈ prods, mpmcProducer γ s_i) ∗
        (R sent ∨ ∃ conss : List MSet, ⌜conss.length = n_cons⌝ ∗
          [∗list] r_i ∈ conss, mpmcConsumer γ r_i))
  | .Closed drain =>
      iprop(([∗list] v ∈ drain, P v) ∗
        (∃ prods : List MSet, ⌜prods.length = n_prod⌝ ∗ [∗list] s_i ∈ prods, mpmcProducer γ s_i) ∗
        R sent)
  | _ => iprop(True)

@[irreducible] def mpmcInv (γ : MpmcNames) (n_prod n_cons : Nat) (P : V → IProp GF)
    (R : MSet → IProp GF) : IProp GF :=
  iprop(∃ (s : ChanState V) (sent recv : MSet),
    ownChan γ.mpmcChanName V s ∗
    server γ.mpmcSentName n_prod (msetFrag sent) ∗
    server γ.mpmcRecvName n_cons (msetFrag recv) ∗
    ⌜sent = recv • inflightMset V s ∧ n_cons > 0 ∧ n_prod > 0⌝ ∗
    mpmcClosedPart γ s ∗
    mpmcInvMatch γ n_prod n_cons P R sent recv s)

def isMpmc (γ : MpmcNames) (ch : Loc) (n_prod n_cons : Nat) (P : V → IProp GF)
    (R : MSet → IProp GF) : IProp GF :=
  iprop(isChan ch γ.mpmcChanName V ∗ inv nroot (mpmcInv γ n_prod n_cons P R))

instance isMpmc_persistent (γ : MpmcNames) (ch : Loc) (n_prod n_cons : Nat)
    (P : V → IProp GF) (R : MSet → IProp GF) :
    Persistent (isMpmc γ ch n_prod n_cons P R) := by
  unfold isMpmc; infer_instance

omit [IntoValTyped (GF := GF) V t] in
theorem mpmcInv_elim (γ : MpmcNames) (n_prod n_cons : Nat) (P : V → IProp GF)
    (R : MSet → IProp GF) :
    mpmcInv γ n_prod n_cons P R ⊢ ∃ (s : ChanState V) (sent recv : MSet),
      ownChan γ.mpmcChanName V s ∗
      server γ.mpmcSentName n_prod (msetFrag sent) ∗
      server γ.mpmcRecvName n_cons (msetFrag recv) ∗
      ⌜sent = recv • inflightMset V s ∧ n_cons > 0 ∧ n_prod > 0⌝ ∗
      mpmcClosedPart γ s ∗
      mpmcInvMatch γ n_prod n_cons P R sent recv s := by
  unfold mpmcInv; exact .rfl

omit [IntoValTyped (GF := GF) V t] in
theorem mpmcInv_intro (γ : MpmcNames) (n_prod n_cons : Nat) (P : V → IProp GF)
    (R : MSet → IProp GF) (s : ChanState V) (sent recv : MSet)
    (h : sent = recv • inflightMset V s ∧ n_cons > 0 ∧ n_prod > 0) :
    ⊢ ownChan γ.mpmcChanName V s -∗
      server γ.mpmcSentName n_prod (msetFrag sent) -∗
      server γ.mpmcRecvName n_cons (msetFrag recv) -∗
      mpmcClosedPart γ s -∗
      mpmcInvMatch γ n_prod n_cons P R sent recv s -∗
      mpmcInv γ n_prod n_cons P R := by
  iintro H1 H2 H3 H4 H5
  unfold mpmcInv
  iexists s, sent, recv
  isplitl [H1]; · iexact H1
  isplitl [H2]; · iexact H2
  isplitl [H3]; · iexact H3
  isplitr
  · ipureintro; exact h
  isplitl [H4]; · iexact H4
  · iexact H5

omit [IntoValTyped (GF := GF) V t] in
theorem start_mpmc (ch : Loc) (P : V → IProp GF) (R : MSet → IProp GF) (γ : ChanNames)
    (n_prod n_cons : Nat) (s : ChanState V)
    (Hs : match s with | .Buffered [] => True | .Idle => True | _ => False)
    (Hprod : n_prod > 0) (Hcons : n_cons > 0) :
    ⊢ isChan ch γ V -∗ ownChan γ V s ={⊤}=∗
      ∃ γmpmc, isMpmc γmpmc ch n_prod n_cons P R ∗
        ([∗list] _k ↦ Q ∈ List.replicate n_prod (mpmcProducer γmpmc UCMRA.unit), Q) ∗
        ([∗list] _k ↦ Q ∈ List.replicate n_cons (mpmcConsumer γmpmc UCMRA.unit), Q) := by
  have hs : s = .Buffered [] ∨ s = .Idle := by
    rcases s with (_ | ⟨_, _⟩) | _ | _ | _ | _ | _ | _ <;> simp_all
  iintro #Hch Hoc
  imod dghostVar_alloc false with ⟨%γclosed, Hclosed⟩
  imod contribution_init_pow (A := Auth (GMap Pos positive)) n_prod with ⟨%γsent, HsentAuth, HsentFrags⟩
  imod contribution_init_pow (A := Auth (GMap Pos positive)) n_cons with ⟨%γrecv, HrecvAuth, HrecvFrags⟩
  iexists ⟨γ, γsent, γrecv, γclosed⟩
  imod inv_alloc nroot ⊤ (mpmcInv ⟨γ, γsent, γrecv, γclosed⟩ n_prod n_cons P R)
    $$ [Hoc HsentAuth HrecvAuth Hclosed] with #Hinv
  · inext
    rcases hs with rfl | rfl
    all_goals
      iapply mpmcInv_intro ⟨γ, γsent, γrecv, γclosed⟩ n_prod n_cons P R _ UCMRA.unit UCMRA.unit
        ⟨by simp [inflightMset], Hcons, Hprod⟩ $$ Hoc HsentAuth HrecvAuth [Hclosed] []
      · simp only [mpmcClosedPart]; iexact Hclosed
      · simp only [mpmcInvMatch]
        first | itrivial | (iapply BigSepL.bigSepL_nil.2; iempintro)
  imodintro
  unfold isMpmc mpmcProducer mpmcConsumer
  iframe
  iframe #

omit [IntoValTyped (GF := GF) V t] in
/-- No extra producer once the channel is closed. -/
theorem mpmc_closed_no_producer (γ : MpmcNames) (n_prod n_cons : Nat) (P : V → IProp GF)
    (R : MSet → IProp GF) (sent recv : MSet) (d : List V) (y : MSet) :
    server γ.mpmcSentName n_prod (msetFrag sent) ∗
      mpmcInvMatch γ n_prod n_cons P R sent recv (.Closed d) ∗ mpmcProducer γ y ⊢ False := by
  iintro ⟨HsentI, Hm, Hprod⟩
  cases d with
  | nil =>
    simp only [mpmcInvMatch, mpmcProducer]
    icases Hm with ⟨-, ⟨%prods, %Hlen, Hprods⟩, -⟩
    subst Hlen
    iapply clients_extra_false _ _ prods y $$ [$HsentI $Hprods $Hprod]
  | cons _ _ =>
    simp only [mpmcInvMatch, mpmcProducer]
    icases Hm with ⟨-, ⟨%prods, %Hlen, Hprods⟩, -⟩
    subst Hlen
    iapply clients_extra_false _ _ prods y $$ [$HsentI $Hprods $Hprod]

omit [IntoValTyped (GF := GF) V t] in
set_option maxHeartbeats 400000 in
theorem mpmc_send_au (γ : MpmcNames) (ch : Loc) (n_prod n_cons : Nat) (P : V → IProp GF)
    (R : MSet → IProp GF) (sent : MSet) (v : V) (Φ : IProp GF) :
    ⊢ isMpmc γ ch n_prod n_cons P R -∗ £ 1 ∗ £ 1 -∗ mpmcProducer γ sent ∗ P v -∗
      ▷ (mpmcProducer γ (sent • msetSingleton v) -∗ Φ) -∗ sendAu γ.mpmcChanName v Φ := by
  unfold isMpmc sendAu
  iintro ⟨#Hchan, #Hinv⟩ ⟨Hlc1, Hlc2⟩ ⟨Hprod, HP⟩ Hcont
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc1 Hi with Hi
  icases mpmcInv_elim _ _ _ _ _ $$ Hi with ⟨%s, %sent0, %recv, Hch, HsentI, HrecvI, %Hpure, Hclosed, Hm⟩
  obtain ⟨Hrel, Hncons, Hnprod⟩ := Hpure
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists s
  iframe Hch
  cases s with
  | Buffered buff =>
    dsimp only
    iintro Hoc
    unfold mpmcProducer
    imod update_client _ _ _ _ _ _ (mset_local_update sent0 sent (msetSingleton v)) $$ HsentI Hprod
      with ⟨HsentI, Hprod⟩
    imod Hmask with -
    imod Hclose $$ [Hoc HsentI HrecvI Hclosed Hm HP] with -
    · inext
      iapply mpmcInv_intro γ n_prod n_cons P R (.Buffered (buff ++ [v])) (sent0 • msetSingleton v)
        recv ⟨by subst Hrel; simp [inflightMset]; ac_rfl, Hncons, Hnprod⟩
        $$ Hoc HsentI HrecvI [Hclosed] [Hm HP]
      · simp only [mpmcClosedPart]; iexact Hclosed
      · simp only [mpmcInvMatch]
        iapply BigSepL.bigSepL_snoc.2
        isplitl [Hm]
        · iexact Hm
        · iexact HP
    imodintro
    iapply Hcont
    iexact Hprod
  | Idle =>
    dsimp only
    iintro Hoc
    unfold mpmcProducer
    imod update_client _ _ _ _ _ _ (mset_local_update sent0 sent (msetSingleton v)) $$ HsentI Hprod
      with ⟨HsentI, Hprod⟩
    imod Hmask with -
    imod Hclose $$ [Hoc HsentI HrecvI Hclosed HP] with -
    · inext
      iapply mpmcInv_intro γ n_prod n_cons P R (.SndPending v) (sent0 • msetSingleton v)
        recv ⟨by subst Hrel; simp [inflightMset], Hncons, Hnprod⟩
        $$ Hoc HsentI HrecvI [Hclosed] [HP]
      · simp only [mpmcClosedPart]; iexact Hclosed
      · simp only [mpmcInvMatch]; iexact HP
    imodintro
    unfold sendNestedAu
    iinv Hinv with Hi Hclose
    imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc2 Hi with Hi
    icases mpmcInv_elim _ _ _ _ _ $$ Hi with
      ⟨%s, %sent1, %recv1, Hch, HsentI, HrecvI, %Hpure, Hclosed, Hm⟩
    obtain ⟨Hrel, Hncons, Hnprod⟩ := Hpure
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iexists s
    iframe Hch
    cases s with
    | RcvCommit =>
      dsimp only
      iintro Hoc
      imod Hmask with -
      imod Hclose $$ [Hoc HsentI HrecvI Hclosed] with -
      · inext
        iapply mpmcInv_intro γ n_prod n_cons P R .Idle sent1 recv1
          ⟨by simpa [inflightMset] using Hrel, Hncons, Hnprod⟩ $$ Hoc HsentI HrecvI [Hclosed] []
        · simp only [mpmcClosedPart]; iexact Hclosed
        · simp only [mpmcInvMatch]; itrivial
      imodintro
      iapply Hcont
      iexact Hprod
    | Closed d =>
      dsimp only
      iapply mpmc_closed_no_producer γ n_prod n_cons P R sent1 recv1 d _ $$ [$HsentI $Hm Hprod]
      unfold mpmcProducer
      iexact Hprod
    | _ => itrivial
  | RcvPending =>
    dsimp only
    iintro Hoc
    unfold mpmcProducer
    imod update_client _ _ _ _ _ _ (mset_local_update sent0 sent (msetSingleton v)) $$ HsentI Hprod
      with ⟨HsentI, Hprod⟩
    imod Hmask with -
    imod Hclose $$ [Hoc HsentI HrecvI Hclosed HP] with -
    · inext
      iapply mpmcInv_intro γ n_prod n_cons P R (.SndCommit v) (sent0 • msetSingleton v)
        recv ⟨by subst Hrel; simp [inflightMset], Hncons, Hnprod⟩
        $$ Hoc HsentI HrecvI [Hclosed] [HP]
      · simp only [mpmcClosedPart]; iexact Hclosed
      · simp only [mpmcInvMatch]; iexact HP
    imodintro
    iapply Hcont
    iexact Hprod
  | Closed d =>
    dsimp only
    iapply mpmc_closed_no_producer γ n_prod n_cons P R sent0 recv d sent $$ [$HsentI $Hm $Hprod]
  | _ => itrivial

theorem wp_mpmc_send (γ : MpmcNames) (ch : Loc) (n_prod n_cons : Nat) (P : V → IProp GF)
    (R : MSet → IProp GF) (sent : MSet) (v : V) :
    {{ isMpmc γ ch n_prod n_cons P R ∗ mpmcProducer γ sent ∗ P v }}
      (App (App (Val (chan.send t)) (Val #ch)) (Val #v))
    {{ RET #(); mpmcProducer γ (sent • msetSingleton v) }} := by
  iintro %Φ ⟨#Hmpmc, Hprod, HP⟩ HΦ
  ihave #Hch : isChan ch γ.mpmcChanName V $$ [Hmpmc]
  · unfold isMpmc; icases Hmpmc with ⟨$, -⟩
  iapply chan.wp_send ch v γ.mpmcChanName $$ Hch
  iintro ⟨Hlc1, Hlc2, _, _⟩
  iapply mpmc_send_au γ ch n_prod n_cons P R sent v (Φ #()) $$ Hmpmc [$Hlc1 $Hlc2] [$Hprod $HP] HΦ

omit [IntoValTyped (GF := GF) V t] in
set_option maxHeartbeats 800000 in
theorem mpmc_rcv_au (γ : MpmcNames) (ch : Loc) (n_prod n_cons : Nat) (P : V → IProp GF)
    (R : MSet → IProp GF) (received : MSet) (Φ : V → Bool → IProp GF) :
    ⊢ isMpmc γ ch n_prod n_cons P R -∗ £ 1 ∗ £ 1 -∗ mpmcConsumer γ received -∗
      ▷ (∀ (v : V) (ok : Bool),
        (if ok then iprop(P v ∗ mpmcConsumer γ (received • msetSingleton v))
         else iprop(isClosed γ ∗ mpmcConsumer γ received ∗ ⌜v = zero_val V⌝)) -∗ Φ v ok) -∗
      recvAu γ.mpmcChanName V Φ := by
  unfold isMpmc recvAu
  iintro ⟨#Hchan, #Hinv⟩ ⟨Hlc1, Hlc2⟩ Hcons Hcont
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc1 Hi with Hi
  icases mpmcInv_elim _ _ _ _ _ $$ Hi with ⟨%s, %sent, %recv, Hch, HsentI, HrecvI, %Hpure, Hclosed, Hm⟩
  obtain ⟨Hrel, Hncons, Hnprod⟩ := Hpure
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists s
  iframe Hch
  unfold mpmcConsumer
  cases s with
  | Buffered b =>
    cases b with
    | nil => itrivial
    | cons v rest =>
      dsimp only
      iintro Hoc
      imod update_client _ _ _ _ _ _ (mset_local_update recv received (msetSingleton v))
        $$ HrecvI Hcons with ⟨HrecvI, Hcons⟩
      simp only [mpmcInvMatch]
      icases BigSepL.bigSepL_cons.1 $$ Hm with ⟨HPv, Hrest⟩
      imod Hmask with -
      imod Hclose $$ [Hoc HsentI HrecvI Hclosed Hrest] with -
      · inext
        iapply mpmcInv_intro γ n_prod n_cons P R (.Buffered rest) sent (recv • msetSingleton v)
          ⟨by subst Hrel; simp [inflightMset]; ac_rfl, Hncons, Hnprod⟩
          $$ Hoc HsentI HrecvI [Hclosed] [Hrest]
        · simp only [mpmcClosedPart]; iexact Hclosed
        · simp only [mpmcInvMatch]; iexact Hrest
      imodintro
      iapply Hcont
      simp only [↓reduceIte, mpmcConsumer]
      iframe
  | Idle =>
    dsimp only
    iintro Hoc
    imod Hmask with -
    imod Hclose $$ [Hoc HsentI HrecvI Hclosed] with -
    · inext
      iapply mpmcInv_intro γ n_prod n_cons P R .RcvPending sent recv
        ⟨by simpa [inflightMset] using Hrel, Hncons, Hnprod⟩ $$ Hoc HsentI HrecvI [Hclosed] []
      · simp only [mpmcClosedPart]; iexact Hclosed
      · simp only [mpmcInvMatch]; itrivial
    imodintro
    unfold recvNestedAu
    iinv Hinv with Hi Hclose
    imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc2 Hi with Hi
    icases mpmcInv_elim _ _ _ _ _ $$ Hi with
      ⟨%s, %sent, %recv, Hch, HsentI, HrecvI, %Hpure, Hclosed, Hm⟩
    obtain ⟨Hrel, Hncons, Hnprod⟩ := Hpure
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iexists s
    iframe Hch
    cases s with
    | SndCommit v =>
      dsimp only
      iintro Hoc
      imod update_client _ _ _ _ _ _ (mset_local_update recv received (msetSingleton v))
        $$ HrecvI Hcons with ⟨HrecvI, Hcons⟩
      simp only [mpmcInvMatch]
      imod Hmask with -
      imod Hclose $$ [Hoc HsentI HrecvI Hclosed] with -
      · inext
        iapply mpmcInv_intro γ n_prod n_cons P R .Idle sent (recv • msetSingleton v)
          ⟨by simpa [inflightMset] using Hrel, Hncons, Hnprod⟩ $$ Hoc HsentI HrecvI [Hclosed] []
        · simp only [mpmcClosedPart]; iexact Hclosed
        · simp only [mpmcInvMatch]; itrivial
      imodintro
      iapply Hcont
      simp only [↓reduceIte, mpmcConsumer]
      iframe
    | Closed d =>
      cases d with
      | nil =>
        dsimp only
        iintro Hoc
        imod Hmask with -
        simp only [mpmcClosedPart]
        icases Hclosed with #Hclosed
        simp only [mpmcInvMatch]
        icases Hm with ⟨%Hsr, Hprods, (HR | ⟨%conss, %Hlen, Hconss⟩)⟩
        · imod Hclose $$ [Hoc HsentI HrecvI Hprods HR] with -
          · inext
            iapply mpmcInv_intro γ n_prod n_cons P R (.Closed []) sent recv ⟨by simpa using Hrel, Hncons, Hnprod⟩
              $$ Hoc HsentI HrecvI [] [Hprods HR]
            · simp only [mpmcClosedPart]; iexact Hclosed
            · simp only [mpmcInvMatch]
              isplitr
              · ipureintro; exact Hsr
              isplitl [Hprods]
              · iexact Hprods
              · ileft; iexact HR
          imodintro
          iapply Hcont
          simp only [Bool.false_eq_true, ↓reduceIte]
          unfold isClosed
          iframe
          iframe #
        · iexfalso
          subst Hlen
          simp only [mpmcConsumer]
          iapply clients_extra_false _ _ conss received $$ [$HrecvI $Hconss $Hcons]
      | cons _ _ => itrivial
    | _ => itrivial
  | SndPending v =>
    dsimp only
    iintro Hoc
    imod update_client _ _ _ _ _ _ (mset_local_update recv received (msetSingleton v))
      $$ HrecvI Hcons with ⟨HrecvI, Hcons⟩
    simp only [mpmcInvMatch]
    imod Hmask with -
    imod Hclose $$ [Hoc HsentI HrecvI Hclosed] with -
    · inext
      iapply mpmcInv_intro γ n_prod n_cons P R .RcvCommit sent (recv • msetSingleton v)
        ⟨by simpa [inflightMset] using Hrel, Hncons, Hnprod⟩ $$ Hoc HsentI HrecvI [Hclosed] []
      · simp only [mpmcClosedPart]; iexact Hclosed
      · simp only [mpmcInvMatch]; itrivial
    imodintro
    iapply Hcont
    simp only [↓reduceIte, mpmcConsumer]
    iframe
  | Closed d =>
    cases d with
    | nil =>
      dsimp only
      iintro Hoc
      imod Hmask with -
      simp only [mpmcClosedPart]
      icases Hclosed with #Hclosed
      simp only [mpmcInvMatch]
      icases Hm with ⟨%Hsr, Hprods, (HR | ⟨%conss, %Hlen, Hconss⟩)⟩
      · imod Hclose $$ [Hoc HsentI HrecvI Hprods HR] with -
        · inext
          iapply mpmcInv_intro γ n_prod n_cons P R (.Closed []) sent recv ⟨by simpa using Hrel, Hncons, Hnprod⟩
            $$ Hoc HsentI HrecvI [] [Hprods HR]
          · simp only [mpmcClosedPart]; iexact Hclosed
          · simp only [mpmcInvMatch]
            isplitr
            · ipureintro; exact Hsr
            isplitl [Hprods]
            · iexact Hprods
            · ileft; iexact HR
        imodintro
        iapply Hcont
        simp only [Bool.false_eq_true, ↓reduceIte]
        unfold isClosed
        iframe
        iframe #
      · iexfalso
        subst Hlen
        simp only [mpmcConsumer]
        iapply clients_extra_false _ _ conss received $$ [$HrecvI $Hconss $Hcons]
    | cons v rest =>
      dsimp only
      iintro Hoc
      imod update_client _ _ _ _ _ _ (mset_local_update recv received (msetSingleton v))
        $$ HrecvI Hcons with ⟨HrecvI, Hcons⟩
      imod Hmask with -
      simp only [mpmcInvMatch]
      icases Hm with ⟨Hbig, Hmp, HR⟩
      icases BigSepL.bigSepL_cons.1 $$ Hbig with ⟨HPv, Hrest⟩
      cases rest with
      | nil =>
        simp only [mpmcClosedPart]
        imod dghostVar_update true _ _ $$ Hclosed with Hclosed
        imod dghostVar_persist _ _ _ $$ Hclosed with #Hclosed
        imod Hclose $$ [Hoc HsentI HrecvI Hmp HR] with -
        · inext
          iapply mpmcInv_intro γ n_prod n_cons P R (.Closed []) sent (recv • msetSingleton v)
            ⟨by subst Hrel; simp [inflightMset], Hncons, Hnprod⟩ $$ Hoc HsentI HrecvI [] [Hmp HR]
          · simp only [mpmcClosedPart]; iexact Hclosed
          · simp only [mpmcInvMatch]
            isplitr
            · ipureintro; subst Hrel; simp [inflightMset]
            isplitl [Hmp]
            · iexact Hmp
            · ileft; iexact HR
        imodintro
        iapply Hcont
        simp only [↓reduceIte, mpmcConsumer]
        iframe
      | cons w ws =>
        imod Hclose $$ [Hoc HsentI HrecvI Hclosed Hrest Hmp HR] with -
        · inext
          iapply mpmcInv_intro γ n_prod n_cons P R (.Closed (w :: ws)) sent (recv • msetSingleton v)
            ⟨by subst Hrel; simp [inflightMset]; ac_rfl, Hncons, Hnprod⟩
            $$ Hoc HsentI HrecvI [Hclosed] [Hrest Hmp HR]
          · simp only [mpmcClosedPart]; iexact Hclosed
          · simp only [mpmcInvMatch]
            isplitl [Hrest]
            · iexact Hrest
            isplitl [Hmp]
            · iexact Hmp
            · iexact HR
        imodintro
        iapply Hcont
        simp only [↓reduceIte, mpmcConsumer]
        iframe
  | _ => itrivial

theorem wp_mpmc_receive (γ : MpmcNames) (ch : Loc) (n_prod n_cons : Nat) (P : V → IProp GF)
    (R : MSet → IProp GF) (received : MSet) :
    {{ isMpmc γ ch n_prod n_cons P R ∗ mpmcConsumer γ received }}
      (App (Val (chan.receive t)) (Val #ch))
    {{ (v : V) (ok : Bool), RET (PairV #v #ok);
        (if ok then iprop(P v ∗ mpmcConsumer γ (received • msetSingleton v))
         else iprop(isClosed γ ∗ mpmcConsumer γ received ∗ ⌜v = zero_val V⌝)) }} := by
  iintro %Φ ⟨#Hmpmc, Hcons⟩ HΦ
  ihave #Hch : isChan ch γ.mpmcChanName V $$ [Hmpmc]
  · unfold isMpmc; icases Hmpmc with ⟨$, -⟩
  iapply chan.wp_receive ch γ.mpmcChanName $$ Hch
  iintro ⟨Hlc1, Hlc2, _, _⟩
  iapply mpmc_rcv_au γ ch n_prod n_cons P R received (fun v ok => Φ (PairV #v #ok))
    $$ Hmpmc [$Hlc1 $Hlc2] Hcons
  inext
  iintro %v %ok H
  iapply HΦ $$ %v %ok H

omit [IntoValTyped (GF := GF) V t] in
set_option maxHeartbeats 800000 in
theorem mpmc_close_au (γ : MpmcNames) (ch : Loc) (n_prod n_cons : Nat) (P : V → IProp GF)
    (R : MSet → IProp GF) (producers : List MSet) (Φ : IProp GF) (hlen : producers.length = n_prod) :
    ⊢ isMpmc γ ch n_prod n_cons P R -∗ £ 1 -∗
      ([∗list] s_i ∈ producers, mpmcProducer γ s_i) ∗ R (msetSum producers) -∗
      ▷ Φ -∗ closeAu γ.mpmcChanName V Φ := by
  subst hlen
  unfold isMpmc closeAu
  iintro ⟨#Hchan, #Hinv⟩ Hlc1 ⟨Hprods, HR⟩ Hcont
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc1 Hi with Hi
  icases mpmcInv_elim _ _ _ _ _ $$ Hi with ⟨%s, %sent, %recv, Hch, HsentI, HrecvI, %Hpure, Hclosed, Hm⟩
  obtain ⟨Hrel, Hncons, Hnprod⟩ := Hpure
  simp only [mpmcProducer]
  icases persistent_entails_left (clients_agree _ _ _) $$ [HsentI Hprods] with ⟨⟨HsentI, Hprods⟩, %Hsum⟩
  · isplitl [HsentI]
    · iexact HsentI
    · iexact Hprods
  subst Hsum
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists s
  iframe Hch
  cases s with
  | Buffered buff =>
    dsimp only
    iintro Hoc
    imod Hmask with -
    cases buff with
    | nil =>
      simp only [mpmcClosedPart]
      imod dghostVar_update true _ _ $$ Hclosed with Hclosed
      imod dghostVar_persist _ _ _ $$ Hclosed with #Hclosed
      imod Hclose $$ [Hoc HsentI HrecvI Hprods HR] with -
      · inext
        iapply mpmcInv_intro γ producers.length n_cons P R (.Closed []) (msetSum producers) recv
          ⟨by simpa [inflightMset] using Hrel, Hncons, Hnprod⟩ $$ Hoc HsentI HrecvI [] [Hprods HR]
        · simp only [mpmcClosedPart]; iexact Hclosed
        · simp only [mpmcInvMatch, mpmcProducer]
          isplitr
          · ipureintro; simpa [inflightMset] using Hrel
          isplitl [Hprods]
          · iexists producers
            isplitr
            · ipureintro; rfl
            · iexact Hprods
          · ileft; iexact HR
      imodintro
      iexact Hcont
    | cons w ws =>
      imod Hclose $$ [Hoc HsentI HrecvI Hclosed Hm Hprods HR] with -
      · inext
        iapply mpmcInv_intro γ producers.length n_cons P R (.Closed (w :: ws)) (msetSum producers)
          recv ⟨by simpa [inflightMset] using Hrel, Hncons, Hnprod⟩
          $$ Hoc HsentI HrecvI [Hclosed] [Hm Hprods HR]
        · simp only [mpmcClosedPart]; iexact Hclosed
        · simp only [mpmcInvMatch, mpmcProducer]
          isplitl [Hm]
          · iexact Hm
          isplitl [Hprods]
          · iexists producers
            isplitr
            · ipureintro; rfl
            · iexact Hprods
          · iexact HR
      imodintro
      iexact Hcont
  | Idle =>
    dsimp only
    iintro Hoc
    imod Hmask with -
    simp only [mpmcClosedPart]
    imod dghostVar_update true _ _ $$ Hclosed with Hclosed
    imod dghostVar_persist _ _ _ $$ Hclosed with #Hclosed
    imod Hclose $$ [Hoc HsentI HrecvI Hprods HR] with -
    · inext
      iapply mpmcInv_intro γ producers.length n_cons P R (.Closed []) (msetSum producers) recv
        ⟨by simpa [inflightMset] using Hrel, Hncons, Hnprod⟩ $$ Hoc HsentI HrecvI [] [Hprods HR]
      · simp only [mpmcClosedPart]; iexact Hclosed
      · simp only [mpmcInvMatch, mpmcProducer]
        isplitr
        · ipureintro; simpa [inflightMset] using Hrel
        isplitl [Hprods]
        · iexists producers
          isplitr
          · ipureintro; rfl
          · iexact Hprods
        · ileft; iexact HR
    imodintro
    iexact Hcont
  | Closed d =>
    dsimp only
    cases producers with
    | nil => exact absurd Hnprod (by decide)
    | cons p ps =>
      icases BigSepL.bigSepL_cons.1 $$ Hprods with ⟨Hp, -⟩
      iapply mpmc_closed_no_producer γ _ n_cons P R _ recv d p $$ [$HsentI $Hm Hp]
      simp only [mpmcProducer]
      iexact Hp
  | _ => itrivial

theorem wp_mpmc_close (γ : MpmcNames) (ch : Loc) (n_prod n_cons : Nat) (P : V → IProp GF)
    (R : MSet → IProp GF) (producers : List MSet) {ct : go.GoType} {dir : go.ChanDir}
    [ct ↓u go.ChannelType dir t] (hlen : producers.length = n_prod) :
    {{ isMpmc γ ch n_prod n_cons P R ∗ ([∗list] s_i ∈ producers, mpmcProducer γ s_i) ∗
        R (msetSum producers) }}
      (App (Val #(functions go.close [ct])) (Val #ch))
    {{ RET #(); True }} := by
  iintro %Φ ⟨#Hmpmc, Hprods, HR⟩ HΦ
  ihave #Hch : isChan ch γ.mpmcChanName V $$ [Hmpmc]
  · unfold isMpmc; icases Hmpmc with ⟨$, -⟩
  iapply chan.wp_close (ct := ct) ch γ.mpmcChanName $$ Hch
  iintro ⟨Hlc1, _, _, _⟩
  iapply mpmc_close_au γ ch n_prod n_cons P R producers (Φ #()) hlen $$ Hmpmc Hlc1 [$Hprods $HR]
  inext
  iapply HΦ
  itrivial

omit [IntoValTyped (GF := GF) V t] in
set_option maxHeartbeats 400000 in
theorem mpmc_get_final_resource (γ : MpmcNames) (ch : Loc) (n_prod n_cons : Nat)
    (P : V → IProp GF) (R : MSet → IProp GF) (consumers : List MSet)
    (hlen : consumers.length = n_cons) :
    ⊢ £ 1 -∗ isMpmc γ ch n_prod n_cons P R -∗ isClosed γ -∗
      ([∗list] r_i ∈ consumers, mpmcConsumer γ r_i) ={⊤}=∗ R (msetSum consumers) := by
  subst hlen
  unfold isMpmc
  iintro Hlc ⟨#Hchan, #Hinv⟩ #Hcl Hcons
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc Hi with Hi
  icases mpmcInv_elim _ _ _ _ _ $$ Hi with ⟨%s, %sent, %recv, Hch, HsentI, HrecvI, %Hpure, Hclosed, Hm⟩
  obtain ⟨Hrel, Hncons, Hnprod⟩ := Hpure
  unfold isClosed
  have hs : s = .Closed [] ∨ mpmcClosedPart (GF := GF) γ s =
      dghostVar γ.mpmcClosedName (DFrac.own 1) false := by
    rcases s with _ | _ | _ | _ | _ | _ | (_ | ⟨_, _⟩) <;> simp [mpmcClosedPart]
  rcases hs with rfl | hs
  · simp only [mpmcInvMatch, mpmcConsumer]
    icases Hm with ⟨%Hsr, Hprods, (HR | ⟨%conss, %Hlen, Hconss⟩)⟩
    · icases persistent_entails_left (clients_agree _ _ _) $$ [HrecvI Hcons]
        with ⟨⟨HrecvI, Hcons⟩, %Hsum⟩
      · isplitl [HrecvI]
        · iexact HrecvI
        · iexact Hcons
      subst Hsum
      subst Hsr
      imod Hclose $$ [Hch HsentI HrecvI Hclosed Hprods Hcons] with -
      · inext
        iapply mpmcInv_intro γ n_prod consumers.length P R (.Closed []) (msetSum consumers)
          (msetSum consumers) ⟨Hrel, Hncons, Hnprod⟩ $$ Hch HsentI HrecvI Hclosed [Hprods Hcons]
        simp only [mpmcInvMatch, mpmcConsumer]
        isplitr
        · ipureintro; trivial
        isplitl [Hprods]
        · iexact Hprods
        · iright
          iexists consumers
          isplitr
          · ipureintro; rfl
          · iexact Hcons
      imodintro
      iexact HR
    · iexfalso
      cases consumers with
      | nil => exact absurd Hncons (by decide)
      | cons c cs =>
        icases BigSepL.bigSepL_cons.1 $$ Hcons with ⟨Hc, -⟩
        rw [← Hlen]
        iapply clients_extra_false _ _ conss c $$ [$HrecvI $Hconss $Hc]
  · rw [hs]
    ihave %Hbad := dghostVar_agree _ _ _ _ _ $$ Hcl Hclosed
    cases Hbad

end mpmc

end Perennial
