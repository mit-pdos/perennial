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
  `UCMRA.unit`; `{[+ v +]}` is `mset_singleton v`, `list_to_set_disj` is `list_to_mset`, and
  `foldr (⊎) ∅` is `mset_sum`. The contribution camera is used at
  `A := Auth (gmap Pos positive)` (code `authR (gmapUR pos positiveR)`), and only
  fragments `◯ m` are stored (`mset_frag`).
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
abbrev mset : Type := gmap Pos positive

section mset
variable {V : Type} [Pos.Countable V]

def mset_singleton (v : V) : mset := {[Pos.Countable.encode v := positive.one]}

def list_to_mset (l : List V) : mset := l.foldr (fun v acc => mset_singleton v • acc) UCMRA.unit

/-- `foldr (⊎) ∅`. -/
def mset_sum (ys : List (mset)) : mset := ys.foldr (· • ·) UCMRA.unit

instance mset_assoc : Std.Associative (α := mset) (· • ·) := ⟨fun _ _ _ => CMRA.assoc.symm⟩
instance mset_comm : Std.Commutative (α := mset) (· • ·) := ⟨fun _ _ => CMRA.comm⟩

@[simp] theorem mset_unit_r (a : mset) : a • UCMRA.unit = a := CMRA.unit_right_id
@[simp] theorem mset_unit_l (a : mset) : UCMRA.unit • a = a := UCMRA.unit_left_id

omit [Pos.Countable V] in
@[simp] theorem mset_sum_nil : mset_sum ([] : List mset) = UCMRA.unit := rfl
omit [Pos.Countable V] in
@[simp] theorem mset_sum_cons (y : mset) (ys : List mset) : mset_sum (y :: ys) = y • mset_sum ys :=
  rfl

@[simp] theorem list_to_mset_nil : list_to_mset ([] : List V) = UCMRA.unit := rfl
@[simp] theorem list_to_mset_cons (v : V) (l : List V) :
    list_to_mset (v :: l) = mset_singleton v • list_to_mset l := rfl
@[simp] theorem list_to_mset_app (l1 l2 : List V) :
    list_to_mset (l1 ++ l2) = list_to_mset l1 • list_to_mset l2 := by
  induction l1 with
  | nil => simp
  | cons v l ih => simp only [List.cons_append, list_to_mset_cons, ih]; ac_rfl

theorem mset_valid (m : mset) : ✓ m := fun k => by
  cases h : (Iris.Std.PartialMap.get? m k : Option positive) with
  | none => exact trivial
  | some x => exact trivial

/-- The contribution camera element of a multiset. -/
abbrev mset_frag (m : mset) : Auth (gmap Pos positive) := Auth.frag m

theorem mset_frag_op (a b : mset) : mset_frag (a • b) = mset_frag a • mset_frag b :=
  Auth.frag_op

theorem mset_frag_unit : mset_frag (UCMRA.unit : mset) = UCMRA.unit := rfl

theorem mset_frag_inj {a b : mset} (h : mset_frag a = mset_frag b) : a = b := Auth.frag_inj h

theorem mset_frag_valid (m : mset) : ✓ mset_frag m := Auth.frag_valid.mpr (mset_valid m)

/-- `(X, Y) ~l~> (X ⊎ Z, Y ⊎ Z)` (Rocq `gmultiset_disj_union_local_update`). -/
theorem mset_local_update (X Y Z : mset) :
    (mset_frag X, mset_frag Y) ~l~> (mset_frag (X • Z), mset_frag (Y • Z)) := by
  have h := LocalUpdate.op_discrete (mset_frag X) (mset_frag Y) (mset_frag Z)
    (fun _ => by rw [← mset_frag_op]; exact mset_frag_valid _)
  rwa [← mset_frag_op, ← mset_frag_op, CMRA.comm (x := Z), CMRA.comm (x := Z)] at h

end mset

/-! ## Contribution lemmas for all clients at once -/

section contrib_all
variable {GF : BundledGFunctors} [allG GF]

theorem positive_of_nat_succ (n : Nat) (hn : n ≠ 0) :
    positive.of_nat (n + 1) = positive.one + positive.of_nat n := by
  ext; simp [positive.of_nat, positive.one]; omega

/-- All the clients `ys` together. -/
theorem clients_own (γ : GName) (ys : List mset) (hne : ys ≠ []) :
    ([∗list] y ∈ ys, client (GF := GF) γ (mset_frag y)) ⊢
      own γ (Auth.frag (contrib_cl (positive.of_nat ys.length) (mset_frag (mset_sum ys)))) := by
  induction ys with
  | nil => exact absurd rfl hne
  | cons y ys ih =>
    cases ys with
    | nil =>
      refine BigSepL.bigSepL_singleton.1.trans ?_
      unfold client
      simp only [mset_sum, List.foldr, List.length_cons, List.length_nil, CMRA.unit_right_id]
      exact .rfl
    | cons y' ys' =>
      refine BigSepL.bigSepL_cons.1.trans ((sep_mono_right (ih (List.cons_ne_nil _ _))).trans ?_)
      unfold client
      refine (own_op γ _ _).2.trans (BiEntails.of_eq ?_).1
      have hp : positive.one + positive.of_nat (y' :: ys').length =
          positive.of_nat (y :: y' :: ys').length := by
        ext; simp [positive.of_nat, positive.one]
      rw [← Auth.frag_op, contrib_cl_op, hp, ← mset_frag_op]
      rfl

/-- The server's total is the sum of all `n` clients (replaces Rocq `auth_map_agree`). -/
theorem clients_agree (γ : GName) (X : mset) (ys : List mset) :
    server (GF := GF) γ ys.length (mset_frag X) ∗ ([∗list] y ∈ ys, client γ (mset_frag y)) ⊢
      ⌜X = mset_sum ys⌝ := by
  cases ys with
  | nil =>
    iintro ⟨Hs, -⟩
    ihave H := server_0_empty γ _ $$ Hs
    icases discrete_eq_mp $$ H with %H
    ipureintro
    exact mset_frag_inj H
  | cons y ys =>
    iintro ⟨Hs, Hc⟩
    ihave Hc := clients_own γ (y :: ys) (by simp) $$ Hc
    unfold server
    simp only [List.length_cons, Nat.add_one_ne_zero, ↓reduceIte]
    icases (own_valid_pure_2 γ _ _) $$ Hs Hc with %Hv
    ipureintro
    obtain ⟨hinc, _⟩ := Auth.auth_both_valid_discrete.mp Hv
    rcases contrib_cl_inc _ _ _ _ hinc with ⟨_, h⟩ | ⟨r, hr, _⟩
    · exact mset_frag_inj h
    · exact absurd hr.symm (positive_add_ne_self _ _)

/-- An extra client contradicts a server with `n` clients (replaces the uses of Rocq
`bulk_dealloc_all` for contradictions). -/
theorem clients_extra_false (γ : GName) (X : mset) (ys : List mset) (y : mset) :
    server (GF := GF) γ ys.length (mset_frag X) ∗ ([∗list] z ∈ ys, client γ (mset_frag z)) ∗
      client γ (mset_frag y) ⊢ False := by
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
    change contrib_cl positive.one (mset_frag y) • contrib_cl _ _ ≼ _ at hinc
    rw [contrib_cl_op] at hinc
    rcases contrib_cl_inc _ _ _ _ hinc with ⟨h, _⟩ | ⟨r, hr, _⟩
    · have := congrArg positive.pred h; simp [positive.of_nat, positive.one] at this
    · have := congrArg positive.pred hr; simp [positive.of_nat, positive.one] at this; omega

end contrib_all

/-! ## MPMC channels -/

structure mpmc_names where
  mpmc_chan_name : chan_names
  mpmc_sent_name : GName
  mpmc_recv_name : GName
  mpmc_closed_name : GName

section mpmc
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : heapGS HasLC.hasLC GF] [allG GF]
variable [sem : go.Semantics]
variable {V : Type} [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V] {t : go.type}
  [IntoValTyped (GF := GF) V t]

omit [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V t] in
/-- (Missing from `Perennial/Ghost/DGhostVar.lean`.) -/
instance dghost_var_discard_persistent {A : Type} [Pos.Countable A] (γ : GName) (a : A) :
    Persistent (dghost_var (GF := GF) γ DFrac.discard a) := by
  unfold dghost_var; infer_instance

def is_closed (γ : mpmc_names) : IProp GF :=
  dghost_var γ.mpmc_closed_name DFrac.discard true

instance is_closed_persistent (γ : mpmc_names) : Persistent (is_closed (GF := GF) γ) := by
  unfold is_closed; infer_instance

def mpmc_producer (γ : mpmc_names) (sent : mset) : IProp GF :=
  client γ.mpmc_sent_name (mset_frag sent)

def mpmc_consumer (γ : mpmc_names) (received : mset) : IProp GF :=
  client γ.mpmc_recv_name (mset_frag received)

omit [ZeroVal V] [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V t] in
variable (V) in
def inflight_mset (s : chanstate.t V) : mset :=
  match s with
  | .Buffered buff => list_to_mset buff
  | .SndPending v | .SndCommit v => mset_singleton v
  | .Closed drain => list_to_mset drain
  | _ => UCMRA.unit

/-- The `"Hclosed"` part of the MPMC invariant. -/
def mpmc_closed_part (γ : mpmc_names) (s : chanstate.t V) : IProp GF :=
  match s with
  | .Closed [] => dghost_var γ.mpmc_closed_name DFrac.discard true
  | _ => dghost_var γ.mpmc_closed_name (DFrac.own 1) false

/-- The state-dependent resources of the MPMC invariant. -/
def mpmc_inv_match (γ : mpmc_names) (n_prod n_cons : Nat) (P : V → IProp GF)
    (R : mset → IProp GF) (sent recv : mset) (s : chanstate.t V) : IProp GF :=
  match s with
  | .Buffered buff => iprop([∗list] v ∈ buff, P v)
  | .SndPending v => P v
  | .SndCommit v => P v
  | .Closed [] =>
      iprop(⌜sent = recv⌝ ∗
        (∃ prods : List mset, ⌜prods.length = n_prod⌝ ∗ [∗list] s_i ∈ prods, mpmc_producer γ s_i) ∗
        (R sent ∨ ∃ conss : List mset, ⌜conss.length = n_cons⌝ ∗
          [∗list] r_i ∈ conss, mpmc_consumer γ r_i))
  | .Closed drain =>
      iprop(([∗list] v ∈ drain, P v) ∗
        (∃ prods : List mset, ⌜prods.length = n_prod⌝ ∗ [∗list] s_i ∈ prods, mpmc_producer γ s_i) ∗
        R sent)
  | _ => iprop(True)

@[irreducible] def mpmc_inv (γ : mpmc_names) (n_prod n_cons : Nat) (P : V → IProp GF)
    (R : mset → IProp GF) : IProp GF :=
  iprop(∃ (s : chanstate.t V) (sent recv : mset),
    own_chan γ.mpmc_chan_name V s ∗
    server γ.mpmc_sent_name n_prod (mset_frag sent) ∗
    server γ.mpmc_recv_name n_cons (mset_frag recv) ∗
    ⌜sent = recv • inflight_mset V s ∧ n_cons > 0 ∧ n_prod > 0⌝ ∗
    mpmc_closed_part γ s ∗
    mpmc_inv_match γ n_prod n_cons P R sent recv s)

def is_mpmc (γ : mpmc_names) (ch : loc) (n_prod n_cons : Nat) (P : V → IProp GF)
    (R : mset → IProp GF) : IProp GF :=
  iprop(is_chan ch γ.mpmc_chan_name V ∗ inv nroot (mpmc_inv γ n_prod n_cons P R))

instance is_mpmc_persistent (γ : mpmc_names) (ch : loc) (n_prod n_cons : Nat)
    (P : V → IProp GF) (R : mset → IProp GF) :
    Persistent (is_mpmc γ ch n_prod n_cons P R) := by
  unfold is_mpmc; infer_instance

omit [IntoValTyped (GF := GF) V t] in
theorem mpmc_inv_elim (γ : mpmc_names) (n_prod n_cons : Nat) (P : V → IProp GF)
    (R : mset → IProp GF) :
    mpmc_inv γ n_prod n_cons P R ⊢ ∃ (s : chanstate.t V) (sent recv : mset),
      own_chan γ.mpmc_chan_name V s ∗
      server γ.mpmc_sent_name n_prod (mset_frag sent) ∗
      server γ.mpmc_recv_name n_cons (mset_frag recv) ∗
      ⌜sent = recv • inflight_mset V s ∧ n_cons > 0 ∧ n_prod > 0⌝ ∗
      mpmc_closed_part γ s ∗
      mpmc_inv_match γ n_prod n_cons P R sent recv s := by
  unfold mpmc_inv; exact .rfl

omit [IntoValTyped (GF := GF) V t] in
theorem mpmc_inv_intro (γ : mpmc_names) (n_prod n_cons : Nat) (P : V → IProp GF)
    (R : mset → IProp GF) (s : chanstate.t V) (sent recv : mset)
    (h : sent = recv • inflight_mset V s ∧ n_cons > 0 ∧ n_prod > 0) :
    ⊢ own_chan γ.mpmc_chan_name V s -∗
      server γ.mpmc_sent_name n_prod (mset_frag sent) -∗
      server γ.mpmc_recv_name n_cons (mset_frag recv) -∗
      mpmc_closed_part γ s -∗
      mpmc_inv_match γ n_prod n_cons P R sent recv s -∗
      mpmc_inv γ n_prod n_cons P R := by
  iintro H1 H2 H3 H4 H5
  unfold mpmc_inv
  iexists s, sent, recv
  isplitl [H1]; · iexact H1
  isplitl [H2]; · iexact H2
  isplitl [H3]; · iexact H3
  isplitr
  · ipureintro; exact h
  isplitl [H4]; · iexact H4
  · iexact H5

omit [IntoValTyped (GF := GF) V t] in
theorem start_mpmc (ch : loc) (P : V → IProp GF) (R : mset → IProp GF) (γ : chan_names)
    (n_prod n_cons : Nat) (s : chanstate.t V)
    (Hs : match s with | .Buffered [] => True | .Idle => True | _ => False)
    (Hprod : n_prod > 0) (Hcons : n_cons > 0) :
    ⊢ is_chan ch γ V -∗ own_chan γ V s ={⊤}=∗
      ∃ γmpmc, is_mpmc γmpmc ch n_prod n_cons P R ∗
        ([∗list] _k ↦ Q ∈ List.replicate n_prod (mpmc_producer γmpmc UCMRA.unit), Q) ∗
        ([∗list] _k ↦ Q ∈ List.replicate n_cons (mpmc_consumer γmpmc UCMRA.unit), Q) := by
  have hs : s = .Buffered [] ∨ s = .Idle := by
    rcases s with (_ | ⟨_, _⟩) | _ | _ | _ | _ | _ | _ <;> simp_all
  iintro #Hch Hoc
  imod dghost_var_alloc false with ⟨%γclosed, Hclosed⟩
  imod contribution_init_pow (A := Auth (gmap Pos positive)) n_prod with ⟨%γsent, HsentAuth, HsentFrags⟩
  imod contribution_init_pow (A := Auth (gmap Pos positive)) n_cons with ⟨%γrecv, HrecvAuth, HrecvFrags⟩
  iexists ⟨γ, γsent, γrecv, γclosed⟩
  imod inv_alloc nroot ⊤ (mpmc_inv ⟨γ, γsent, γrecv, γclosed⟩ n_prod n_cons P R)
    $$ [Hoc HsentAuth HrecvAuth Hclosed] with #Hinv
  · inext
    rcases hs with rfl | rfl
    all_goals
      iapply mpmc_inv_intro ⟨γ, γsent, γrecv, γclosed⟩ n_prod n_cons P R _ UCMRA.unit UCMRA.unit
        ⟨by simp [inflight_mset], Hcons, Hprod⟩ $$ Hoc HsentAuth HrecvAuth [Hclosed] []
      · simp only [mpmc_closed_part]; iexact Hclosed
      · simp only [mpmc_inv_match]
        first | itrivial | (iapply BigSepL.bigSepL_nil.2; iempintro)
  imodintro
  unfold is_mpmc mpmc_producer mpmc_consumer
  iframe
  iframe #

omit [IntoValTyped (GF := GF) V t] in
/-- No extra producer once the channel is closed. -/
theorem mpmc_closed_no_producer (γ : mpmc_names) (n_prod n_cons : Nat) (P : V → IProp GF)
    (R : mset → IProp GF) (sent recv : mset) (d : List V) (y : mset) :
    server γ.mpmc_sent_name n_prod (mset_frag sent) ∗
      mpmc_inv_match γ n_prod n_cons P R sent recv (.Closed d) ∗ mpmc_producer γ y ⊢ False := by
  iintro ⟨HsentI, Hm, Hprod⟩
  cases d with
  | nil =>
    simp only [mpmc_inv_match, mpmc_producer]
    icases Hm with ⟨-, ⟨%prods, %Hlen, Hprods⟩, -⟩
    subst Hlen
    iapply clients_extra_false _ _ prods y $$ [$HsentI $Hprods $Hprod]
  | cons _ _ =>
    simp only [mpmc_inv_match, mpmc_producer]
    icases Hm with ⟨-, ⟨%prods, %Hlen, Hprods⟩, -⟩
    subst Hlen
    iapply clients_extra_false _ _ prods y $$ [$HsentI $Hprods $Hprod]

omit [IntoValTyped (GF := GF) V t] in
set_option maxHeartbeats 400000 in
theorem mpmc_send_au (γ : mpmc_names) (ch : loc) (n_prod n_cons : Nat) (P : V → IProp GF)
    (R : mset → IProp GF) (sent : mset) (v : V) (Φ : IProp GF) :
    ⊢ is_mpmc γ ch n_prod n_cons P R -∗ £ 1 ∗ £ 1 -∗ mpmc_producer γ sent ∗ P v -∗
      ▷ (mpmc_producer γ (sent • mset_singleton v) -∗ Φ) -∗ send_au γ.mpmc_chan_name v Φ := by
  unfold is_mpmc send_au
  iintro ⟨#Hchan, #Hinv⟩ ⟨Hlc1, Hlc2⟩ ⟨Hprod, HP⟩ Hcont
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc1 Hi with Hi
  icases mpmc_inv_elim _ _ _ _ _ $$ Hi with ⟨%s, %sent0, %recv, Hch, HsentI, HrecvI, %Hpure, Hclosed, Hm⟩
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
    unfold mpmc_producer
    imod update_client _ _ _ _ _ _ (mset_local_update sent0 sent (mset_singleton v)) $$ HsentI Hprod
      with ⟨HsentI, Hprod⟩
    imod Hmask with -
    imod Hclose $$ [Hoc HsentI HrecvI Hclosed Hm HP] with -
    · inext
      iapply mpmc_inv_intro γ n_prod n_cons P R (.Buffered (buff ++ [v])) (sent0 • mset_singleton v)
        recv ⟨by subst Hrel; simp [inflight_mset]; ac_rfl, Hncons, Hnprod⟩
        $$ Hoc HsentI HrecvI [Hclosed] [Hm HP]
      · simp only [mpmc_closed_part]; iexact Hclosed
      · simp only [mpmc_inv_match]
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
    unfold mpmc_producer
    imod update_client _ _ _ _ _ _ (mset_local_update sent0 sent (mset_singleton v)) $$ HsentI Hprod
      with ⟨HsentI, Hprod⟩
    imod Hmask with -
    imod Hclose $$ [Hoc HsentI HrecvI Hclosed HP] with -
    · inext
      iapply mpmc_inv_intro γ n_prod n_cons P R (.SndPending v) (sent0 • mset_singleton v)
        recv ⟨by subst Hrel; simp [inflight_mset], Hncons, Hnprod⟩
        $$ Hoc HsentI HrecvI [Hclosed] [HP]
      · simp only [mpmc_closed_part]; iexact Hclosed
      · simp only [mpmc_inv_match]; iexact HP
    imodintro
    unfold send_nested_au
    iinv Hinv with Hi Hclose
    imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc2 Hi with Hi
    icases mpmc_inv_elim _ _ _ _ _ $$ Hi with
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
        iapply mpmc_inv_intro γ n_prod n_cons P R .Idle sent1 recv1
          ⟨by simpa [inflight_mset] using Hrel, Hncons, Hnprod⟩ $$ Hoc HsentI HrecvI [Hclosed] []
        · simp only [mpmc_closed_part]; iexact Hclosed
        · simp only [mpmc_inv_match]; itrivial
      imodintro
      iapply Hcont
      iexact Hprod
    | Closed d =>
      dsimp only
      iapply mpmc_closed_no_producer γ n_prod n_cons P R sent1 recv1 d _ $$ [$HsentI $Hm Hprod]
      unfold mpmc_producer
      iexact Hprod
    | _ => itrivial
  | RcvPending =>
    dsimp only
    iintro Hoc
    unfold mpmc_producer
    imod update_client _ _ _ _ _ _ (mset_local_update sent0 sent (mset_singleton v)) $$ HsentI Hprod
      with ⟨HsentI, Hprod⟩
    imod Hmask with -
    imod Hclose $$ [Hoc HsentI HrecvI Hclosed HP] with -
    · inext
      iapply mpmc_inv_intro γ n_prod n_cons P R (.SndCommit v) (sent0 • mset_singleton v)
        recv ⟨by subst Hrel; simp [inflight_mset], Hncons, Hnprod⟩
        $$ Hoc HsentI HrecvI [Hclosed] [HP]
      · simp only [mpmc_closed_part]; iexact Hclosed
      · simp only [mpmc_inv_match]; iexact HP
    imodintro
    iapply Hcont
    iexact Hprod
  | Closed d =>
    dsimp only
    iapply mpmc_closed_no_producer γ n_prod n_cons P R sent0 recv d sent $$ [$HsentI $Hm $Hprod]
  | _ => itrivial

theorem wp_mpmc_send (γ : mpmc_names) (ch : loc) (n_prod n_cons : Nat) (P : V → IProp GF)
    (R : mset → IProp GF) (sent : mset) (v : V) :
    {{ is_mpmc γ ch n_prod n_cons P R ∗ mpmc_producer γ sent ∗ P v }}
      (App (App (Val (chan.send t)) (Val #ch)) (Val #v))
    {{ RET #(); mpmc_producer γ (sent • mset_singleton v) }} := by
  iintro %Φ ⟨#Hmpmc, Hprod, HP⟩ HΦ
  ihave #Hch : is_chan ch γ.mpmc_chan_name V $$ [Hmpmc]
  · unfold is_mpmc; icases Hmpmc with ⟨$, -⟩
  iapply chan.wp_send ch v γ.mpmc_chan_name $$ Hch
  iintro ⟨Hlc1, Hlc2, _, _⟩
  iapply mpmc_send_au γ ch n_prod n_cons P R sent v (Φ #()) $$ Hmpmc [$Hlc1 $Hlc2] [$Hprod $HP] HΦ

omit [IntoValTyped (GF := GF) V t] in
set_option maxHeartbeats 800000 in
theorem mpmc_rcv_au (γ : mpmc_names) (ch : loc) (n_prod n_cons : Nat) (P : V → IProp GF)
    (R : mset → IProp GF) (received : mset) (Φ : V → Bool → IProp GF) :
    ⊢ is_mpmc γ ch n_prod n_cons P R -∗ £ 1 ∗ £ 1 -∗ mpmc_consumer γ received -∗
      ▷ (∀ (v : V) (ok : Bool),
        (if ok then iprop(P v ∗ mpmc_consumer γ (received • mset_singleton v))
         else iprop(is_closed γ ∗ mpmc_consumer γ received ∗ ⌜v = zero_val V⌝)) -∗ Φ v ok) -∗
      recv_au γ.mpmc_chan_name V Φ := by
  unfold is_mpmc recv_au
  iintro ⟨#Hchan, #Hinv⟩ ⟨Hlc1, Hlc2⟩ Hcons Hcont
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc1 Hi with Hi
  icases mpmc_inv_elim _ _ _ _ _ $$ Hi with ⟨%s, %sent, %recv, Hch, HsentI, HrecvI, %Hpure, Hclosed, Hm⟩
  obtain ⟨Hrel, Hncons, Hnprod⟩ := Hpure
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists s
  iframe Hch
  unfold mpmc_consumer
  cases s with
  | Buffered b =>
    cases b with
    | nil => itrivial
    | cons v rest =>
      dsimp only
      iintro Hoc
      imod update_client _ _ _ _ _ _ (mset_local_update recv received (mset_singleton v))
        $$ HrecvI Hcons with ⟨HrecvI, Hcons⟩
      simp only [mpmc_inv_match]
      icases BigSepL.bigSepL_cons.1 $$ Hm with ⟨HPv, Hrest⟩
      imod Hmask with -
      imod Hclose $$ [Hoc HsentI HrecvI Hclosed Hrest] with -
      · inext
        iapply mpmc_inv_intro γ n_prod n_cons P R (.Buffered rest) sent (recv • mset_singleton v)
          ⟨by subst Hrel; simp [inflight_mset]; ac_rfl, Hncons, Hnprod⟩
          $$ Hoc HsentI HrecvI [Hclosed] [Hrest]
        · simp only [mpmc_closed_part]; iexact Hclosed
        · simp only [mpmc_inv_match]; iexact Hrest
      imodintro
      iapply Hcont
      simp only [↓reduceIte, mpmc_consumer]
      iframe
  | Idle =>
    dsimp only
    iintro Hoc
    imod Hmask with -
    imod Hclose $$ [Hoc HsentI HrecvI Hclosed] with -
    · inext
      iapply mpmc_inv_intro γ n_prod n_cons P R .RcvPending sent recv
        ⟨by simpa [inflight_mset] using Hrel, Hncons, Hnprod⟩ $$ Hoc HsentI HrecvI [Hclosed] []
      · simp only [mpmc_closed_part]; iexact Hclosed
      · simp only [mpmc_inv_match]; itrivial
    imodintro
    unfold recv_nested_au
    iinv Hinv with Hi Hclose
    imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc2 Hi with Hi
    icases mpmc_inv_elim _ _ _ _ _ $$ Hi with
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
      imod update_client _ _ _ _ _ _ (mset_local_update recv received (mset_singleton v))
        $$ HrecvI Hcons with ⟨HrecvI, Hcons⟩
      simp only [mpmc_inv_match]
      imod Hmask with -
      imod Hclose $$ [Hoc HsentI HrecvI Hclosed] with -
      · inext
        iapply mpmc_inv_intro γ n_prod n_cons P R .Idle sent (recv • mset_singleton v)
          ⟨by simpa [inflight_mset] using Hrel, Hncons, Hnprod⟩ $$ Hoc HsentI HrecvI [Hclosed] []
        · simp only [mpmc_closed_part]; iexact Hclosed
        · simp only [mpmc_inv_match]; itrivial
      imodintro
      iapply Hcont
      simp only [↓reduceIte, mpmc_consumer]
      iframe
    | Closed d =>
      cases d with
      | nil =>
        dsimp only
        iintro Hoc
        imod Hmask with -
        simp only [mpmc_closed_part]
        icases Hclosed with #Hclosed
        simp only [mpmc_inv_match]
        icases Hm with ⟨%Hsr, Hprods, (HR | ⟨%conss, %Hlen, Hconss⟩)⟩
        · imod Hclose $$ [Hoc HsentI HrecvI Hprods HR] with -
          · inext
            iapply mpmc_inv_intro γ n_prod n_cons P R (.Closed []) sent recv ⟨by simpa using Hrel, Hncons, Hnprod⟩
              $$ Hoc HsentI HrecvI [] [Hprods HR]
            · simp only [mpmc_closed_part]; iexact Hclosed
            · simp only [mpmc_inv_match]
              isplitr
              · ipureintro; exact Hsr
              isplitl [Hprods]
              · iexact Hprods
              · ileft; iexact HR
          imodintro
          iapply Hcont
          simp only [Bool.false_eq_true, ↓reduceIte]
          unfold is_closed
          iframe
          iframe #
        · iexfalso
          subst Hlen
          simp only [mpmc_consumer]
          iapply clients_extra_false _ _ conss received $$ [$HrecvI $Hconss $Hcons]
      | cons _ _ => itrivial
    | _ => itrivial
  | SndPending v =>
    dsimp only
    iintro Hoc
    imod update_client _ _ _ _ _ _ (mset_local_update recv received (mset_singleton v))
      $$ HrecvI Hcons with ⟨HrecvI, Hcons⟩
    simp only [mpmc_inv_match]
    imod Hmask with -
    imod Hclose $$ [Hoc HsentI HrecvI Hclosed] with -
    · inext
      iapply mpmc_inv_intro γ n_prod n_cons P R .RcvCommit sent (recv • mset_singleton v)
        ⟨by simpa [inflight_mset] using Hrel, Hncons, Hnprod⟩ $$ Hoc HsentI HrecvI [Hclosed] []
      · simp only [mpmc_closed_part]; iexact Hclosed
      · simp only [mpmc_inv_match]; itrivial
    imodintro
    iapply Hcont
    simp only [↓reduceIte, mpmc_consumer]
    iframe
  | Closed d =>
    cases d with
    | nil =>
      dsimp only
      iintro Hoc
      imod Hmask with -
      simp only [mpmc_closed_part]
      icases Hclosed with #Hclosed
      simp only [mpmc_inv_match]
      icases Hm with ⟨%Hsr, Hprods, (HR | ⟨%conss, %Hlen, Hconss⟩)⟩
      · imod Hclose $$ [Hoc HsentI HrecvI Hprods HR] with -
        · inext
          iapply mpmc_inv_intro γ n_prod n_cons P R (.Closed []) sent recv ⟨by simpa using Hrel, Hncons, Hnprod⟩
            $$ Hoc HsentI HrecvI [] [Hprods HR]
          · simp only [mpmc_closed_part]; iexact Hclosed
          · simp only [mpmc_inv_match]
            isplitr
            · ipureintro; exact Hsr
            isplitl [Hprods]
            · iexact Hprods
            · ileft; iexact HR
        imodintro
        iapply Hcont
        simp only [Bool.false_eq_true, ↓reduceIte]
        unfold is_closed
        iframe
        iframe #
      · iexfalso
        subst Hlen
        simp only [mpmc_consumer]
        iapply clients_extra_false _ _ conss received $$ [$HrecvI $Hconss $Hcons]
    | cons v rest =>
      dsimp only
      iintro Hoc
      imod update_client _ _ _ _ _ _ (mset_local_update recv received (mset_singleton v))
        $$ HrecvI Hcons with ⟨HrecvI, Hcons⟩
      imod Hmask with -
      simp only [mpmc_inv_match]
      icases Hm with ⟨Hbig, Hmp, HR⟩
      icases BigSepL.bigSepL_cons.1 $$ Hbig with ⟨HPv, Hrest⟩
      cases rest with
      | nil =>
        simp only [mpmc_closed_part]
        imod dghost_var_update true _ _ $$ Hclosed with Hclosed
        imod dghost_var_persist _ _ _ $$ Hclosed with #Hclosed
        imod Hclose $$ [Hoc HsentI HrecvI Hmp HR] with -
        · inext
          iapply mpmc_inv_intro γ n_prod n_cons P R (.Closed []) sent (recv • mset_singleton v)
            ⟨by subst Hrel; simp [inflight_mset], Hncons, Hnprod⟩ $$ Hoc HsentI HrecvI [] [Hmp HR]
          · simp only [mpmc_closed_part]; iexact Hclosed
          · simp only [mpmc_inv_match]
            isplitr
            · ipureintro; subst Hrel; simp [inflight_mset]
            isplitl [Hmp]
            · iexact Hmp
            · ileft; iexact HR
        imodintro
        iapply Hcont
        simp only [↓reduceIte, mpmc_consumer]
        iframe
      | cons w ws =>
        imod Hclose $$ [Hoc HsentI HrecvI Hclosed Hrest Hmp HR] with -
        · inext
          iapply mpmc_inv_intro γ n_prod n_cons P R (.Closed (w :: ws)) sent (recv • mset_singleton v)
            ⟨by subst Hrel; simp [inflight_mset]; ac_rfl, Hncons, Hnprod⟩
            $$ Hoc HsentI HrecvI [Hclosed] [Hrest Hmp HR]
          · simp only [mpmc_closed_part]; iexact Hclosed
          · simp only [mpmc_inv_match]
            isplitl [Hrest]
            · iexact Hrest
            isplitl [Hmp]
            · iexact Hmp
            · iexact HR
        imodintro
        iapply Hcont
        simp only [↓reduceIte, mpmc_consumer]
        iframe
  | _ => itrivial

theorem wp_mpmc_receive (γ : mpmc_names) (ch : loc) (n_prod n_cons : Nat) (P : V → IProp GF)
    (R : mset → IProp GF) (received : mset) :
    {{ is_mpmc γ ch n_prod n_cons P R ∗ mpmc_consumer γ received }}
      (App (Val (chan.receive t)) (Val #ch))
    {{ (v : V) (ok : Bool), RET (PairV #v #ok);
        (if ok then iprop(P v ∗ mpmc_consumer γ (received • mset_singleton v))
         else iprop(is_closed γ ∗ mpmc_consumer γ received ∗ ⌜v = zero_val V⌝)) }} := by
  iintro %Φ ⟨#Hmpmc, Hcons⟩ HΦ
  ihave #Hch : is_chan ch γ.mpmc_chan_name V $$ [Hmpmc]
  · unfold is_mpmc; icases Hmpmc with ⟨$, -⟩
  iapply chan.wp_receive ch γ.mpmc_chan_name $$ Hch
  iintro ⟨Hlc1, Hlc2, _, _⟩
  iapply mpmc_rcv_au γ ch n_prod n_cons P R received (fun v ok => Φ (PairV #v #ok))
    $$ Hmpmc [$Hlc1 $Hlc2] Hcons
  inext
  iintro %v %ok H
  iapply HΦ $$ %v %ok H

omit [IntoValTyped (GF := GF) V t] in
set_option maxHeartbeats 800000 in
theorem mpmc_close_au (γ : mpmc_names) (ch : loc) (n_prod n_cons : Nat) (P : V → IProp GF)
    (R : mset → IProp GF) (producers : List mset) (Φ : IProp GF) (hlen : producers.length = n_prod) :
    ⊢ is_mpmc γ ch n_prod n_cons P R -∗ £ 1 -∗
      ([∗list] s_i ∈ producers, mpmc_producer γ s_i) ∗ R (mset_sum producers) -∗
      ▷ Φ -∗ close_au γ.mpmc_chan_name V Φ := by
  subst hlen
  unfold is_mpmc close_au
  iintro ⟨#Hchan, #Hinv⟩ Hlc1 ⟨Hprods, HR⟩ Hcont
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc1 Hi with Hi
  icases mpmc_inv_elim _ _ _ _ _ $$ Hi with ⟨%s, %sent, %recv, Hch, HsentI, HrecvI, %Hpure, Hclosed, Hm⟩
  obtain ⟨Hrel, Hncons, Hnprod⟩ := Hpure
  simp only [mpmc_producer]
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
      simp only [mpmc_closed_part]
      imod dghost_var_update true _ _ $$ Hclosed with Hclosed
      imod dghost_var_persist _ _ _ $$ Hclosed with #Hclosed
      imod Hclose $$ [Hoc HsentI HrecvI Hprods HR] with -
      · inext
        iapply mpmc_inv_intro γ producers.length n_cons P R (.Closed []) (mset_sum producers) recv
          ⟨by simpa [inflight_mset] using Hrel, Hncons, Hnprod⟩ $$ Hoc HsentI HrecvI [] [Hprods HR]
        · simp only [mpmc_closed_part]; iexact Hclosed
        · simp only [mpmc_inv_match, mpmc_producer]
          isplitr
          · ipureintro; simpa [inflight_mset] using Hrel
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
        iapply mpmc_inv_intro γ producers.length n_cons P R (.Closed (w :: ws)) (mset_sum producers)
          recv ⟨by simpa [inflight_mset] using Hrel, Hncons, Hnprod⟩
          $$ Hoc HsentI HrecvI [Hclosed] [Hm Hprods HR]
        · simp only [mpmc_closed_part]; iexact Hclosed
        · simp only [mpmc_inv_match, mpmc_producer]
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
    simp only [mpmc_closed_part]
    imod dghost_var_update true _ _ $$ Hclosed with Hclosed
    imod dghost_var_persist _ _ _ $$ Hclosed with #Hclosed
    imod Hclose $$ [Hoc HsentI HrecvI Hprods HR] with -
    · inext
      iapply mpmc_inv_intro γ producers.length n_cons P R (.Closed []) (mset_sum producers) recv
        ⟨by simpa [inflight_mset] using Hrel, Hncons, Hnprod⟩ $$ Hoc HsentI HrecvI [] [Hprods HR]
      · simp only [mpmc_closed_part]; iexact Hclosed
      · simp only [mpmc_inv_match, mpmc_producer]
        isplitr
        · ipureintro; simpa [inflight_mset] using Hrel
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
      simp only [mpmc_producer]
      iexact Hp
  | _ => itrivial

theorem wp_mpmc_close (γ : mpmc_names) (ch : loc) (n_prod n_cons : Nat) (P : V → IProp GF)
    (R : mset → IProp GF) (producers : List mset) {ct : go.type} {dir : go.chan_dir}
    [ct ↓u go.ChannelType dir t] (hlen : producers.length = n_prod) :
    {{ is_mpmc γ ch n_prod n_cons P R ∗ ([∗list] s_i ∈ producers, mpmc_producer γ s_i) ∗
        R (mset_sum producers) }}
      (App (Val #(functions go.close [ct])) (Val #ch))
    {{ RET #(); True }} := by
  iintro %Φ ⟨#Hmpmc, Hprods, HR⟩ HΦ
  ihave #Hch : is_chan ch γ.mpmc_chan_name V $$ [Hmpmc]
  · unfold is_mpmc; icases Hmpmc with ⟨$, -⟩
  iapply chan.wp_close (ct := ct) ch γ.mpmc_chan_name $$ Hch
  iintro ⟨Hlc1, _, _, _⟩
  iapply mpmc_close_au γ ch n_prod n_cons P R producers (Φ #()) hlen $$ Hmpmc Hlc1 [$Hprods $HR]
  inext
  iapply HΦ
  itrivial

omit [IntoValTyped (GF := GF) V t] in
set_option maxHeartbeats 400000 in
theorem mpmc_get_final_resource (γ : mpmc_names) (ch : loc) (n_prod n_cons : Nat)
    (P : V → IProp GF) (R : mset → IProp GF) (consumers : List mset)
    (hlen : consumers.length = n_cons) :
    ⊢ £ 1 -∗ is_mpmc γ ch n_prod n_cons P R -∗ is_closed γ -∗
      ([∗list] r_i ∈ consumers, mpmc_consumer γ r_i) ={⊤}=∗ R (mset_sum consumers) := by
  subst hlen
  unfold is_mpmc
  iintro Hlc ⟨#Hchan, #Hinv⟩ #Hcl Hcons
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc Hi with Hi
  icases mpmc_inv_elim _ _ _ _ _ $$ Hi with ⟨%s, %sent, %recv, Hch, HsentI, HrecvI, %Hpure, Hclosed, Hm⟩
  obtain ⟨Hrel, Hncons, Hnprod⟩ := Hpure
  unfold is_closed
  have hs : s = .Closed [] ∨ mpmc_closed_part (GF := GF) γ s =
      dghost_var γ.mpmc_closed_name (DFrac.own 1) false := by
    rcases s with _ | _ | _ | _ | _ | _ | (_ | ⟨_, _⟩) <;> simp [mpmc_closed_part]
  rcases hs with rfl | hs
  · simp only [mpmc_inv_match, mpmc_consumer]
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
        iapply mpmc_inv_intro γ n_prod consumers.length P R (.Closed []) (mset_sum consumers)
          (mset_sum consumers) ⟨Hrel, Hncons, Hnprod⟩ $$ Hch HsentI HrecvI Hclosed [Hprods Hcons]
        simp only [mpmc_inv_match, mpmc_consumer]
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
    ihave %Hbad := dghost_var_agree _ _ _ _ _ $$ Hcl Hclosed
    cases Hbad

end mpmc

end Perennial
