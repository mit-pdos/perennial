/-
Port of `new/golang/theory/chan/idioms/spsc.v`: single-producer single-consumer (SPSC)
channels, with histories of sent and received values.

* Producer maintains exclusive send permission with history tracking.
* Consumer maintains exclusive receive permission with history tracking.
* Ghost state tracks sent/received histories with fractional permissions.
* The invariant maintains `sent = received ++ in_flight`.
* Resource protocols `P` (per-value, indexed by position) and `R` (final state).

Lean notes: the per-state part of the invariant is the separate definition
`spsc_inv_match`; `[Pos.Countable V]` as in `ChanAuBase.lean`.
-/
import Perennial.Golang.Theory.Chan.Idioms.Base
import Perennial.Golang.Theory.Chan

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

/-- Ghost state names of an SPSC channel. -/
structure spsc_names where
  /-- Underlying channel ghost state -/
  chan_name : chan_names
  /-- History of sent values -/
  spsc_sent_name : GName
  /-- History of received values -/
  spsc_recv_name : GName

section spsc
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : heapGS HasLC.hasLC GF] [allG GF]
variable [sem : go.Semantics]
variable {V : Type} [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V] {t : go.type}
  [IntoValTyped (GF := GF) V t]

/-- Producer maintains (1/2) permission of sent history. -/
def spsc_producer (γ : spsc_names) (sent : List V) : IProp GF :=
  dghost_var γ.spsc_sent_name (DFrac.own (1 : Qp).half) sent

/-- Consumer maintains (1/2) permission of received history. -/
def spsc_consumer (γ : spsc_names) (received : List V) : IProp GF :=
  dghost_var γ.spsc_recv_name (DFrac.own (1 : Qp).half) received

/-- Values that have been sent but not yet received. -/
def inflight (s : chanstate.t V) : List V :=
  match s with
  | .Buffered buff => buff
  | .SndPending v | .SndCommit v => [v]
  | .Closed drain => drain
  | _ => []

/-- The state-dependent part of the SPSC invariant. -/
def spsc_inv_match (γ : spsc_names) (P : Int → V → IProp GF) (R : List V → IProp GF)
    (sent recv : List V) (s : chanstate.t V) : IProp GF :=
  match s with
  -- P holds for all buffered values
  | .Buffered buff => iprop([∗list] i ↦ v ∈ buff, P ((recv.length : Int) + i) v)
  -- P holds for pending/committed values
  | .SndPending v | .SndCommit v => P recv.length v
  -- Closed channel: park producer permission, provide R when drained
  | .Closed [] => iprop(spsc_producer γ sent ∗ (R sent ∨ spsc_consumer γ sent))
  | .Closed drain =>
      iprop(([∗list] i ↦ v ∈ drain, P ((recv.length : Int) + i) v) ∗
        spsc_producer γ sent ∗ (R sent ∨ spsc_consumer γ sent))
  | _ => iprop(True)

@[irreducible] def spsc_inv (γ : spsc_names) (P : Int → V → IProp GF) (R : List V → IProp GF) : IProp GF :=
  iprop(∃ (s : chanstate.t V) (sent recv : List V),
    "Hch" ∷ own_chan γ.chan_name V s ∗
    "HsentI" ∷ dghost_var γ.spsc_sent_name (DFrac.own (1 : Qp).half) sent ∗
    "HrecvI" ∷ dghost_var γ.spsc_recv_name (DFrac.own (1 : Qp).half) recv ∗
    "%Hrel" ∷ ⌜sent = recv ++ inflight s⌝ ∗
    "Hm" ∷ spsc_inv_match γ P R sent recv s)

/-- The main SPSC channel predicate.

* `P`: resource associated with each value (maintained while in-flight);
* `R`: final resource when channel is closed and drained.

The invariant maintains `sent = received + inflight(channel_state)`, `P` for all
in-flight values; when closed, the producer permission is parked to prevent further
sends, and when closed and drained, the consumer gets `R`. -/
def is_spsc (γ : spsc_names) (ch : loc) (P : Int → V → IProp GF) (R : List V → IProp GF) :
    IProp GF :=
  iprop(is_chan ch γ.chan_name V ∗ inv nroot (spsc_inv γ P R))

instance is_spsc_persistent (γ : spsc_names) (ch : loc) (P : Int → V → IProp GF)
    (R : List V → IProp GF) : Persistent (is_spsc γ ch P R) := by
  unfold is_spsc; infer_instance

omit [ZeroVal V] [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V t] in
theorem dghost_var_halves {A : Type} [Pos.Countable A] (γ : GName) (a : A) :
    dghost_var (GF := GF) γ (DFrac.own 1) a ⊢
      dghost_var γ (DFrac.own (1 : Qp).half) a ∗ dghost_var γ (DFrac.own (1 : Qp).half) a := by
  have h := dghost_var_split (GF := GF) γ a (DFrac.own (1 : Qp).half) (DFrac.own (1 : Qp).half)
  rw [DFrac.op_own, Qp.half_add_half] at h
  exact wand_entails h

omit [ZeroVal V] [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V t] in
/-- Three halves of a `dghost_var` are contradictory. -/
theorem dghost_var_three_halves {A : Type} [Pos.Countable A] (γ : GName) (a b c : A) :
    ⊢ dghost_var (GF := GF) γ (DFrac.own (1 : Qp).half) a -∗
      dghost_var γ (DFrac.own (1 : Qp).half) b -∗
      dghost_var γ (DFrac.own (1 : Qp).half) c -∗ False := by
  iintro H1 H2 H3
  icombine H1 H2 gives %Hab
  obtain ⟨_, rfl⟩ := Hab
  icombine H1 H2 as H12
  icombine H12 H3 gives %Hbad
  exfalso
  obtain ⟨Hbad, _⟩ := Hbad
  revert Hbad
  simp only [CMRA.Valid, DFrac.op_own]
  intro h
  have : (1 : Rat) + 1 / 2 ≤ 1 := h
  grind

omit [ZeroVal V] [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V t] in
/-- Popping the first in-flight value off the indexed big star. -/
theorem spsc_pop (P : Int → V → IProp GF) (recv : List V) (v : V) (rest : List V) :
    ([∗list] i ↦ x ∈ v :: rest, P ((recv.length : Int) + i) x) ⊣⊢
      P recv.length v ∗ [∗list] i ↦ x ∈ rest, P (((recv ++ [v]).length : Int) + i) x := by
  refine BigSepL.bigSepL_cons.trans (BiEntails.of_eq ?_)
  have h : ∀ k : Nat, ((recv.length : Int) + ((k + 1 : Nat) : Int)) =
      ((recv ++ [v]).length : Int) + (k : Int) := by intro k; simp; omega
  simp only [h]
  rw [show ((recv.length : Int) + ((0 : Nat) : Int)) = recv.length by omega]

omit [ZeroVal V] [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V t] in
/-- Pushing a new in-flight value onto the indexed big star. -/
theorem spsc_push (P : Int → V → IProp GF) (recv buff : List V) (v : V) :
    ([∗list] i ↦ x ∈ buff, P ((recv.length : Int) + i) x) ∗ P (recv ++ buff).length v ⊢
      [∗list] i ↦ x ∈ buff ++ [v], P ((recv.length : Int) + i) x := by
  refine (BiEntails.of_eq ?_).1.trans BigSepL.bigSepL_snoc.2
  simp only [List.length_append]
  rw [show (((recv.length + buff.length : Nat)) : Int) = recv.length + buff.length by omega]

omit [IntoValTyped (GF := GF) V t] in
/-- Create an SPSC channel from a basic channel. -/
theorem start_spsc (ch : loc) (P : Int → V → IProp GF) (R : List V → IProp GF) (γ : chan_names) :
    ⊢ is_chan ch γ V -∗ (own_chan γ V .Idle ∨ own_chan γ V (.Buffered [])) ={⊤}=∗
      ∃ γspsc, is_spsc γspsc ch P R ∗ spsc_producer γspsc ([] : List V) ∗
        spsc_consumer γspsc ([] : List V) := by
  iintro #Hch Hoc
  imod dghost_var_alloc ([] : List V) with ⟨%γsent, Hsent⟩
  icases dghost_var_halves _ _ $$ Hsent with ⟨HsentA, HsentF⟩
  imod dghost_var_alloc ([] : List V) with ⟨%γrecv, Hrecv⟩
  icases dghost_var_halves _ _ $$ Hrecv with ⟨HrecvA, HrecvF⟩
  iexists ⟨γ, γsent, γrecv⟩
  unfold is_spsc spsc_producer spsc_consumer
  imod inv_alloc nroot ⊤ (spsc_inv ⟨γ, γsent, γrecv⟩ P R) $$ [Hoc HsentA HrecvA] with #Hinv
  · inext
    unfold spsc_inv
    icases Hoc with (Hoc | Hoc)
    · iexists .Idle, [], []
      simp only [spsc_inv_match, inflight, List.append_nil]
      iframe
      isplit <;> itrivial
    · iexists .Buffered [], [], []
      simp only [spsc_inv_match, inflight, List.append_nil]
      iframe
      isplitr
      · itrivial
      · iapply BigSepL.bigSepL_nil.2
        iempintro
  imodintro
  iframe
  iframe #

omit [IntoValTyped (GF := GF) V t] in
theorem spsc_inv_intro (γ : spsc_names) (P : Int → V → IProp GF) (R : List V → IProp GF)
    (s : chanstate.t V) (sent recv : List V) (h : sent = recv ++ inflight s) :
    ⊢ own_chan γ.chan_name V s -∗
      dghost_var γ.spsc_sent_name (DFrac.own (1 : Qp).half) sent -∗
      dghost_var γ.spsc_recv_name (DFrac.own (1 : Qp).half) recv -∗
      spsc_inv_match γ P R sent recv s -∗ spsc_inv γ P R := by
  iintro H1 H2 H3 H4
  unfold spsc_inv
  iexists s, sent, recv
  isplitl [H1]; · iexact H1
  isplitl [H2]; · iexact H2
  isplitl [H3]; · iexact H3
  isplitr
  · ipureintro; exact h
  · iexact H4

omit [IntoValTyped (GF := GF) V t] in
theorem spsc_inv_elim (γ : spsc_names) (P : Int → V → IProp GF) (R : List V → IProp GF) :
    spsc_inv γ P R ⊢ ∃ (s : chanstate.t V) (sent recv : List V),
      own_chan γ.chan_name V s ∗
      dghost_var γ.spsc_sent_name (DFrac.own (1 : Qp).half) sent ∗
      dghost_var γ.spsc_recv_name (DFrac.own (1 : Qp).half) recv ∗
      ⌜sent = recv ++ inflight s⌝ ∗ spsc_inv_match γ P R sent recv s := by
  unfold spsc_inv; exact .rfl

omit [IntoValTyped (GF := GF) V t] in
set_option maxHeartbeats 400000 in
theorem spsc_rcv_au (γ : spsc_names) (ch : loc) (P : Int → V → IProp GF) (R : List V → IProp GF)
    (received : List V) (Φ : V → Bool → IProp GF) :
    ⊢ is_spsc γ ch P R -∗ £ 1 ∗ £ 1 -∗ spsc_consumer γ received -∗
      ▷ (∀ (v : V) (ok : Bool),
          (if ok then iprop(P received.length v ∗ spsc_consumer γ (received ++ [v]))
           else iprop(R received ∗ ⌜v = zero_val V⌝)) -∗ Φ v ok) -∗
      recv_au γ.chan_name V Φ := by
  unfold is_spsc recv_au
  iintro ⟨#Hchan, #Hinv⟩ ⟨Hlc1, Hlc2⟩ Hcons Hcont
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc1 Hi with Hi
  icases spsc_inv_elim _ _ _ $$ Hi with ⟨%s, %sent, %recv, Hch, HsentI, HrecvI, %Hrel, Hm⟩
  unfold spsc_consumer
  ihave %Heq := dghost_var_agree _ _ _ _ _ $$ Hcons HrecvI
  subst Heq
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists s
  iframe Hch
  cases s with
  | Buffered b =>
    cases b with
    | nil => itrivial
    | cons v rest =>
      dsimp only
      iintro Hoc
      imod dghost_var_update_halves (received ++ [v]) _ _ _ $$ Hcons HrecvI with ⟨Hcons, HrecvI⟩
      simp only [spsc_inv_match]
      icases (spsc_pop P received v rest).1 $$ Hm with ⟨HPv, Hrest⟩
      imod Hmask with -
      imod Hclose $$ [Hoc HsentI HrecvI Hrest] with -
      · inext
        iapply spsc_inv_intro γ P R (.Buffered rest) sent (received ++ [v]) (by simp [Hrel, inflight])
          $$ Hoc HsentI HrecvI
        simp only [spsc_inv_match]
        iexact Hrest
      imodintro
      iapply Hcont
      simp only [↓reduceIte]
      iframe
  | Idle =>
    dsimp only
    iintro Hoc
    imod Hmask with -
    imod Hclose $$ [Hoc HsentI HrecvI] with -
    · inext
      iapply spsc_inv_intro γ P R .RcvPending sent received (by simpa [inflight] using Hrel)
        $$ Hoc HsentI HrecvI
      simp only [spsc_inv_match]
      itrivial
    imodintro
    unfold recv_nested_au
    iinv Hinv with Hi Hclose
    imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc2 Hi with Hi
    icases spsc_inv_elim _ _ _ $$ Hi with ⟨%s, %sent, %recv, Hch, HsentI, HrecvI, %Hrel, Hm⟩
    ihave %Heq := dghost_var_agree _ _ _ _ _ $$ Hcons HrecvI
    subst Heq
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iexists s
    iframe Hch
    cases s with
    | SndCommit v =>
      dsimp only
      iintro Hoc
      imod dghost_var_update_halves (received ++ [v]) _ _ _ $$ Hcons HrecvI with ⟨Hcons, HrecvI⟩
      simp only [spsc_inv_match]
      imod Hmask with -
      imod Hclose $$ [Hoc HsentI HrecvI] with -
      · inext
        iapply spsc_inv_intro γ P R .Idle sent (received ++ [v]) (by simpa [inflight] using Hrel)
          $$ Hoc HsentI HrecvI
        simp only [spsc_inv_match]
        itrivial
      imodintro
      iapply Hcont
      simp only [↓reduceIte]
      iframe
    | Closed d =>
      cases d with
      | nil =>
        dsimp only
        simp only [inflight, List.append_nil] at Hrel
        subst Hrel
        simp only [spsc_inv_match, spsc_consumer]
        icases Hm with ⟨Hprod, (HR | Hc2)⟩
        · iintro Hoc
          imod Hmask with -
          imod Hclose $$ [Hoc HsentI HrecvI Hprod Hcons] with -
          · inext
            iapply spsc_inv_intro γ P R (.Closed []) sent sent (by simp [inflight])
              $$ Hoc HsentI HrecvI
            simp only [spsc_inv_match, spsc_consumer]
            isplitl [Hprod]
            · iexact Hprod
            · iright; iexact Hcons
          imodintro
          iapply Hcont
          simp only [Bool.false_eq_true, ↓reduceIte]
          iframe
        · iexfalso
          iapply dghost_var_three_halves $$ Hcons HrecvI Hc2
      | cons _ _ => itrivial
    | _ => itrivial
  | SndPending v =>
    dsimp only
    iintro Hoc
    imod dghost_var_update_halves (received ++ [v]) _ _ _ $$ Hcons HrecvI with ⟨Hcons, HrecvI⟩
    simp only [spsc_inv_match]
    imod Hmask with -
    imod Hclose $$ [Hoc HsentI HrecvI] with -
    · inext
      iapply spsc_inv_intro γ P R .RcvCommit sent (received ++ [v]) (by simpa [inflight] using Hrel)
        $$ Hoc HsentI HrecvI
      simp only [spsc_inv_match]
      itrivial
    imodintro
    iapply Hcont
    simp only [↓reduceIte]
    iframe
  | Closed d =>
    cases d with
    | nil =>
      dsimp only
      simp only [inflight, List.append_nil] at Hrel
      subst Hrel
      simp only [spsc_inv_match, spsc_consumer]
      icases Hm with ⟨Hprod, (HR | Hc2)⟩
      · iintro Hoc
        imod Hmask with -
        imod Hclose $$ [Hoc HsentI HrecvI Hprod Hcons] with -
        · inext
          iapply spsc_inv_intro γ P R (.Closed []) sent sent (by simp [inflight])
            $$ Hoc HsentI HrecvI
          simp only [spsc_inv_match, spsc_consumer]
          isplitl [Hprod]
          · iexact Hprod
          · iright; iexact Hcons
        imodintro
        iapply Hcont
        simp only [Bool.false_eq_true, ↓reduceIte]
        iframe
      · iexfalso
        iapply dghost_var_three_halves $$ Hcons HrecvI Hc2
    | cons v rest =>
      dsimp only
      iintro Hoc
      imod dghost_var_update_halves (received ++ [v]) _ _ _ $$ Hcons HrecvI with ⟨Hcons, HrecvI⟩
      simp only [spsc_inv_match]
      icases Hm with ⟨Hbig, Hprod, Hor⟩
      icases (spsc_pop P received v rest).1 $$ Hbig with ⟨HPv, Hrest⟩
      imod Hmask with -
      imod Hclose $$ [Hoc HsentI HrecvI Hrest Hprod Hor] with -
      · inext
        iapply spsc_inv_intro γ P R (.Closed rest) sent (received ++ [v]) (by simp [Hrel, inflight])
          $$ Hoc HsentI HrecvI
        cases rest with
        | nil =>
          simp only [spsc_inv_match]
          isplitl [Hprod]
          · iexact Hprod
          · iexact Hor
        | cons w ws =>
          simp only [spsc_inv_match]
          isplitl [Hrest]
          · iexact Hrest
          isplitl [Hprod]
          · iexact Hprod
          · iexact Hor
      imodintro
      iapply Hcont
      simp only [↓reduceIte]
      iframe
  | _ => itrivial

/-- SPSC receive operation with history tracking. -/
theorem wp_spsc_receive (γ : spsc_names) (ch : loc) (P : Int → V → IProp GF)
    (R : List V → IProp GF) (received : List V) :
    {{ is_spsc γ ch P R ∗ spsc_consumer γ received }}
      (App (Val (chan.receive t)) (Val #ch))
    {{ (v : V) (ok : Bool), RET (PairV #v #ok);
        (if ok then iprop(P received.length v ∗ spsc_consumer γ (received ++ [v]))
         else iprop(R received ∗ ⌜v = zero_val V⌝)) }} := by
  iintro %Φ ⟨#Hspsc, Hcons⟩ HΦ
  ihave #Hch : is_chan ch γ.chan_name V $$ [Hspsc]
  · unfold is_spsc; icases Hspsc with ⟨$, -⟩
  iapply chan.wp_receive ch γ.chan_name $$ Hch
  iintro ⟨Hlc1, Hlc2, _, _⟩
  iapply spsc_rcv_au γ ch P R received (fun v ok => Φ (PairV #v #ok)) $$ Hspsc [$Hlc1 $Hlc2] Hcons
  inext
  iintro %v %ok H
  iapply HΦ $$ %v %ok H

omit [IntoValTyped (GF := GF) V t] in
set_option maxHeartbeats 400000 in
theorem spsc_send_au (γ : spsc_names) (ch : loc) (P : Int → V → IProp GF) (R : List V → IProp GF)
    (sent : List V) (v : V) (Φ : IProp GF) :
    ⊢ is_spsc γ ch P R -∗ £ 1 ∗ £ 1 ∗ £ 1 -∗ spsc_producer γ sent ∗ P sent.length v -∗
      ▷ (spsc_producer γ (sent ++ [v]) -∗ Φ) -∗ send_au γ.chan_name v Φ := by
  unfold is_spsc send_au
  iintro ⟨#Hchan, #Hinv⟩ ⟨Hlc1, Hlc2, Hlc3⟩ ⟨Hprod, HP⟩ Hcont
  imod lc_fupd_elim_later (E := ⊤) $$ Hlc1 Hcont with Hcont
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc2 Hi with Hi
  icases spsc_inv_elim _ _ _ $$ Hi with ⟨%s, %sent0, %recv, Hch, HsentI, HrecvI, %Hrel, Hm⟩
  unfold spsc_producer
  ihave %Heq := dghost_var_agree _ _ _ _ _ $$ Hprod HsentI
  subst Heq
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists s
  iframe Hch
  cases s with
  | Buffered buff =>
    dsimp only
    simp only [inflight] at Hrel
    subst Hrel
    iintro Hoc
    imod dghost_var_update_halves ((recv ++ buff) ++ [v]) _ _ _ $$ Hprod HsentI with ⟨Hprod, HsentI⟩
    imod Hmask with -
    imod Hclose $$ [Hoc HsentI HrecvI Hm HP] with -
    · inext
      iapply spsc_inv_intro γ P R (.Buffered (buff ++ [v])) ((recv ++ buff) ++ [v]) recv
        (by simp [inflight]) $$ Hoc HsentI HrecvI
      simp only [spsc_inv_match]
      iapply spsc_push P recv buff v
      isplitl [Hm]
      · iexact Hm
      · iexact HP
    imodintro
    iapply Hcont $$ Hprod
  | Idle =>
    dsimp only
    simp only [inflight, List.append_nil] at Hrel
    subst Hrel
    iintro Hoc
    imod dghost_var_update_halves (sent ++ [v]) _ _ _ $$ Hprod HsentI with ⟨Hprod, HsentI⟩
    imod Hmask with -
    imod Hclose $$ [Hoc HsentI HrecvI HP] with -
    · inext
      iapply spsc_inv_intro γ P R (.SndPending v) (sent ++ [v]) sent (by simp [inflight])
        $$ Hoc HsentI HrecvI
      simp only [spsc_inv_match]
      iexact HP
    imodintro
    unfold send_nested_au
    iinv Hinv with Hi Hclose
    imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc3 Hi with Hi
    icases spsc_inv_elim _ _ _ $$ Hi with ⟨%s, %sent1, %recv1, Hch, HsentI, HrecvI, %Hrel, Hm⟩
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
      imod Hclose $$ [Hoc HsentI HrecvI] with -
      · inext
        iapply spsc_inv_intro γ P R .Idle sent1 recv1 (by simpa [inflight] using Hrel)
          $$ Hoc HsentI HrecvI
        simp only [spsc_inv_match]
        itrivial
      imodintro
      iapply Hcont $$ Hprod
    | Closed d =>
      dsimp only
      cases d with
      | nil =>
        simp only [spsc_inv_match, spsc_producer]
        icases Hm with ⟨Hp2, -⟩
        iapply dghost_var_three_halves $$ Hprod HsentI Hp2
      | cons _ _ =>
        simp only [spsc_inv_match, spsc_producer]
        icases Hm with ⟨-, Hp2, -⟩
        iapply dghost_var_three_halves $$ Hprod HsentI Hp2
    | _ => itrivial
  | RcvPending =>
    dsimp only
    simp only [inflight, List.append_nil] at Hrel
    subst Hrel
    iintro Hoc
    imod dghost_var_update_halves (sent ++ [v]) _ _ _ $$ Hprod HsentI with ⟨Hprod, HsentI⟩
    imod Hmask with -
    imod Hclose $$ [Hoc HsentI HrecvI HP] with -
    · inext
      iapply spsc_inv_intro γ P R (.SndCommit v) (sent ++ [v]) sent (by simp [inflight])
        $$ Hoc HsentI HrecvI
      simp only [spsc_inv_match]
      iexact HP
    imodintro
    iapply Hcont $$ Hprod
  | Closed d =>
    dsimp only
    cases d with
    | nil =>
      simp only [spsc_inv_match, spsc_producer]
      icases Hm with ⟨Hp2, -⟩
      iapply dghost_var_three_halves $$ Hprod HsentI Hp2
    | cons _ _ =>
      simp only [spsc_inv_match, spsc_producer]
      icases Hm with ⟨-, Hp2, -⟩
      iapply dghost_var_three_halves $$ Hprod HsentI Hp2
  | _ => itrivial

/-- SPSC send operation with history tracking. -/
theorem wp_spsc_send (γ : spsc_names) (ch : loc) (P : Int → V → IProp GF) (R : List V → IProp GF)
    (sent : List V) (v : V) :
    {{ is_spsc γ ch P R ∗ spsc_producer γ sent ∗ P sent.length v }}
      (App (App (Val (chan.send t)) (Val #ch)) (Val #v))
    {{ RET #(); spsc_producer γ (sent ++ [v]) }} := by
  iintro %Φ ⟨#Hspsc, Hprod, HP⟩ HΦ
  ihave #Hch : is_chan ch γ.chan_name V $$ [Hspsc]
  · unfold is_spsc; icases Hspsc with ⟨$, -⟩
  iapply chan.wp_send ch v γ.chan_name $$ Hch
  iintro ⟨Hlc1, Hlc2, Hlc3, _⟩
  iapply spsc_send_au γ ch P R sent v (Φ #()) $$ Hspsc [$Hlc1 $Hlc2 $Hlc3] [$Hprod $HP] HΦ

omit [IntoValTyped (GF := GF) V t] in
set_option maxHeartbeats 400000 in
theorem spsc_close_au (γ : spsc_names) (ch : loc) (P : Int → V → IProp GF) (R : List V → IProp GF)
    (sent : List V) (Φ : IProp GF) :
    ⊢ is_spsc γ ch P R -∗ £ 1 -∗ spsc_producer γ sent ∗ R sent -∗ ▷ Φ -∗
      close_au γ.chan_name V Φ := by
  unfold is_spsc close_au
  iintro ⟨#Hchan, #Hinv⟩ Hlc1 ⟨Hprod, HR⟩ Hcont
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc1 Hi with Hi
  icases spsc_inv_elim _ _ _ $$ Hi with ⟨%s, %sent0, %recv, Hch, HsentI, HrecvI, %Hrel, Hm⟩
  unfold spsc_producer
  ihave %Heq := dghost_var_agree _ _ _ _ _ $$ Hprod HsentI
  subst Heq
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
    imod Hclose $$ [Hoc HsentI HrecvI Hm Hprod HR] with -
    · inext
      iapply spsc_inv_intro γ P R (.Closed buff) sent recv (by simpa [inflight] using Hrel)
        $$ Hoc HsentI HrecvI
      cases buff with
      | nil =>
        simp only [spsc_inv_match, spsc_producer]
        isplitl [Hprod]
        · iexact Hprod
        · ileft; iexact HR
      | cons w ws =>
        simp only [spsc_inv_match, spsc_producer]
        isplitl [Hm]
        · iexact Hm
        isplitl [Hprod]
        · iexact Hprod
        · ileft; iexact HR
    imodintro
    iexact Hcont
  | Idle =>
    dsimp only
    iintro Hoc
    imod Hmask with -
    imod Hclose $$ [Hoc HsentI HrecvI Hprod HR] with -
    · inext
      iapply spsc_inv_intro γ P R (.Closed []) sent recv (by simpa [inflight] using Hrel)
        $$ Hoc HsentI HrecvI
      simp only [spsc_inv_match, spsc_producer]
      isplitl [Hprod]
      · iexact Hprod
      · ileft; iexact HR
    imodintro
    iexact Hcont
  | Closed d =>
    dsimp only
    cases d with
    | nil =>
      simp only [spsc_inv_match, spsc_producer]
      icases Hm with ⟨Hp2, -⟩
      iapply dghost_var_three_halves $$ Hprod HsentI Hp2
    | cons _ _ =>
      simp only [spsc_inv_match, spsc_producer]
      icases Hm with ⟨-, Hp2, -⟩
      iapply dghost_var_three_halves $$ Hprod HsentI Hp2
  | _ => itrivial

/-- SPSC close operation. -/
theorem wp_spsc_close (γ : spsc_names) (ch : loc) (P : Int → V → IProp GF) (R : List V → IProp GF)
    (sent : List V) {ct : go.type} {dir : go.chan_dir} [ct ↓u go.ChannelType dir t] :
    {{ is_spsc γ ch P R ∗ spsc_producer γ sent ∗ R sent }}
      (App (Val #(functions go.close [ct])) (Val #ch))
    {{ RET #(); True }} := by
  iintro %Φ ⟨#Hspsc, Hprod, HR⟩ HΦ
  ihave #Hch : is_chan ch γ.chan_name V $$ [Hspsc]
  · unfold is_spsc; icases Hspsc with ⟨$, -⟩
  iapply chan.wp_close (ct := ct) ch γ.chan_name $$ Hch
  iintro ⟨Hlc1, _, _, _⟩
  iapply spsc_close_au γ ch P R sent (Φ #()) $$ Hspsc Hlc1 [$Hprod $HR]
  inext
  iapply HΦ
  itrivial

end spsc

end Perennial
