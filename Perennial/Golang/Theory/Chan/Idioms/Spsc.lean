/-
Port of `new/golang/theory/chan/idioms/spsc.v`: single-producer single-consumer (SPSC)
channels, with histories of sent and received values.

* Producer maintains exclusive send permission with history tracking.
* Consumer maintains exclusive receive permission with history tracking.
* Ghost state tracks sent/received histories with fractional permissions.
* The invariant maintains `sent = received ++ in_flight`.
* Resource protocols `P` (per-value, indexed by position) and `R` (final state).

Lean notes: the per-state part of the invariant is the separate definition
`spscInvMatch`; `[Pos.Countable V]` as in `ChanAuBase.lean`.
-/
import Perennial.Golang.Theory.Chan.Idioms.Base
import Perennial.Golang.Theory.Chan

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

/-- Ghost state names of an SPSC channel. -/
structure SpscNames where
  /-- Underlying channel ghost state -/
  chanName : ChanNames
  /-- History of sent values -/
  spscSentName : GName
  /-- History of received values -/
  spscRecvName : GName

section spsc
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable {V : Type} [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V] {t : go.GoType}
  [IntoValTyped (GF := GF) V t]

/-- Producer maintains (1/2) permission of sent history. -/
def spscProducer (γ : SpscNames) (sent : List V) : IProp GF :=
  dghostVar γ.spscSentName (DFrac.own (1 : Qp).half) sent

/-- Consumer maintains (1/2) permission of received history. -/
def spscConsumer (γ : SpscNames) (received : List V) : IProp GF :=
  dghostVar γ.spscRecvName (DFrac.own (1 : Qp).half) received

/-- Values that have been sent but not yet received. -/
def inflight (s : chanstate.t V) : List V :=
  match s with
  | .Buffered buff => buff
  | .SndPending v | .SndCommit v => [v]
  | .Closed drain => drain
  | _ => []

/-- The state-dependent part of the SPSC invariant. -/
def spscInvMatch (γ : SpscNames) (P : Int → V → IProp GF) (R : List V → IProp GF)
    (sent recv : List V) (s : chanstate.t V) : IProp GF :=
  match s with
  -- P holds for all buffered values
  | .Buffered buff => iprop([∗list] i ↦ v ∈ buff, P ((recv.length : Int) + i) v)
  -- P holds for pending/committed values
  | .SndPending v | .SndCommit v => P recv.length v
  -- Closed channel: park producer permission, provide R when drained
  | .Closed [] => iprop(spscProducer γ sent ∗ (R sent ∨ spscConsumer γ sent))
  | .Closed drain =>
      iprop(([∗list] i ↦ v ∈ drain, P ((recv.length : Int) + i) v) ∗
        spscProducer γ sent ∗ (R sent ∨ spscConsumer γ sent))
  | _ => iprop(True)

@[irreducible] def spscInv (γ : SpscNames) (P : Int → V → IProp GF) (R : List V → IProp GF) : IProp GF :=
  iprop(∃ (s : chanstate.t V) (sent recv : List V),
    "Hch" ∷ ownChan γ.chanName V s ∗
    "HsentI" ∷ dghostVar γ.spscSentName (DFrac.own (1 : Qp).half) sent ∗
    "HrecvI" ∷ dghostVar γ.spscRecvName (DFrac.own (1 : Qp).half) recv ∗
    "%Hrel" ∷ ⌜sent = recv ++ inflight s⌝ ∗
    "Hm" ∷ spscInvMatch γ P R sent recv s)

/-- The main SPSC channel predicate.

* `P`: resource associated with each value (maintained while in-flight);
* `R`: final resource when channel is closed and drained.

The invariant maintains `sent = received + inflight(channel_state)`, `P` for all
in-flight values; when closed, the producer permission is parked to prevent further
sends, and when closed and drained, the consumer gets `R`. -/
def isSpsc (γ : SpscNames) (ch : Loc) (P : Int → V → IProp GF) (R : List V → IProp GF) :
    IProp GF :=
  iprop(isChan ch γ.chanName V ∗ inv nroot (spscInv γ P R))

instance isSpsc_persistent (γ : SpscNames) (ch : Loc) (P : Int → V → IProp GF)
    (R : List V → IProp GF) : Persistent (isSpsc γ ch P R) := by
  unfold isSpsc; infer_instance

omit [ZeroVal V] [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V t] in
theorem dghostVar_halves {A : Type} [Pos.Countable A] (γ : GName) (a : A) :
    dghostVar (GF := GF) γ (DFrac.own 1) a ⊢
      dghostVar γ (DFrac.own (1 : Qp).half) a ∗ dghostVar γ (DFrac.own (1 : Qp).half) a := by
  have h := dghostVar_split (GF := GF) γ a (DFrac.own (1 : Qp).half) (DFrac.own (1 : Qp).half)
  rw [DFrac.op_own, Qp.half_add_half] at h
  exact wand_entails h

omit [ZeroVal V] [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V t] in
/-- Three halves of a `dghostVar` are contradictory. -/
theorem dghostVar_three_halves {A : Type} [Pos.Countable A] (γ : GName) (a b c : A) :
    ⊢ dghostVar (GF := GF) γ (DFrac.own (1 : Qp).half) a -∗
      dghostVar γ (DFrac.own (1 : Qp).half) b -∗
      dghostVar γ (DFrac.own (1 : Qp).half) c -∗ False := by
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
theorem start_spsc (ch : Loc) (P : Int → V → IProp GF) (R : List V → IProp GF) (γ : ChanNames) :
    ⊢ isChan ch γ V -∗ (ownChan γ V .Idle ∨ ownChan γ V (.Buffered [])) ={⊤}=∗
      ∃ γspsc, isSpsc γspsc ch P R ∗ spscProducer γspsc ([] : List V) ∗
        spscConsumer γspsc ([] : List V) := by
  iintro #Hch Hoc
  imod dghostVar_alloc ([] : List V) with ⟨%γsent, Hsent⟩
  icases dghostVar_halves _ _ $$ Hsent with ⟨HsentA, HsentF⟩
  imod dghostVar_alloc ([] : List V) with ⟨%γrecv, Hrecv⟩
  icases dghostVar_halves _ _ $$ Hrecv with ⟨HrecvA, HrecvF⟩
  iexists ⟨γ, γsent, γrecv⟩
  unfold isSpsc spscProducer spscConsumer
  imod inv_alloc nroot ⊤ (spscInv ⟨γ, γsent, γrecv⟩ P R) $$ [Hoc HsentA HrecvA] with #Hinv
  · inext
    unfold spscInv
    icases Hoc with (Hoc | Hoc)
    · iexists .Idle, [], []
      simp only [spscInvMatch, inflight, List.append_nil]
      iframe
      isplit <;> itrivial
    · iexists .Buffered [], [], []
      simp only [spscInvMatch, inflight, List.append_nil]
      iframe
      isplitr
      · itrivial
      · iapply BigSepL.bigSepL_nil.2
        iempintro
  imodintro
  iframe
  iframe #

omit [IntoValTyped (GF := GF) V t] in
theorem spscInv_intro (γ : SpscNames) (P : Int → V → IProp GF) (R : List V → IProp GF)
    (s : chanstate.t V) (sent recv : List V) (h : sent = recv ++ inflight s) :
    ⊢ ownChan γ.chanName V s -∗
      dghostVar γ.spscSentName (DFrac.own (1 : Qp).half) sent -∗
      dghostVar γ.spscRecvName (DFrac.own (1 : Qp).half) recv -∗
      spscInvMatch γ P R sent recv s -∗ spscInv γ P R := by
  iintro H1 H2 H3 H4
  unfold spscInv
  iexists s, sent, recv
  isplitl [H1]; · iexact H1
  isplitl [H2]; · iexact H2
  isplitl [H3]; · iexact H3
  isplitr
  · ipureintro; exact h
  · iexact H4

omit [IntoValTyped (GF := GF) V t] in
theorem spscInv_elim (γ : SpscNames) (P : Int → V → IProp GF) (R : List V → IProp GF) :
    spscInv γ P R ⊢ ∃ (s : chanstate.t V) (sent recv : List V),
      ownChan γ.chanName V s ∗
      dghostVar γ.spscSentName (DFrac.own (1 : Qp).half) sent ∗
      dghostVar γ.spscRecvName (DFrac.own (1 : Qp).half) recv ∗
      ⌜sent = recv ++ inflight s⌝ ∗ spscInvMatch γ P R sent recv s := by
  unfold spscInv; exact .rfl

omit [IntoValTyped (GF := GF) V t] in
set_option maxHeartbeats 400000 in
theorem spsc_rcv_au (γ : SpscNames) (ch : Loc) (P : Int → V → IProp GF) (R : List V → IProp GF)
    (received : List V) (Φ : V → Bool → IProp GF) :
    ⊢ isSpsc γ ch P R -∗ £ 1 ∗ £ 1 -∗ spscConsumer γ received -∗
      ▷ (∀ (v : V) (ok : Bool),
          (if ok then iprop(P received.length v ∗ spscConsumer γ (received ++ [v]))
           else iprop(R received ∗ ⌜v = zero_val V⌝)) -∗ Φ v ok) -∗
      recvAu γ.chanName V Φ := by
  unfold isSpsc recvAu
  iintro ⟨#Hchan, #Hinv⟩ ⟨Hlc1, Hlc2⟩ Hcons Hcont
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc1 Hi with Hi
  icases spscInv_elim _ _ _ $$ Hi with ⟨%s, %sent, %recv, Hch, HsentI, HrecvI, %Hrel, Hm⟩
  unfold spscConsumer
  ihave %Heq := dghostVar_agree _ _ _ _ _ $$ Hcons HrecvI
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
      imod dghostVar_update_halves (received ++ [v]) _ _ _ $$ Hcons HrecvI with ⟨Hcons, HrecvI⟩
      simp only [spscInvMatch]
      icases (spsc_pop P received v rest).1 $$ Hm with ⟨HPv, Hrest⟩
      imod Hmask with -
      imod Hclose $$ [Hoc HsentI HrecvI Hrest] with -
      · inext
        iapply spscInv_intro γ P R (.Buffered rest) sent (received ++ [v]) (by simp [Hrel, inflight])
          $$ Hoc HsentI HrecvI
        simp only [spscInvMatch]
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
      iapply spscInv_intro γ P R .RcvPending sent received (by simpa [inflight] using Hrel)
        $$ Hoc HsentI HrecvI
      simp only [spscInvMatch]
      itrivial
    imodintro
    unfold recvNestedAu
    iinv Hinv with Hi Hclose
    imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc2 Hi with Hi
    icases spscInv_elim _ _ _ $$ Hi with ⟨%s, %sent, %recv, Hch, HsentI, HrecvI, %Hrel, Hm⟩
    ihave %Heq := dghostVar_agree _ _ _ _ _ $$ Hcons HrecvI
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
      imod dghostVar_update_halves (received ++ [v]) _ _ _ $$ Hcons HrecvI with ⟨Hcons, HrecvI⟩
      simp only [spscInvMatch]
      imod Hmask with -
      imod Hclose $$ [Hoc HsentI HrecvI] with -
      · inext
        iapply spscInv_intro γ P R .Idle sent (received ++ [v]) (by simpa [inflight] using Hrel)
          $$ Hoc HsentI HrecvI
        simp only [spscInvMatch]
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
        simp only [spscInvMatch, spscConsumer]
        icases Hm with ⟨Hprod, (HR | Hc2)⟩
        · iintro Hoc
          imod Hmask with -
          imod Hclose $$ [Hoc HsentI HrecvI Hprod Hcons] with -
          · inext
            iapply spscInv_intro γ P R (.Closed []) sent sent (by simp [inflight])
              $$ Hoc HsentI HrecvI
            simp only [spscInvMatch, spscConsumer]
            isplitl [Hprod]
            · iexact Hprod
            · iright; iexact Hcons
          imodintro
          iapply Hcont
          simp only [Bool.false_eq_true, ↓reduceIte]
          iframe
        · iexfalso
          iapply dghostVar_three_halves $$ Hcons HrecvI Hc2
      | cons _ _ => itrivial
    | _ => itrivial
  | SndPending v =>
    dsimp only
    iintro Hoc
    imod dghostVar_update_halves (received ++ [v]) _ _ _ $$ Hcons HrecvI with ⟨Hcons, HrecvI⟩
    simp only [spscInvMatch]
    imod Hmask with -
    imod Hclose $$ [Hoc HsentI HrecvI] with -
    · inext
      iapply spscInv_intro γ P R .RcvCommit sent (received ++ [v]) (by simpa [inflight] using Hrel)
        $$ Hoc HsentI HrecvI
      simp only [spscInvMatch]
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
      simp only [spscInvMatch, spscConsumer]
      icases Hm with ⟨Hprod, (HR | Hc2)⟩
      · iintro Hoc
        imod Hmask with -
        imod Hclose $$ [Hoc HsentI HrecvI Hprod Hcons] with -
        · inext
          iapply spscInv_intro γ P R (.Closed []) sent sent (by simp [inflight])
            $$ Hoc HsentI HrecvI
          simp only [spscInvMatch, spscConsumer]
          isplitl [Hprod]
          · iexact Hprod
          · iright; iexact Hcons
        imodintro
        iapply Hcont
        simp only [Bool.false_eq_true, ↓reduceIte]
        iframe
      · iexfalso
        iapply dghostVar_three_halves $$ Hcons HrecvI Hc2
    | cons v rest =>
      dsimp only
      iintro Hoc
      imod dghostVar_update_halves (received ++ [v]) _ _ _ $$ Hcons HrecvI with ⟨Hcons, HrecvI⟩
      simp only [spscInvMatch]
      icases Hm with ⟨Hbig, Hprod, Hor⟩
      icases (spsc_pop P received v rest).1 $$ Hbig with ⟨HPv, Hrest⟩
      imod Hmask with -
      imod Hclose $$ [Hoc HsentI HrecvI Hrest Hprod Hor] with -
      · inext
        iapply spscInv_intro γ P R (.Closed rest) sent (received ++ [v]) (by simp [Hrel, inflight])
          $$ Hoc HsentI HrecvI
        cases rest with
        | nil =>
          simp only [spscInvMatch]
          isplitl [Hprod]
          · iexact Hprod
          · iexact Hor
        | cons w ws =>
          simp only [spscInvMatch]
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
theorem wp_spsc_receive (γ : SpscNames) (ch : Loc) (P : Int → V → IProp GF)
    (R : List V → IProp GF) (received : List V) :
    {{ isSpsc γ ch P R ∗ spscConsumer γ received }}
      (App (Val (chan.receive t)) (Val #ch))
    {{ (v : V) (ok : Bool), RET (PairV #v #ok);
        (if ok then iprop(P received.length v ∗ spscConsumer γ (received ++ [v]))
         else iprop(R received ∗ ⌜v = zero_val V⌝)) }} := by
  iintro %Φ ⟨#Hspsc, Hcons⟩ HΦ
  ihave #Hch : isChan ch γ.chanName V $$ [Hspsc]
  · unfold isSpsc; icases Hspsc with ⟨$, -⟩
  iapply chan.wp_receive ch γ.chanName $$ Hch
  iintro ⟨Hlc1, Hlc2, _, _⟩
  iapply spsc_rcv_au γ ch P R received (fun v ok => Φ (PairV #v #ok)) $$ Hspsc [$Hlc1 $Hlc2] Hcons
  inext
  iintro %v %ok H
  iapply HΦ $$ %v %ok H

omit [IntoValTyped (GF := GF) V t] in
set_option maxHeartbeats 400000 in
theorem spsc_send_au (γ : SpscNames) (ch : Loc) (P : Int → V → IProp GF) (R : List V → IProp GF)
    (sent : List V) (v : V) (Φ : IProp GF) :
    ⊢ isSpsc γ ch P R -∗ £ 1 ∗ £ 1 ∗ £ 1 -∗ spscProducer γ sent ∗ P sent.length v -∗
      ▷ (spscProducer γ (sent ++ [v]) -∗ Φ) -∗ sendAu γ.chanName v Φ := by
  unfold isSpsc sendAu
  iintro ⟨#Hchan, #Hinv⟩ ⟨Hlc1, Hlc2, Hlc3⟩ ⟨Hprod, HP⟩ Hcont
  imod lc_fupd_elim_later (E := ⊤) $$ Hlc1 Hcont with Hcont
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc2 Hi with Hi
  icases spscInv_elim _ _ _ $$ Hi with ⟨%s, %sent0, %recv, Hch, HsentI, HrecvI, %Hrel, Hm⟩
  unfold spscProducer
  ihave %Heq := dghostVar_agree _ _ _ _ _ $$ Hprod HsentI
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
    imod dghostVar_update_halves ((recv ++ buff) ++ [v]) _ _ _ $$ Hprod HsentI with ⟨Hprod, HsentI⟩
    imod Hmask with -
    imod Hclose $$ [Hoc HsentI HrecvI Hm HP] with -
    · inext
      iapply spscInv_intro γ P R (.Buffered (buff ++ [v])) ((recv ++ buff) ++ [v]) recv
        (by simp [inflight]) $$ Hoc HsentI HrecvI
      simp only [spscInvMatch]
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
    imod dghostVar_update_halves (sent ++ [v]) _ _ _ $$ Hprod HsentI with ⟨Hprod, HsentI⟩
    imod Hmask with -
    imod Hclose $$ [Hoc HsentI HrecvI HP] with -
    · inext
      iapply spscInv_intro γ P R (.SndPending v) (sent ++ [v]) sent (by simp [inflight])
        $$ Hoc HsentI HrecvI
      simp only [spscInvMatch]
      iexact HP
    imodintro
    unfold sendNestedAu
    iinv Hinv with Hi Hclose
    imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc3 Hi with Hi
    icases spscInv_elim _ _ _ $$ Hi with ⟨%s, %sent1, %recv1, Hch, HsentI, HrecvI, %Hrel, Hm⟩
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
        iapply spscInv_intro γ P R .Idle sent1 recv1 (by simpa [inflight] using Hrel)
          $$ Hoc HsentI HrecvI
        simp only [spscInvMatch]
        itrivial
      imodintro
      iapply Hcont $$ Hprod
    | Closed d =>
      dsimp only
      cases d with
      | nil =>
        simp only [spscInvMatch, spscProducer]
        icases Hm with ⟨Hp2, -⟩
        iapply dghostVar_three_halves $$ Hprod HsentI Hp2
      | cons _ _ =>
        simp only [spscInvMatch, spscProducer]
        icases Hm with ⟨-, Hp2, -⟩
        iapply dghostVar_three_halves $$ Hprod HsentI Hp2
    | _ => itrivial
  | RcvPending =>
    dsimp only
    simp only [inflight, List.append_nil] at Hrel
    subst Hrel
    iintro Hoc
    imod dghostVar_update_halves (sent ++ [v]) _ _ _ $$ Hprod HsentI with ⟨Hprod, HsentI⟩
    imod Hmask with -
    imod Hclose $$ [Hoc HsentI HrecvI HP] with -
    · inext
      iapply spscInv_intro γ P R (.SndCommit v) (sent ++ [v]) sent (by simp [inflight])
        $$ Hoc HsentI HrecvI
      simp only [spscInvMatch]
      iexact HP
    imodintro
    iapply Hcont $$ Hprod
  | Closed d =>
    dsimp only
    cases d with
    | nil =>
      simp only [spscInvMatch, spscProducer]
      icases Hm with ⟨Hp2, -⟩
      iapply dghostVar_three_halves $$ Hprod HsentI Hp2
    | cons _ _ =>
      simp only [spscInvMatch, spscProducer]
      icases Hm with ⟨-, Hp2, -⟩
      iapply dghostVar_three_halves $$ Hprod HsentI Hp2
  | _ => itrivial

/-- SPSC send operation with history tracking. -/
theorem wp_spsc_send (γ : SpscNames) (ch : Loc) (P : Int → V → IProp GF) (R : List V → IProp GF)
    (sent : List V) (v : V) :
    {{ isSpsc γ ch P R ∗ spscProducer γ sent ∗ P sent.length v }}
      (App (App (Val (chan.send t)) (Val #ch)) (Val #v))
    {{ RET #(); spscProducer γ (sent ++ [v]) }} := by
  iintro %Φ ⟨#Hspsc, Hprod, HP⟩ HΦ
  ihave #Hch : isChan ch γ.chanName V $$ [Hspsc]
  · unfold isSpsc; icases Hspsc with ⟨$, -⟩
  iapply chan.wp_send ch v γ.chanName $$ Hch
  iintro ⟨Hlc1, Hlc2, Hlc3, _⟩
  iapply spsc_send_au γ ch P R sent v (Φ #()) $$ Hspsc [$Hlc1 $Hlc2 $Hlc3] [$Hprod $HP] HΦ

omit [IntoValTyped (GF := GF) V t] in
set_option maxHeartbeats 400000 in
theorem spsc_close_au (γ : SpscNames) (ch : Loc) (P : Int → V → IProp GF) (R : List V → IProp GF)
    (sent : List V) (Φ : IProp GF) :
    ⊢ isSpsc γ ch P R -∗ £ 1 -∗ spscProducer γ sent ∗ R sent -∗ ▷ Φ -∗
      closeAu γ.chanName V Φ := by
  unfold isSpsc closeAu
  iintro ⟨#Hchan, #Hinv⟩ Hlc1 ⟨Hprod, HR⟩ Hcont
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc1 Hi with Hi
  icases spscInv_elim _ _ _ $$ Hi with ⟨%s, %sent0, %recv, Hch, HsentI, HrecvI, %Hrel, Hm⟩
  unfold spscProducer
  ihave %Heq := dghostVar_agree _ _ _ _ _ $$ Hprod HsentI
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
      iapply spscInv_intro γ P R (.Closed buff) sent recv (by simpa [inflight] using Hrel)
        $$ Hoc HsentI HrecvI
      cases buff with
      | nil =>
        simp only [spscInvMatch, spscProducer]
        isplitl [Hprod]
        · iexact Hprod
        · ileft; iexact HR
      | cons w ws =>
        simp only [spscInvMatch, spscProducer]
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
      iapply spscInv_intro γ P R (.Closed []) sent recv (by simpa [inflight] using Hrel)
        $$ Hoc HsentI HrecvI
      simp only [spscInvMatch, spscProducer]
      isplitl [Hprod]
      · iexact Hprod
      · ileft; iexact HR
    imodintro
    iexact Hcont
  | Closed d =>
    dsimp only
    cases d with
    | nil =>
      simp only [spscInvMatch, spscProducer]
      icases Hm with ⟨Hp2, -⟩
      iapply dghostVar_three_halves $$ Hprod HsentI Hp2
    | cons _ _ =>
      simp only [spscInvMatch, spscProducer]
      icases Hm with ⟨-, Hp2, -⟩
      iapply dghostVar_three_halves $$ Hprod HsentI Hp2
  | _ => itrivial

/-- SPSC close operation. -/
theorem wp_spsc_close (γ : SpscNames) (ch : Loc) (P : Int → V → IProp GF) (R : List V → IProp GF)
    (sent : List V) {ct : go.GoType} {dir : go.ChanDir} [ct ↓u go.ChannelType dir t] :
    {{ isSpsc γ ch P R ∗ spscProducer γ sent ∗ R sent }}
      (App (Val #(functions go.close [ct])) (Val #ch))
    {{ RET #(); True }} := by
  iintro %Φ ⟨#Hspsc, Hprod, HR⟩ HΦ
  ihave #Hch : isChan ch γ.chanName V $$ [Hspsc]
  · unfold isSpsc; icases Hspsc with ⟨$, -⟩
  iapply chan.wp_close (ct := ct) ch γ.chanName $$ Hch
  iintro ⟨Hlc1, _, _, _⟩
  iapply spsc_close_au γ ch P R sent (Φ #()) $$ Hspsc Hlc1 [$Hprod $HR]
  inext
  iapply HΦ
  itrivial

end spsc

end Perennial
