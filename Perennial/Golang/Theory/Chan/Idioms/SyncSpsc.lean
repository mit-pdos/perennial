/-
Synchronous single-producer single-consumer (SPSC) channels: the SPSC idiom
(`Spsc.lean`) for an *unbuffered* channel, with each side's pending operation
recorded, so that the two sides together know that nothing is in flight.

* Go's unbuffered send synchronizes with its receive: once both the producer
  and the consumer stand outside an operation on the channel, every value sent
  has been received. `isSpsc` keeps `sent = received ++ inflight s`, but its
  `RcvPending`/`SndCommit` states (a receive in progress) and
  `SndPending`/`RcvCommit` (a send in progress) are not tied to the sides'
  tokens, so the holder of both tokens cannot exclude a value in flight.
* Here each side's history ghost variable carries a flag, `true` while that
  side's operation is in progress (set by the operation's first atomic step,
  cleared by its last); a side's token (`sspscProducer`, `sspscConsumer`) has
  it `false`, and the invariant requires the flag of the side whose operation
  a pending state belongs to. The channel is unbuffered: no `Buffered` state,
  nor a `Closed` one with values to drain.
* `sspsc_sync`: the producer's and the consumer's tokens give `sent = recv`.
  Otherwise the statements are those of `Spsc.lean`.

A use: a goroutine that owns both ends of a channel between two phases (it
took the producer's token back from a stopped producer goroutine) and starts
the next phase at the producer's count, which must be its own consumer
position.
-/
module

public import Perennial.Golang.Theory.Chan.Idioms.Spsc

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section sspsc
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable {V : Type} [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V] {t : go.GoType}
  [IntoValTyped (GF := GF) V t]

/-- The producer's token: half of the sent history, no send in progress. -/
def sspscProducer (γ : SpscNames) (sent : List V) : IProp GF :=
  dghostVar γ.spscSentName (DFrac.own (1 : Qp).half) (sent, false)

/-- The consumer's token: half of the received history, no receive in progress. -/
def sspscConsumer (γ : SpscNames) (received : List V) : IProp GF :=
  dghostVar γ.spscRecvName (DFrac.own (1 : Qp).half) (received, false)

/-- **The pending states need their side's flag**: a send in progress (`SndPending`, `RcvCommit`)
the producer's, a receive in progress (`RcvPending`, `SndCommit`) the consumer's. -/
def sspscFlagsOk (s : ChanState V) (pf cf : Bool) : Prop :=
  (match s with | .SndPending _ | .RcvCommit => pf = true | _ => True) ∧
  (match s with | .RcvPending | .SndCommit _ => cf = true | _ => True)

/-- The state-dependent part of the invariant (no buffer: the channel is unbuffered). -/
def sspscInvMatch (γ : SpscNames) (P : Int → V → IProp GF) (R : List V → IProp GF)
    (sent recv : List V) (s : ChanState V) : IProp GF :=
  match s with
  | .Buffered _ => iprop(False)
  | .SndPending v | .SndCommit v => P recv.length v
  | .Closed [] => iprop(sspscProducer γ sent ∗ (R sent ∨ sspscConsumer γ sent))
  | .Closed (_ :: _) => iprop(False)
  | _ => iprop(True)

@[irreducible] def sspscInv (γ : SpscNames) (P : Int → V → IProp GF) (R : List V → IProp GF) :
    IProp GF :=
  iprop(∃ (s : ChanState V) (sent recv : List V) (pf cf : Bool),
    "Hch" ∷ ownChan γ.chanName V s ∗
    "HsentI" ∷ dghostVar γ.spscSentName (DFrac.own (1 : Qp).half) (sent, pf) ∗
    "HrecvI" ∷ dghostVar γ.spscRecvName (DFrac.own (1 : Qp).half) (recv, cf) ∗
    "%Hrel" ∷ ⌜sent = recv ++ inflight s ∧ sspscFlagsOk s pf cf⌝ ∗
    "Hm" ∷ sspscInvMatch γ P R sent recv s)

/-- **A synchronous SPSC channel** (persistent): `isSpsc` for an unbuffered channel, with each
side's pending operation recorded (the file header). -/
def isSspsc (γ : SpscNames) (ch : Loc) (P : Int → V → IProp GF) (R : List V → IProp GF) :
    IProp GF :=
  iprop(isChan ch γ.chanName V ∗ inv nroot (sspscInv γ P R))

instance isSspsc_persistent (γ : SpscNames) (ch : Loc) (P : Int → V → IProp GF)
    (R : List V → IProp GF) : Persistent (isSspsc γ ch P R) := by
  unfold isSspsc; infer_instance

omit [ZeroVal V] [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V t] in
theorem sspscInv_intro (γ : SpscNames) (P : Int → V → IProp GF) (R : List V → IProp GF)
    (s : ChanState V) (sent recv : List V) (pf cf : Bool) (h : sent = recv ++ inflight s)
    (hf : sspscFlagsOk s pf cf) :
    ⊢ ownChan γ.chanName V s -∗
      dghostVar γ.spscSentName (DFrac.own (1 : Qp).half) (sent, pf) -∗
      dghostVar γ.spscRecvName (DFrac.own (1 : Qp).half) (recv, cf) -∗
      sspscInvMatch γ P R sent recv s -∗ sspscInv γ P R := by
  iintro H1 H2 H3 H4
  unfold sspscInv
  iexists s, sent, recv, pf, cf
  isplitl [H1]; · iexact H1
  isplitl [H2]; · iexact H2
  isplitl [H3]; · iexact H3
  isplitr
  · ipureintro; exact ⟨h, hf⟩
  · iexact H4

omit [ZeroVal V] [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V t] in
theorem sspscInv_elim (γ : SpscNames) (P : Int → V → IProp GF) (R : List V → IProp GF) :
    sspscInv γ P R ⊢ ∃ (s : ChanState V) (sent recv : List V) (pf cf : Bool),
      ownChan γ.chanName V s ∗
      dghostVar γ.spscSentName (DFrac.own (1 : Qp).half) (sent, pf) ∗
      dghostVar γ.spscRecvName (DFrac.own (1 : Qp).half) (recv, cf) ∗
      ⌜sent = recv ++ inflight s ∧ sspscFlagsOk s pf cf⌝ ∗ sspscInvMatch γ P R sent recv s := by
  unfold sspscInv; exact .rfl

omit [IntoValTyped (GF := GF) V t] in
/-- Create a synchronous SPSC channel from an unbuffered channel. -/
theorem start_sspsc (ch : Loc) (P : Int → V → IProp GF) (R : List V → IProp GF) (γ : ChanNames) :
    ⊢ isChan ch γ V -∗ ownChan γ V .Idle ={⊤}=∗
      ∃ γspsc, isSspsc γspsc ch P R ∗ sspscProducer γspsc ([] : List V) ∗
        sspscConsumer γspsc ([] : List V) := by
  iintro #Hch Hoc
  imod dghostVar_alloc (([] : List V), false) with ⟨%γsent, Hsent⟩
  icases dghostVar_halves _ _ $$ Hsent with ⟨HsentA, HsentF⟩
  imod dghostVar_alloc (([] : List V), false) with ⟨%γrecv, Hrecv⟩
  icases dghostVar_halves _ _ $$ Hrecv with ⟨HrecvA, HrecvF⟩
  iexists ⟨γ, γsent, γrecv⟩
  unfold isSspsc sspscProducer sspscConsumer
  imod inv_alloc nroot ⊤ (sspscInv ⟨γ, γsent, γrecv⟩ P R) $$ [Hoc HsentA HrecvA] with #Hinv
  · inext
    iapply sspscInv_intro ⟨γ, γsent, γrecv⟩ P R .Idle [] [] false false (by simp [inflight])
      (by simp [sspscFlagsOk]) $$ Hoc HsentA HrecvA
    simp only [sspscInvMatch]
    itrivial
  imodintro
  iframe
  iframe #

omit [IntoValTyped (GF := GF) V t] in
/-- **The two sides' tokens: nothing in flight** (the file header). -/
theorem sspsc_sync (γ : SpscNames) (ch : Loc) (P : Int → V → IProp GF) (R : List V → IProp GF)
    (sent recv : List V) :
    ⊢ isSspsc γ ch P R -∗ £ 1 -∗ sspscProducer γ sent -∗ sspscConsumer γ recv ={⊤}=∗
      ⌜sent = recv⌝ ∗ sspscProducer γ sent ∗ sspscConsumer γ recv := by
  unfold isSspsc
  iintro ⟨#Hchan, #Hinv⟩ Hlc Hprod Hcons
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc Hi with Hi
  icases sspscInv_elim _ _ _ $$ Hi with ⟨%s, %sent0, %recv0, %pf, %cf, Hch, HsentI, HrecvI,
    %Hrel, Hm⟩
  unfold sspscProducer sspscConsumer
  ihave %Hp := dghostVar_agree _ _ _ _ _ $$ Hprod HsentI
  ihave %Hc := dghostVar_agree _ _ _ _ _ $$ Hcons HrecvI
  simp only [Prod.mk.injEq] at Hp Hc
  obtain ⟨rfl, rfl⟩ := Hp
  obtain ⟨rfl, rfl⟩ := Hc
  obtain ⟨Hrel, Hf1, Hf2⟩ := Hrel
  cases s with
  | Buffered _ => simp only [sspscInvMatch]; iexfalso; iexact Hm
  | Closed d =>
    cases d with
    | nil =>
      simp only [sspscInvMatch, sspscProducer]
      icases Hm with ⟨Hp2, -⟩
      iexfalso
      iapply dghostVar_three_halves $$ Hprod HsentI Hp2
    | cons _ _ => simp only [sspscInvMatch]; iexfalso; iexact Hm
  | Idle =>
    imod Hclose $$ [Hch HsentI HrecvI Hm] with -
    · inext
      iapply sspscInv_intro γ P R .Idle sent recv false false Hrel ⟨Hf1, Hf2⟩ $$ Hch HsentI HrecvI Hm
    imodintro
    iframe
    ipureintro; simpa [inflight] using Hrel
  | SndPending _ => simp at Hf1
  | RcvCommit => simp at Hf1
  | RcvPending => simp at Hf2
  | SndCommit _ => simp at Hf2

omit [IntoValTyped (GF := GF) V t] in
set_option maxHeartbeats 800000 in
theorem sspsc_rcv_au (γ : SpscNames) (ch : Loc) (P : Int → V → IProp GF) (R : List V → IProp GF)
    (received : List V) (Φ : V → Bool → IProp GF) :
    ⊢ isSspsc γ ch P R -∗ £ 1 ∗ £ 1 -∗ sspscConsumer γ received -∗
      ▷ (∀ (v : V) (ok : Bool),
          (if ok then iprop(P received.length v ∗ sspscConsumer γ (received ++ [v]))
           else iprop(R received ∗ ⌜v = zero_val V⌝)) -∗ Φ v ok) -∗
      recvAu γ.chanName V Φ := by
  unfold isSspsc recvAu
  iintro ⟨#Hchan, #Hinv⟩ ⟨Hlc1, Hlc2⟩ Hcons Hcont
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc1 Hi with Hi
  icases sspscInv_elim _ _ _ $$ Hi with ⟨%s, %sent, %recv, %pf, %cf, Hch, HsentI, HrecvI, %Hrel, Hm⟩
  unfold sspscConsumer
  ihave %Heq := dghostVar_agree _ _ _ _ _ $$ Hcons HrecvI
  simp only [Prod.mk.injEq] at Heq
  obtain ⟨rfl, rfl⟩ := Heq
  obtain ⟨Hrel, Hf⟩ := Hrel
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists s
  iframe Hch
  cases s with
  | Buffered b => simp only [sspscInvMatch]; iexfalso; iexact Hm
  | Idle =>
    dsimp only
    iintro Hoc
    imod dghostVar_update_halves (received, true) _ _ _ $$ Hcons HrecvI with ⟨Hcons, HrecvI⟩
    imod Hmask with -
    imod Hclose $$ [Hoc HsentI HrecvI] with -
    · inext
      iapply sspscInv_intro γ P R .RcvPending sent received pf true (by simpa [inflight] using Hrel)
        (by simp [sspscFlagsOk]) $$ Hoc HsentI HrecvI
      simp only [sspscInvMatch]
      itrivial
    imodintro
    unfold recvNestedAu
    iinv Hinv with Hi Hclose
    imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc2 Hi with Hi
    icases sspscInv_elim _ _ _ $$ Hi with ⟨%s, %sent, %recv, %pf, %cf, Hch, HsentI, HrecvI,
      %Hrel, Hm⟩
    ihave %Heq := dghostVar_agree _ _ _ _ _ $$ Hcons HrecvI
    simp only [Prod.mk.injEq] at Heq
    obtain ⟨rfl, rfl⟩ := Heq
    obtain ⟨Hrel, Hf⟩ := Hrel
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iexists s
    iframe Hch
    cases s with
    | SndCommit v =>
      dsimp only
      iintro Hoc
      imod dghostVar_update_halves (received ++ [v], false) _ _ _ $$ Hcons HrecvI with
        ⟨Hcons, HrecvI⟩
      simp only [sspscInvMatch]
      imod Hmask with -
      imod Hclose $$ [Hoc HsentI HrecvI] with -
      · inext
        iapply sspscInv_intro γ P R .Idle sent (received ++ [v]) pf false
          (by simpa [inflight] using Hrel) (by simp [sspscFlagsOk]) $$ Hoc HsentI HrecvI
        simp only [sspscInvMatch]
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
        simp only [sspscInvMatch, sspscConsumer]
        icases Hm with ⟨Hprod, (HR | Hc2)⟩
        · iintro Hoc
          imod dghostVar_update_halves (sent, false) _ _ _ $$ Hcons HrecvI with ⟨Hcons, HrecvI⟩
          imod Hmask with -
          imod Hclose $$ [Hoc HsentI HrecvI Hprod Hcons] with -
          · inext
            iapply sspscInv_intro γ P R (.Closed []) sent sent pf false (by simp [inflight])
              (by simp [sspscFlagsOk]) $$ Hoc HsentI HrecvI
            simp only [sspscInvMatch, sspscConsumer]
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
    imod dghostVar_update_halves (received ++ [v], false) _ _ _ $$ Hcons HrecvI with ⟨Hcons, HrecvI⟩
    simp only [sspscInvMatch]
    imod Hmask with -
    imod Hclose $$ [Hoc HsentI HrecvI] with -
    · inext
      iapply sspscInv_intro γ P R .RcvCommit sent (received ++ [v]) pf false
        (by simpa [inflight] using Hrel) (by simpa [sspscFlagsOk] using Hf.1) $$ Hoc HsentI HrecvI
      simp only [sspscInvMatch]
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
      simp only [sspscInvMatch, sspscConsumer]
      icases Hm with ⟨Hprod, (HR | Hc2)⟩
      · iintro Hoc
        imod Hmask with -
        imod Hclose $$ [Hoc HsentI HrecvI Hprod Hcons] with -
        · inext
          iapply sspscInv_intro γ P R (.Closed []) sent sent pf false (by simp [inflight])
            (by simp [sspscFlagsOk]) $$ Hoc HsentI HrecvI
          simp only [sspscInvMatch, sspscConsumer]
          isplitl [Hprod]
          · iexact Hprod
          · iright; iexact Hcons
        imodintro
        iapply Hcont
        simp only [Bool.false_eq_true, ↓reduceIte]
        iframe
      · iexfalso
        iapply dghostVar_three_halves $$ Hcons HrecvI Hc2
    | cons v rest => simp only [sspscInvMatch]; iexfalso; iexact Hm
  | _ => itrivial

/-- Synchronous SPSC receive operation with history tracking. -/
theorem wp_sspsc_receive (γ : SpscNames) (ch : Loc) (P : Int → V → IProp GF)
    (R : List V → IProp GF) (received : List V) :
    {{ isSspsc γ ch P R ∗ sspscConsumer γ received }}
      (App (Val (chan.receive t)) (Val #ch))
    {{ (v : V) (ok : Bool), RET (PairV #v #ok);
        (if ok then iprop(P received.length v ∗ sspscConsumer γ (received ++ [v]))
         else iprop(R received ∗ ⌜v = zero_val V⌝)) }} := by
  iintro %Φ ⟨#Hspsc, Hcons⟩ HΦ
  ihave #Hch : isChan ch γ.chanName V $$ [Hspsc]
  · unfold isSspsc; icases Hspsc with ⟨$, -⟩
  iapply chan.wp_receive ch γ.chanName $$ Hch
  iintro ⟨Hlc1, Hlc2, _, _⟩
  iapply sspsc_rcv_au γ ch P R received (fun v ok => Φ (PairV #v #ok)) $$ Hspsc [$Hlc1 $Hlc2]
    Hcons
  inext
  iintro %v %ok H
  iapply HΦ $$ %v %ok H

omit [IntoValTyped (GF := GF) V t] in
set_option maxHeartbeats 800000 in
theorem sspsc_send_au (γ : SpscNames) (ch : Loc) (P : Int → V → IProp GF) (R : List V → IProp GF)
    (sent : List V) (v : V) (Φ : IProp GF) :
    ⊢ isSspsc γ ch P R -∗ £ 1 ∗ £ 1 ∗ £ 1 -∗ sspscProducer γ sent ∗ P sent.length v -∗
      ▷ (sspscProducer γ (sent ++ [v]) -∗ Φ) -∗ sendAu γ.chanName v Φ := by
  unfold isSspsc sendAu
  iintro ⟨#Hchan, #Hinv⟩ ⟨Hlc1, Hlc2, Hlc3⟩ ⟨Hprod, HP⟩ Hcont
  imod lc_fupd_elim_later (E := ⊤) $$ Hlc1 Hcont with Hcont
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc2 Hi with Hi
  icases sspscInv_elim _ _ _ $$ Hi with ⟨%s, %sent0, %recv, %pf, %cf, Hch, HsentI, HrecvI, %Hrel, Hm⟩
  unfold sspscProducer
  ihave %Heq := dghostVar_agree _ _ _ _ _ $$ Hprod HsentI
  simp only [Prod.mk.injEq] at Heq
  obtain ⟨rfl, rfl⟩ := Heq
  obtain ⟨Hrel, Hf⟩ := Hrel
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists s
  iframe Hch
  cases s with
  | Buffered buff => simp only [sspscInvMatch]; iexfalso; iexact Hm
  | Idle =>
    dsimp only
    simp only [inflight, List.append_nil] at Hrel
    subst Hrel
    iintro Hoc
    imod dghostVar_update_halves (sent ++ [v], true) _ _ _ $$ Hprod HsentI with ⟨Hprod, HsentI⟩
    imod Hmask with -
    imod Hclose $$ [Hoc HsentI HrecvI HP] with -
    · inext
      iapply sspscInv_intro γ P R (.SndPending v) (sent ++ [v]) sent true cf (by simp [inflight])
        (by simp [sspscFlagsOk]) $$ Hoc HsentI HrecvI
      simp only [sspscInvMatch]
      iexact HP
    imodintro
    unfold sendNestedAu
    iinv Hinv with Hi Hclose
    imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc3 Hi with Hi
    icases sspscInv_elim _ _ _ $$ Hi with ⟨%s, %sent1, %recv1, %pf1, %cf1, Hch, HsentI, HrecvI,
      %Hrel, Hm⟩
    ihave %Heq := dghostVar_agree _ _ _ _ _ $$ Hprod HsentI
    simp only [Prod.mk.injEq] at Heq
    obtain ⟨rfl, rfl⟩ := Heq
    obtain ⟨Hrel, Hf⟩ := Hrel
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iexists s
    iframe Hch
    cases s with
    | RcvCommit =>
      dsimp only
      iintro Hoc
      imod dghostVar_update_halves (sent ++ [v], false) _ _ _ $$ Hprod HsentI with
        ⟨Hprod, HsentI⟩
      imod Hmask with -
      imod Hclose $$ [Hoc HsentI HrecvI] with -
      · inext
        iapply sspscInv_intro γ P R .Idle (sent ++ [v]) recv1 false cf1
          (by simpa [inflight] using Hrel) (by simp [sspscFlagsOk]) $$ Hoc HsentI HrecvI
        simp only [sspscInvMatch]
        itrivial
      imodintro
      iapply Hcont $$ Hprod
    | Closed d =>
      dsimp only
      cases d with
      | nil =>
        simp only [sspscInvMatch, sspscProducer]
        icases Hm with ⟨Hp2, -⟩
        iapply dghostVar_three_halves $$ Hprod HsentI Hp2
      | cons _ _ => simp only [sspscInvMatch]; iexfalso; iexact Hm
    | _ => itrivial
  | RcvPending =>
    dsimp only
    simp only [inflight, List.append_nil] at Hrel
    subst Hrel
    iintro Hoc
    imod dghostVar_update_halves (sent ++ [v], false) _ _ _ $$ Hprod HsentI with ⟨Hprod, HsentI⟩
    imod Hmask with -
    imod Hclose $$ [Hoc HsentI HrecvI HP] with -
    · inext
      iapply sspscInv_intro γ P R (.SndCommit v) (sent ++ [v]) sent false cf (by simp [inflight])
        (by simpa [sspscFlagsOk] using Hf.2) $$ Hoc HsentI HrecvI
      simp only [sspscInvMatch]
      iexact HP
    imodintro
    iapply Hcont $$ Hprod
  | Closed d =>
    dsimp only
    cases d with
    | nil =>
      simp only [sspscInvMatch, sspscProducer]
      icases Hm with ⟨Hp2, -⟩
      iapply dghostVar_three_halves $$ Hprod HsentI Hp2
    | cons _ _ => simp only [sspscInvMatch]; iexfalso; iexact Hm
  | _ => itrivial

/-- Synchronous SPSC send operation with history tracking. -/
theorem wp_sspsc_send (γ : SpscNames) (ch : Loc) (P : Int → V → IProp GF)
    (R : List V → IProp GF) (sent : List V) (v : V) :
    {{ isSspsc γ ch P R ∗ sspscProducer γ sent ∗ P sent.length v }}
      (App (App (Val (chan.send t)) (Val #ch)) (Val #v))
    {{ RET #(); sspscProducer γ (sent ++ [v]) }} := by
  iintro %Φ ⟨#Hspsc, Hprod, HP⟩ HΦ
  ihave #Hch : isChan ch γ.chanName V $$ [Hspsc]
  · unfold isSspsc; icases Hspsc with ⟨$, -⟩
  iapply chan.wp_send ch v γ.chanName $$ Hch
  iintro ⟨Hlc1, Hlc2, Hlc3, _⟩
  iapply sspsc_send_au γ ch P R sent v (Φ #()) $$ Hspsc [$Hlc1 $Hlc2 $Hlc3] [$Hprod $HP] HΦ

omit [IntoValTyped (GF := GF) V t] in
set_option maxHeartbeats 800000 in
theorem sspsc_close_au (γ : SpscNames) (ch : Loc) (P : Int → V → IProp GF) (R : List V → IProp GF)
    (sent : List V) (Φ : IProp GF) :
    ⊢ isSspsc γ ch P R -∗ £ 1 -∗ sspscProducer γ sent ∗ R sent -∗ ▷ Φ -∗
      closeAu γ.chanName V Φ := by
  unfold isSspsc closeAu
  iintro ⟨#Hchan, #Hinv⟩ Hlc1 ⟨Hprod, HR⟩ Hcont
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc1 Hi with Hi
  icases sspscInv_elim _ _ _ $$ Hi with ⟨%s, %sent0, %recv, %pf, %cf, Hch, HsentI, HrecvI, %Hrel, Hm⟩
  unfold sspscProducer
  ihave %Heq := dghostVar_agree _ _ _ _ _ $$ Hprod HsentI
  simp only [Prod.mk.injEq] at Heq
  obtain ⟨rfl, rfl⟩ := Heq
  obtain ⟨Hrel, Hf⟩ := Hrel
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists s
  iframe Hch
  cases s with
  | Buffered buff => simp only [sspscInvMatch]; iexfalso; iexact Hm
  | Idle =>
    dsimp only
    iintro Hoc
    imod Hmask with -
    imod Hclose $$ [Hoc HsentI HrecvI Hprod HR] with -
    · inext
      iapply sspscInv_intro γ P R (.Closed []) sent recv false cf (by simpa [inflight] using Hrel)
        (by simp [sspscFlagsOk]) $$ Hoc HsentI HrecvI
      simp only [sspscInvMatch, sspscProducer]
      isplitl [Hprod]
      · iexact Hprod
      · ileft; iexact HR
    imodintro
    iexact Hcont
  | Closed d =>
    dsimp only
    cases d with
    | nil =>
      simp only [sspscInvMatch, sspscProducer]
      icases Hm with ⟨Hp2, -⟩
      iapply dghostVar_three_halves $$ Hprod HsentI Hp2
    | cons _ _ => simp only [sspscInvMatch]; iexfalso; iexact Hm
  | _ => itrivial

/-- Close a synchronous SPSC channel. -/
theorem wp_sspsc_close (γ : SpscNames) (ch : Loc) (P : Int → V → IProp GF)
    (R : List V → IProp GF) (sent : List V) {ct : go.GoType} {dir : go.ChanDir}
    [ct ↓u go.ChannelType dir t] :
    {{ isSspsc γ ch P R ∗ sspscProducer γ sent ∗ R sent }}
      (App (Val #(functions go.close [ct])) (Val #ch))
    {{ RET #(); True }} := by
  iintro %Φ ⟨#Hspsc, Hprod, HR⟩ HΦ
  ihave #Hch : isChan ch γ.chanName V $$ [Hspsc]
  · unfold isSspsc; icases Hspsc with ⟨$, -⟩
  iapply chan.wp_close (ct := ct) ch γ.chanName $$ Hch
  iintro ⟨Hlc1, _, _, _⟩
  iapply sspsc_close_au γ ch P R sent (Φ #()) $$ Hspsc Hlc1 [$Hprod $HR]
  inext
  iapply HΦ
  itrivial

end sspsc

end Perennial
