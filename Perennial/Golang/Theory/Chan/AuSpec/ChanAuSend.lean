/-
Port of `new/golang/theory/chan/au_spec/chan_au_send.v`: specifications of the
channel model's `Cap`, `Len`, `TrySend`, `Send`, `tryClose` and `Close`.
-/
import Perennial.Golang.Theory.Chan.AuSpec.ChanAuBase

set_option linter.iris.style.nameCheck false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE
open github_com.mit_pdos.perennial.goose.model
open github_com.goose_lang.primitive (isMutex isMutex_unseal isMutexDef ownMutex ownMutex_unseal
  ownMutexDef Mutex.wp_Lock Mutex.wp_Unlock)

section atomic_specs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem_fn : GoSemanticsFunctions] [pre_sem : go.PreSemantics] [sem : go.ChanSemantics]
variable {V : Type} [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V] {t : go.GoType}
  [IntoValTyped (GF := GF) V t]

set_option goose.wp.extras true

omit [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V t] in
/-- `is_lock` is `isMutex` (the channel invariant is stated with `is_lock`, as in Rocq). -/
theorem isLock_eq_is_Mutex (m : Loc) (R : IProp GF) : isLock m R = isMutex m R := by
  rw [isMutex_unseal]; rfl

set_option maxHeartbeats 400000 in
theorem wp_Cap (ch : Loc) (γ : ChanNames) :
    {{ isChan (GF := GF) ch γ V }}
      (App (Val (ch @!! go.GoType.PointerType (channel.Channel t) @!! go!"Cap")) (Val #()))
    {{ RET #γ.chanCap; True }} := by
  wp_start as #Hch
  wp_auto
  ihave %Hnn := isChan_not_null _ _ _ $$ Hch
  rw [isChan_unseal]
  iNamed Hch
  wp_if_destruct
  · exact absurd rfl Hnn
  iapply HΦ
  itrivial

set_option maxHeartbeats 400000 in
theorem wp_Len (ch : Loc) (γ : ChanNames) :
    {{ isChan (GF := GF) ch γ V }}
      (App (Val (ch @!! go.GoType.PointerType (channel.Channel t) @!! go!"Len")) (Val #()))
    {{ (l : w64), RET #l; ⌜0 ≤ sint.Z l ∧ sint.Z l ≤ sint.Z γ.chanCap⌝ }} := by
  wp_start as #His
  wp_auto
  ihave %Hnn := isChan_not_null _ _ _ $$ His
  rw [isChan_unseal]
  iNamed His
  wp_if_destruct
  · exact absurd rfl Hnn
  rw [isLock_eq_is_Mutex] at *
  wp_apply Mutex.wp_Lock $$ [$lock] as ⟨Hlock, Hchan⟩
  iNamed Hchan
  cases s with
  | Buffered buffer =>
    iNamed phys
    wp_auto
    ihave %Hlen := ownSlice_len _ _ _ $$ slice
    simp only [chanLogical]
    ihave %Hsz := ownChan_buffer_size _ _ _ $$ offer
    wp_apply Mutex.wp_Unlock $$ [$lock $Hlock state buffer slice slice_cap offer]
    · iapply chanInvInner_intro _ _ _ (ChanPhysState.Buffered buffer)
      simp only [chanPhys, chanLogical]
      iframe
    iapply HΦ
    ipureintro
    word
  | Idle =>
    iNamed phys
    wp_auto
    ihave %Hlen := ownSlice_len _ _ _ $$ slice
    wp_apply Mutex.wp_Unlock $$ [$lock $Hlock state buffer slice slice_cap offer v]
    · iapply chanInvInner_intro _ _ _ (ChanPhysState.Idle)
      simp only [chanPhys]
      iframe
    iapply HΦ
    ipureintro
    simp at Hlen
    word
  | SndWait v =>
    iNamed phys
    wp_auto
    ihave %Hlen := ownSlice_len _ _ _ $$ slice
    wp_apply Mutex.wp_Unlock $$ [$lock $Hlock state buffer slice slice_cap offer v]
    · iapply chanInvInner_intro _ _ _ (ChanPhysState.SndWait v)
      simp only [chanPhys]
      iframe
    iapply HΦ
    ipureintro
    simp at Hlen
    word
  | RcvWait =>
    iNamed phys
    wp_auto
    ihave %Hlen := ownSlice_len _ _ _ $$ slice
    wp_apply Mutex.wp_Unlock $$ [$lock $Hlock state buffer slice slice_cap offer v]
    · iapply chanInvInner_intro _ _ _ (ChanPhysState.RcvWait)
      simp only [chanPhys]
      iframe
    iapply HΦ
    ipureintro
    simp at Hlen
    word
  | SndDone v =>
    iNamed phys
    wp_auto
    ihave %Hlen := ownSlice_len _ _ _ $$ slice
    wp_apply Mutex.wp_Unlock $$ [$lock $Hlock state buffer slice slice_cap offer v]
    · iapply chanInvInner_intro _ _ _ (ChanPhysState.SndDone v)
      simp only [chanPhys]
      iframe
    iapply HΦ
    ipureintro
    simp at Hlen
    word
  | RcvDone =>
    iNamed phys
    wp_auto
    ihave %Hlen := ownSlice_len _ _ _ $$ slice
    wp_apply Mutex.wp_Unlock $$ [$lock $Hlock state buffer slice slice_cap offer v]
    · iapply chanInvInner_intro _ _ _ (ChanPhysState.RcvDone)
      simp only [chanPhys]
      iframe
    iapply HΦ
    ipureintro
    simp at Hlen
    word
  | Closed buffer =>
    cases buffer with
    | nil =>
      iNamed phys
      wp_auto
      ihave %Hlen := ownSlice_len _ _ _ $$ slice
      wp_apply Mutex.wp_Unlock $$ [$lock $Hlock state buffer slice slice_cap offer]
      · iapply chanInvInner_intro _ _ _ (ChanPhysState.Closed [])
        simp only [chanPhys]
        iframe
      iapply HΦ
      ipureintro
      simp at Hlen
      word
    | cons x buffer =>
      iNamed phys
      simp only [chanLogical]
      ihave %Hsz := ownChan_drain_size _ _ _ $$ offer
      wp_auto
      ihave %Hlen := ownSlice_len _ _ _ $$ slice
      wp_apply Mutex.wp_Unlock $$ [$lock $Hlock state buffer slice slice_cap offer]
      · iapply chanInvInner_intro _ _ _ (ChanPhysState.Closed (x :: buffer))
        simp only [chanPhys, chanLogical]
        iframe
      iapply HΦ
      ipureintro
      word

set_option maxHeartbeats 400000 in
theorem wp_TrySend_blocking (ch : Loc) (v : V) (γ : ChanNames) :
    ⊢ ∀ Φ : val → IProp GF, isChan ch γ V -∗ (sendAu γ v (Φ #true) ∧ Φ #false) -∗
      WP (App (App (Val (ch @!! go.GoType.PointerType (channel.Channel t) @!! go!"TrySend")) (Val #v))
        (Val #true)) {{ Φ }} := by
  wp_start as Hunb
  rw [isChan_unseal]
  iNamed Hunb
  wp_auto_lc 5
  rw [isLock_eq_is_Mutex] at *
  wp_apply Mutex.wp_Lock $$ [$lock] as ⟨Hlock, Hchan⟩
  iNamed Hchan
  cases s with
  | Buffered buffer =>
    iNamed phys
    simp only [chanLogical]
    ihave %Hcv := ownChan_cap_valid _ _ _ $$ offer
    ihave %Hlen := ownSlice_len _ _ _ $$ slice
    wp_auto
    wp_if_destruct
    · wp_apply wp_slice_literal (V := V) [v]
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, _⟩
      wp_auto
      wp_apply wp_slice_append $$ [slice slice_cap Hsl] with %fr ⟨Hfr, Hfrsl, Hsl⟩
      · iframe
      icases HΦ with ⟨HΦ, -⟩
      iapply fupd_wp
      unfold sendAu
      imod HΦ with HΦ
      imod lc_fupd_elim_later $$ Hlc1 HΦ with HΦ
      iNamed HΦ
      ihave %Heq := ownChan_agree _ _ _ _ $$ offer Hoc
      subst Heq
      imod ownChan_halves_update _ _ (chanstate.t.Buffered (buffer ++ [v])) _ _ ?_ $$ Hoc offer
        with ⟨Hgv1, Hgv2⟩
      · simp only [ChanCapValid] at Hcv ⊢
        simp only [List.length_append, List.length_cons, List.length_nil]
        constructor <;> word
      dsimp only
      imod Hcont $$ Hgv1 with Hstep
      imodintro
      wp_apply Mutex.wp_Unlock $$ [$lock $Hlock state buffer Hfr Hfrsl Hgv2]
      · iapply chanInvInner_intro _ _ _ (ChanPhysState.Buffered (buffer ++ [v]))
        simp only [chanPhys, chanLogical]
        iframe
      iexact Hstep
    · wp_apply Mutex.wp_Unlock $$ [$lock $Hlock state buffer slice slice_cap offer]
      · iapply chanInvInner_intro _ _ _ (ChanPhysState.Buffered buffer)
        simp only [chanPhys, chanLogical]
        iframe
      icases HΦ with ⟨-, HΦ⟩
      iexact HΦ
  | Idle =>
    iNamed phys
    chan_unfold_consts
    wp_auto
    simp only [chanLogical]
    iNamed offer
    ihave %HcvIdle := ownChan_cap_valid _ _ _ $$ offer
    simp only [ChanCapValid] at HcvIdle
    imod offer_idle_to_send γ V iprop(sendAu γ v (Φ #true) ∧ Φ #false) (Φ #true) v $$ Hoffer
      with ⟨offer1, offer2⟩
    wp_apply Mutex.wp_Unlock $$ [$lock $Hlock state v slice slice_cap buffer offer1 Hpred offer HΦ]
    · iapply chanInvInner_intro _ _ _ (ChanPhysState.SndWait v)
      simp only [chanPhys, chanLogical]
      isplitl [state v slice slice_cap buffer]
      · iexists slice_val
        iframe
      iexists iprop(sendAu γ v (Φ #true) ∧ Φ #false), (Φ #true), Φr0
      iframe
      iintro H
      icases H with ⟨H, -⟩
      iexact H
    wp_apply Mutex.wp_Lock $$ [$lock] as ⟨Hlock, Hchan⟩
    iNamed Hchan
    cases s with
    | Buffered buff =>
      simp only [chanLogical]
      ihave %Hcv2 := ownChan_cap_valid _ _ _ $$ offer
      simp only [ChanCapValid] at Hcv2
      exfalso; word
    | Idle =>
      simp only [chanLogical]
      iNamed offer
      iexfalso
      iapply savedOffer_half_full_invalid $$ offer2 Hoffer
    | SndWait v' =>
      iNamed phys
      simp only [chanLogical]
      iNamed offer
      imod savedOffer_lc_agree γ V _ _ _ _ _ _ $$ Hlc1 offer2 Hoffer with ⟨%Heq, #Hpeq, #H, H1⟩
      wp_auto
      wp_apply Mutex.wp_Unlock $$ [$lock $Hlock state v slice slice_cap buffer Hpred H1 offer]
      · iapply chanInvInner_intro _ _ _ (ChanPhysState.Idle)
        simp only [chanPhys, chanLogical]
        isplitl [state v slice slice_cap buffer]
        · iexists _, slice_val
          iframe
        iexists Φr0
        iframe
      ihave HP := internal_eq_rewrite_wand $$ Hpeq HP
      icases HP with ⟨-, HP⟩
      iexact HP
    | RcvWait =>
      simp only [chanLogical]
      iNamed offer
      ihave ⟨%Heq, -⟩ := savedOffer_agree γ V _ _ _ _ _ _ _ _ $$ [$offer2 $Hoffer]
      cases Heq
    | SndDone v' =>
      simp only [chanLogical]
      iNamed offer
      ihave ⟨%Heq, -⟩ := savedOffer_agree γ V _ _ _ _ _ _ _ _ $$ [$offer2 $Hoffer]
      cases Heq
    | RcvDone =>
      iNamed phys
      simp only [chanLogical]
      iNamed offer
      iapply fupd_wp
      unfold sendNestedAu
      imod Hau with Hau
      imod lc_fupd_elim_later $$ Hlc1 Hau with Hau
      iNamed Hau
      ihave %Hseq := ownChan_agree _ _ _ _ $$ Hocinner offer
      subst Hseq
      imod ownChan_halves_update _ _ chanstate.t.Idle _ _ HcvIdle $$ Hocinner offer with ⟨Hgv1, Hgv2⟩
      dsimp only
      imod Hcontinner $$ Hgv1 with Hcont
      imodintro
      imod savedOffer_lc_agree γ V _ _ _ _ _ _ $$ Hlc2 offer2 Hoffer with ⟨%Heq, #Hpeq, #H, H1⟩
      wp_auto
      wp_apply Mutex.wp_Unlock $$ [$lock $Hlock state v slice slice_cap buffer Hpred H1 Hgv2]
      · iapply chanInvInner_intro _ _ _ (ChanPhysState.Idle)
        simp only [chanPhys, chanLogical]
        isplitl [state v slice slice_cap buffer]
        · iexists _, slice_val
          iframe
        iexists Φr0
        iframe
      iapply internal_eq_rewrite_wand $$ H Hcont
    | Closed buff =>
      cases buff with
      | nil =>
        simp only [chanLogical]
        icases offer with ⟨Hoc, Hoffer⟩
        have hcap0 : γ.chanCap = W64 0 := by word
        ispecialize Hoffer $$ %hcap0
        iexfalso
        iapply savedOffer_half_full_invalid $$ offer2 Hoffer
      | cons x xs =>
        simp only [chanLogical]
        ihave %Hcv2 := ownChan_cap_valid _ _ _ $$ offer
        simp only [ChanCapValid] at Hcv2
        exfalso; word
  | SndWait v' =>
    iNamed phys
    wp_auto
    wp_apply Mutex.wp_Unlock $$ [$lock $Hlock state v slice slice_cap buffer offer]
    · iapply chanInvInner_intro _ _ _ (ChanPhysState.SndWait v')
      simp only [chanPhys]
      iframe
    icases HΦ with ⟨-, HΦ⟩
    iexact HΦ
  | RcvWait =>
    -- NOTE (Rocq): this leaves no freedom for picking the linearization order.
    iNamed phys
    chan_unfold_consts
    wp_auto
    simp only [chanLogical]
    iNamed offer
    ihave HP := Hau $$ HP
    iapply fupd_wp
    unfold recvAu
    imod HP with HP
    imod lc_fupd_elim_later $$ Hlc1 HP with HP
    iNamed HP
    ihave %Hseq := ownChan_agree _ _ _ _ $$ Hoc offer
    subst Hseq
    ihave %HcvIdle := ownChan_cap_valid _ _ _ $$ offer
    simp only [ChanCapValid] at HcvIdle
    imod ownChan_halves_update _ _ chanstate.t.RcvPending _ _ HcvIdle $$ offer Hoc with ⟨Hgv1, Hgv2⟩
    dsimp only
    imod Hcont $$ Hgv2 with Hcont1
    icases HΦ with ⟨HΦ, -⟩
    unfold sendAu
    imod HΦ with HΦ
    imod lc_fupd_elim_later $$ Hlc2 HΦ with HΦ
    iNamed HΦ
    ihave %Hseq := ownChan_agree _ _ _ _ $$ Hgv1 Hoc
    subst Hseq
    imod ownChan_halves_update _ _ (chanstate.t.SndCommit v) _ _ HcvIdle $$ Hgv1 Hoc
      with ⟨Hgv1, Hgv2⟩
    dsimp only
    imod Hcont $$ Hgv2 with Hcont
    imodintro
    wp_apply Mutex.wp_Unlock $$ [$lock $Hlock state v slice slice_cap buffer Hgv1 Hcont1 Hpred Hoffer]
    · iapply chanInvInner_intro _ _ _ (ChanPhysState.SndDone v)
      simp only [chanPhys, chanLogical]
      iframe
    iexact Hcont
  | SndDone v' =>
    iNamed phys
    wp_auto
    wp_apply Mutex.wp_Unlock $$ [$lock $Hlock state v slice slice_cap buffer offer]
    · iapply chanInvInner_intro _ _ _ (ChanPhysState.SndDone v')
      simp only [chanPhys]
      iframe
    icases HΦ with ⟨-, HΦ⟩
    iexact HΦ
  | RcvDone =>
    iNamed phys
    wp_auto
    wp_apply Mutex.wp_Unlock $$ [$lock $Hlock state v slice slice_cap buffer offer]
    · iapply chanInvInner_intro _ _ _ (ChanPhysState.RcvDone)
      simp only [chanPhys]
      iframe
    icases HΦ with ⟨-, HΦ⟩
    iexact HΦ
  | Closed buff =>
    icases HΦ with ⟨HΦ, -⟩
    iapply fupd_wp
    unfold sendAu
    imod HΦ with HΦ
    imod lc_fupd_elim_later $$ Hlc1 HΦ with HΦ
    iNamed HΦ
    cases buff with
    | nil =>
      simp only [chanLogical]
      icases offer with ⟨offer1, -⟩
      ihave %Hseq := ownChan_agree _ _ _ _ $$ Hoc offer1
      subst Hseq
      dsimp only
      iexfalso
      iexact Hcont
    | cons x xs =>
      simp only [chanLogical]
      ihave %Hseq := ownChan_agree _ _ _ _ $$ Hoc offer
      subst Hseq
      dsimp only
      iexfalso
      iexact Hcont

set_option maxHeartbeats 400000 in
theorem wp_TrySend_nonblocking (ch : Loc) (v : V) (γ : ChanNames) :
    ⊢ ∀ Φ : val → IProp GF, isChan ch γ V -∗ nonblockingSendAu γ v (Φ #true) (Φ #false) -∗
      WP (App (App (Val (ch @!! go.GoType.PointerType (channel.Channel t) @!! go!"TrySend")) (Val #v))
        (Val #false)) {{ Φ }} := by
  wp_start as Hunb
  rw [isChan_unseal]
  iNamed Hunb
  wp_auto_lc 5
  rw [isLock_eq_is_Mutex] at *
  wp_apply Mutex.wp_Lock $$ [$lock] as ⟨Hlock, Hchan⟩
  iNamed Hchan
  unfold nonblockingSendAu nonblockingSendAuInner
  cases s with
  | Buffered buffer =>
    iNamed phys
    simp only [chanLogical]
    ihave %Hcv := ownChan_cap_valid _ _ _ $$ offer
    ihave %Hlen := ownSlice_len _ _ _ $$ slice
    wp_auto
    wp_if_destruct
    · icases HΦ with ⟨HΦ, -⟩
      iapply fupd_wp
      imod HΦ with HΦ
      imod lc_fupd_elim_later $$ Hlc1 HΦ with HΦ
      iNamed HΦ
      ihave %Heq := ownChan_agree _ _ _ _ $$ offer Hoc
      subst Heq
      imod ownChan_halves_update _ _ (chanstate.t.Buffered (buffer ++ [v])) _ _ ?_ $$ Hoc offer
        with ⟨Hgv1, Hgv2⟩
      · simp only [ChanCapValid] at Hcv ⊢
        simp only [List.length_append, List.length_cons, List.length_nil]
        constructor <;> word
      dsimp only
      imod Hcont $$ Hgv1 with Hstep
      imodintro
      wp_apply wp_slice_literal (V := V) [v]
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, _⟩
      wp_auto
      wp_apply wp_slice_append $$ [slice slice_cap Hsl] with %fr ⟨Hfr, Hfrsl, Hsl⟩
      · iframe
      wp_apply Mutex.wp_Unlock $$ [$lock $Hlock state buffer Hfr Hfrsl Hgv2]
      · iapply chanInvInner_intro _ _ _ (ChanPhysState.Buffered (buffer ++ [v]))
        simp only [chanPhys, chanLogical]
        iframe
      iexact Hstep
    · wp_apply Mutex.wp_Unlock $$ [$lock $Hlock state buffer slice slice_cap offer]
      · iapply chanInvInner_intro _ _ _ (ChanPhysState.Buffered buffer)
        simp only [chanPhys, chanLogical]
        iframe
      icases HΦ with ⟨-, HΦ⟩
      iexact HΦ
  | Idle =>
    iNamed phys
    wp_auto
    wp_apply Mutex.wp_Unlock $$ [$lock $Hlock state v slice slice_cap buffer offer]
    · iapply chanInvInner_intro _ _ _ (ChanPhysState.Idle)
      simp only [chanPhys]
      iframe
    icases HΦ with ⟨-, HΦ⟩
    iexact HΦ
  | SndWait v' =>
    iNamed phys
    wp_auto
    wp_apply Mutex.wp_Unlock $$ [$lock $Hlock state v slice slice_cap buffer offer]
    · iapply chanInvInner_intro _ _ _ (ChanPhysState.SndWait v')
      simp only [chanPhys]
      iframe
    icases HΦ with ⟨-, HΦ⟩
    iexact HΦ
  | RcvWait =>
    iNamed phys
    chan_unfold_consts
    wp_auto
    simp only [chanLogical]
    iNamed offer
    ihave HP := Hau $$ HP
    iapply fupd_wp
    unfold recvAu
    imod HP with HP
    imod lc_fupd_elim_later $$ Hlc1 HP with HP
    iNamed HP
    ihave %Hseq := ownChan_agree _ _ _ _ $$ Hoc offer
    subst Hseq
    ihave %HcvIdle := ownChan_cap_valid _ _ _ $$ offer
    simp only [ChanCapValid] at HcvIdle
    imod ownChan_halves_update _ _ chanstate.t.RcvPending _ _ HcvIdle $$ offer Hoc with ⟨Hgv1, Hgv2⟩
    dsimp only
    imod Hcont $$ Hgv2 with Hcont1
    icases HΦ with ⟨HΦ, -⟩
    imod HΦ with HΦ
    imod lc_fupd_elim_later $$ Hlc2 HΦ with HΦ
    iNamed HΦ
    ihave %Hseq := ownChan_agree _ _ _ _ $$ Hgv1 Hoc
    subst Hseq
    imod ownChan_halves_update _ _ (chanstate.t.SndCommit v) _ _ HcvIdle $$ Hgv1 Hoc
      with ⟨Hgv1, Hgv2⟩
    dsimp only
    imod Hcont $$ Hgv2 with Hcont
    imodintro
    wp_apply Mutex.wp_Unlock $$ [$lock $Hlock state v slice slice_cap buffer Hgv1 Hcont1 Hpred Hoffer]
    · iapply chanInvInner_intro _ _ _ (ChanPhysState.SndDone v)
      simp only [chanPhys, chanLogical]
      iframe
    iexact Hcont
  | SndDone v' =>
    iNamed phys
    wp_auto
    wp_apply Mutex.wp_Unlock $$ [$lock $Hlock state v slice slice_cap buffer offer]
    · iapply chanInvInner_intro _ _ _ (ChanPhysState.SndDone v')
      simp only [chanPhys]
      iframe
    icases HΦ with ⟨-, HΦ⟩
    iexact HΦ
  | RcvDone =>
    iNamed phys
    wp_auto
    wp_apply Mutex.wp_Unlock $$ [$lock $Hlock state v slice slice_cap buffer offer]
    · iapply chanInvInner_intro _ _ _ (ChanPhysState.RcvDone)
      simp only [chanPhys]
      iframe
    icases HΦ with ⟨-, HΦ⟩
    iexact HΦ
  | Closed buff =>
    icases HΦ with ⟨HΦ, -⟩
    iapply fupd_wp
    imod HΦ with HΦ
    imod lc_fupd_elim_later $$ Hlc1 HΦ with HΦ
    iNamed HΦ
    cases buff with
    | nil =>
      simp only [chanLogical]
      icases offer with ⟨offer1, -⟩
      ihave %Hseq := ownChan_agree _ _ _ _ $$ Hoc offer1
      subst Hseq
      dsimp only
      iexfalso
      iexact Hcont
    | cons x xs =>
      simp only [chanLogical]
      ihave %Hseq := ownChan_agree _ _ _ _ $$ Hoc offer
      subst Hseq
      dsimp only
      iexfalso
      iexact Hcont

set_option maxHeartbeats 400000 in
theorem wp_TrySend_nonblocking_alt (ch : Loc) (v : V) (γ : ChanNames) :
    ⊢ ∀ Φ : val → IProp GF, isChan ch γ V -∗ nonblockingSendAuAlt γ v (Φ #true) (Φ #false) -∗
      WP (App (App (Val (ch @!! go.GoType.PointerType (channel.Channel t) @!! go!"TrySend")) (Val #v))
        (Val #false)) {{ Φ }} := by
  wp_start as Hunb
  rw [isChan_unseal]
  iNamed Hunb
  wp_auto_lc 5
  rw [isLock_eq_is_Mutex] at *
  wp_apply Mutex.wp_Lock $$ [$lock] as ⟨Hlock, Hchan⟩
  iNamed Hchan
  unfold nonblockingSendAuAlt
  cases s with
  | Buffered buffer =>
    iNamed phys
    simp only [chanLogical]
    ihave %Hcv := ownChan_cap_valid _ _ _ $$ offer
    ihave %Hlen := ownSlice_len _ _ _ $$ slice
    wp_auto
    wp_if_destruct
    · iapply fupd_wp
      imod HΦ with HΦ
      imod lc_fupd_elim_later $$ Hlc1 HΦ with HΦ
      iNamed HΦ
      ihave %Heq := ownChan_agree _ _ _ _ $$ offer Hoc
      subst Heq
      dsimp only
      rw [ite_eq_left (by word)]
      imod ownChan_halves_update _ _ (chanstate.t.Buffered (buffer ++ [v])) _ _ ?_ $$ Hoc offer
        with ⟨Hgv1, Hgv2⟩
      · simp only [ChanCapValid] at Hcv ⊢
        simp only [List.length_append, List.length_cons, List.length_nil]
        constructor <;> word
      imod Hcont $$ Hgv1 with Hstep
      imodintro
      wp_apply wp_slice_literal (V := V) [v]
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, _⟩
      wp_auto
      wp_apply wp_slice_append $$ [slice slice_cap Hsl] with %fr ⟨Hfr, Hfrsl, Hsl⟩
      · iframe
      wp_apply Mutex.wp_Unlock $$ [$lock $Hlock state buffer Hfr Hfrsl Hgv2]
      · iapply chanInvInner_intro _ _ _ (ChanPhysState.Buffered (buffer ++ [v]))
        simp only [chanPhys, chanLogical]
        iframe
      iexact Hstep
    · iapply fupd_wp
      imod HΦ with HΦ
      imod lc_fupd_elim_later $$ Hlc1 HΦ with HΦ
      iNamed HΦ
      ihave %Heq := ownChan_agree _ _ _ _ $$ offer Hoc
      subst Heq
      dsimp only
      rw [ite_eq_right (by word)]
      imod Hcont $$ Hoc with HΦ
      imodintro
      wp_apply Mutex.wp_Unlock $$ [$lock $Hlock state buffer slice slice_cap offer]
      · iapply chanInvInner_intro _ _ _ (ChanPhysState.Buffered buffer)
        simp only [chanPhys, chanLogical]
        iframe
      iexact HΦ
  | Idle =>
    iNamed phys
    wp_auto
    iapply fupd_wp
    imod HΦ with HΦ
    imod lc_fupd_elim_later $$ Hlc1 HΦ with HΦ
    iNamed HΦ
    simp only [chanLogical]
    iNamed offer
    ihave %Hseq := ownChan_agree _ _ _ _ $$ Hoc offer
    subst Hseq
    dsimp only
    imod Hcont $$ Hoc with HΦ
    imodintro
    wp_apply Mutex.wp_Unlock $$ [$lock $Hlock state v slice slice_cap buffer Hoffer Hpred offer]
    · iapply chanInvInner_intro _ _ _ (ChanPhysState.Idle)
      simp only [chanPhys, chanLogical]
      isplitl [state v slice slice_cap buffer]
      · iframe
      iexists Φr0
      iframe
    iexact HΦ
  | SndWait v' =>
    iNamed phys
    wp_auto
    iapply fupd_wp
    imod HΦ with HΦ
    imod lc_fupd_elim_later $$ Hlc1 HΦ with HΦ
    iNamed HΦ
    simp only [chanLogical]
    iNamed offer
    ihave %Hseq := ownChan_agree _ _ _ _ $$ Hoc offer
    subst Hseq
    dsimp only
    imod Hcont $$ Hoc with HΦ
    imodintro
    wp_apply Mutex.wp_Unlock $$ [$lock $Hlock state v slice slice_cap buffer Hoffer HP Hpred Hau offer]
    · iapply chanInvInner_intro _ _ _ (ChanPhysState.SndWait v')
      simp only [chanPhys, chanLogical]
      isplitl [state v slice slice_cap buffer]
      · iframe
      iexists P0, Φ0, Φr0
      iframe
    iexact HΦ
  | RcvWait =>
    iNamed phys
    chan_unfold_consts
    wp_auto
    simp only [chanLogical]
    iNamed offer
    ihave HP := Hau $$ HP
    iapply fupd_wp
    unfold recvAu
    imod HP with HP
    imod lc_fupd_elim_later $$ Hlc1 HP with HP
    iNamed HP
    ihave %Hseq := ownChan_agree _ _ _ _ $$ Hoc offer
    subst Hseq
    ihave %HcvIdle := ownChan_cap_valid _ _ _ $$ offer
    simp only [ChanCapValid] at HcvIdle
    imod ownChan_halves_update _ _ chanstate.t.RcvPending _ _ HcvIdle $$ offer Hoc with ⟨Hgv1, Hgv2⟩
    dsimp only
    imod Hcont $$ Hgv2 with Hcont1
    imod HΦ with HΦ
    imod lc_fupd_elim_later $$ Hlc2 HΦ with HΦ
    iNamed HΦ
    ihave %Hseq := ownChan_agree _ _ _ _ $$ Hgv1 Hoc
    subst Hseq
    imod ownChan_halves_update _ _ (chanstate.t.SndCommit v) _ _ HcvIdle $$ Hgv1 Hoc
      with ⟨Hgv1, Hgv2⟩
    dsimp only
    imod Hcont $$ Hgv2 with Hcont
    imodintro
    wp_apply Mutex.wp_Unlock $$ [$lock $Hlock state v slice slice_cap buffer Hgv1 Hcont1 Hpred Hoffer]
    · iapply chanInvInner_intro _ _ _ (ChanPhysState.SndDone v)
      simp only [chanPhys, chanLogical]
      iframe
    iexact Hcont
  | SndDone v' =>
    iNamed phys
    wp_auto
    iapply fupd_wp
    imod HΦ with HΦ
    imod lc_fupd_elim_later $$ Hlc1 HΦ with HΦ
    iNamed HΦ
    simp only [chanLogical]
    iNamed offer
    ihave %Hseq := ownChan_agree _ _ _ _ $$ Hoc offer
    subst Hseq
    dsimp only
    imod Hcont $$ Hoc with HΦ
    imodintro
    wp_apply Mutex.wp_Unlock $$ [$lock $Hlock state v slice slice_cap buffer Hoffer Hpred Hau offer]
    · iapply chanInvInner_intro _ _ _ (ChanPhysState.SndDone v')
      simp only [chanPhys, chanLogical]
      isplitl [state v slice slice_cap buffer]
      · iframe
      iexists P0, Φr0
      iframe
    iexact HΦ
  | RcvDone =>
    iNamed phys
    wp_auto
    iapply fupd_wp
    imod HΦ with HΦ
    imod lc_fupd_elim_later $$ Hlc1 HΦ with HΦ
    iNamed HΦ
    simp only [chanLogical]
    iNamed offer
    ihave %Hseq := ownChan_agree _ _ _ _ $$ Hoc offer
    subst Hseq
    dsimp only
    imod Hcont $$ Hoc with HΦ
    imodintro
    wp_apply Mutex.wp_Unlock $$ [$lock $Hlock state v slice slice_cap buffer Hoffer Hpred Hau offer]
    · iapply chanInvInner_intro _ _ _ (ChanPhysState.RcvDone)
      simp only [chanPhys, chanLogical]
      isplitl [state v slice slice_cap buffer]
      · iframe
      iexists P0, Φ0, Φr0, v1
      iframe
    iexact HΦ
  | Closed buff =>
    iapply fupd_wp
    imod HΦ with HΦ
    imod lc_fupd_elim_later $$ Hlc1 HΦ with HΦ
    iNamed HΦ
    cases buff with
    | nil =>
      simp only [chanLogical]
      icases offer with ⟨offer1, -⟩
      ihave %Hseq := ownChan_agree _ _ _ _ $$ Hoc offer1
      subst Hseq
      dsimp only
      iexfalso
      iexact Hcont
    | cons x xs =>
      simp only [chanLogical]
      ihave %Hseq := ownChan_agree _ _ _ _ $$ Hoc offer
      subst Hseq
      dsimp only
      iexfalso
      iexact Hcont

theorem wp_TrySend (ch : Loc) (v : V) (γ : ChanNames) (blocking : Bool) :
    ⊢ ∀ Φ : val → IProp GF, isChan ch γ V -∗
      (if blocking then iprop(sendAu γ v (Φ #true) ∧ Φ #false)
       else iprop(nonblockingSendAu γ v (Φ #true) (Φ #false) ∨
         nonblockingSendAuAlt γ v (Φ #true) (Φ #false))) -∗
      WP (App (App (Val (ch @!! go.GoType.PointerType (channel.Channel t) @!! go!"TrySend")) (Val #v))
        (Val #blocking)) {{ Φ }} := by
  iintro %Φ #Hch HΦ
  cases blocking with
  | true =>
    simp only [↓reduceIte]
    iapply wp_TrySend_blocking $$ Hch HΦ
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases HΦ with (HΦ | HΦ)
    · iapply wp_TrySend_nonblocking $$ Hch HΦ
    · iapply wp_TrySend_nonblocking_alt $$ Hch HΦ

set_option maxHeartbeats 400000 in
theorem wp_Send (ch : Loc) (v : V) (γ : ChanNames) :
    ⊢ ∀ Φ : val → IProp GF, isChan ch γ V -∗
      (£ 1 ∗ £ 1 ∗ £ 1 ∗ £ 1 -∗ sendAu γ v (Φ #())) -∗
      WP (App (Val (ch @!! go.GoType.PointerType (channel.Channel t) @!! go!"Send")) (Val #v)) {{ Φ }} := by
  wp_start as #Hic
  ihave %Hnn := isChan_not_null _ _ _ $$ Hic
  wp_auto_lc 4
  ispecialize HΦ $$ [Hlc1 Hlc2 Hlc3 Hlc4]
  · iframe
  wp_if_destruct
  · exact absurd rfl Hnn
  wp_for
  wp_apply wp_TrySend ch v γ true $$ Hic
  simp only [↓reduceIte]
  isplit
  · iapply sendAu_wand $$ HΦ
    iintro HΦ
    wp_auto
    simp only [val_bool_eq, Bool.false_eq_true, decide_false, decide_true, ↓reduceIte]
    wp_auto
    iexact HΦ
  · wp_auto
    simp only [val_bool_eq, Bool.false_eq_true, decide_false, decide_true, ↓reduceIte]
    wp_auto
    wp_for_post
    iframe

/-- Demo of a simple-to-understand AU (Rocq: `#[local]`). -/
theorem wp_BlockingSend (ch : Loc) (v : V) (γ : ChanNames) (Hcapnz : sint.Z γ.chanCap > 0) :
    ⊢ ∀ Φ : val → IProp GF, isChan ch γ V -∗
      (£ 1 ∗ £ 1 ∗ £ 1 ∗ £ 1 -∗ bufferedSendAu γ v (Φ #())) -∗
      WP (App (Val (ch @!! go.GoType.PointerType (channel.Channel t) @!! go!"Send")) (Val #v)) {{ Φ }} := by
  iintro %Φ #Hunb HΦ
  iapply wp_Send $$ Hunb
  iintro Hlc
  ispecialize HΦ $$ Hlc
  unfold bufferedSendAu sendAu
  imod HΦ with HΦ
  imodintro
  inext
  iNamed HΦ
  ihave %Hcv := ownChan_cap_valid _ _ _ $$ Hoc
  iexists s
  iframe Hoc
  rcases s with _ | _ | _ | _ | _ | _ | _
  all_goals first
    | iexact Hcont
    | (exfalso; simp only [ChanCapValid] at Hcv; word)

set_option maxHeartbeats 400000 in
theorem wp_tryClose (ch : Loc) (γ : ChanNames) :
    ⊢ ∀ Φ : val → IProp GF, isChan ch γ V -∗ (closeAu γ V (Φ #true) ∧ Φ #false) -∗
      WP (App (Val (ch @!! go.GoType.PointerType (channel.Channel t) @!! go!"tryClose")) (Val #())) {{ Φ }} := by
  wp_start as #Hunb
  rw [isChan_unseal]
  iNamed Hunb
  chan_unfold_consts
  wp_auto_lc 1
  rw [isLock_eq_is_Mutex] at *
  wp_apply Mutex.wp_Lock $$ [$lock] as ⟨Hlock, Hchan⟩
  iNamed Hchan
  cases s with
  | Buffered buffer =>
    iNamed phys
    simp only [chanLogical]
    ihave %Hcv := ownChan_cap_valid _ _ _ $$ offer
    simp only [ChanCapValid] at Hcv
    wp_auto
    icases HΦ with ⟨HΦ, -⟩
    iapply fupd_wp
    unfold closeAu
    imod HΦ with HΦ
    imod lc_fupd_elim_later $$ Hlc1 HΦ with HΦ
    iNamed HΦ
    ihave %Heq := ownChan_agree _ _ _ _ $$ Hocinner offer
    subst Heq
    imod ownChan_halves_update _ _ (chanstate.t.Closed buffer) _ _ ?_ $$ Hocinner offer
      with ⟨Hgv1, Hgv2⟩
    · cases buffer <;> simp only [ChanCapValid] <;> word
    dsimp only
    imod Hcontinner $$ Hgv1 with HΦ
    imodintro
    wp_apply Mutex.wp_Unlock $$ [$lock $Hlock state slice slice_cap buffer Hgv2]
    · iapply chanInvInner_intro _ _ _ (ChanPhysState.Closed buffer)
      cases buffer with
      | nil =>
        simp only [chanPhys, chanLogical]
        iframe
        iintro %Hcap0
        exfalso
        rw [Hcap0] at Hcv
        exact absurd Hcv.2 (by decide)
      | cons x xs =>
        simp only [chanPhys, chanLogical]
        iframe
    iexact HΦ
  | Idle =>
    iNamed phys
    simp only [chanLogical]
    iNamed offer
    ihave %Hcv := ownChan_cap_valid _ _ _ $$ offer
    simp only [ChanCapValid] at Hcv
    wp_auto
    icases HΦ with ⟨HΦ, -⟩
    iapply fupd_wp
    unfold closeAu
    imod HΦ with HΦ
    imod lc_fupd_elim_later $$ Hlc1 HΦ with HΦ
    iNamed HΦ
    ihave %Heq := ownChan_agree _ _ _ _ $$ Hocinner offer
    subst Heq
    imod ownChan_halves_update _ _ (chanstate.t.Closed []) _ _ ?_ $$ Hocinner offer
      with ⟨Hgv1, Hgv2⟩
    · simp only [ChanCapValid]; word
    dsimp only
    imod Hcontinner $$ Hgv1 with HΦ
    imodintro
    wp_apply Mutex.wp_Unlock $$ [$lock $Hlock state slice slice_cap buffer Hgv2 Hoffer]
    · iapply chanInvInner_intro _ _ _ (ChanPhysState.Closed [])
      simp only [chanPhys, chanLogical]
      isplitl [state slice slice_cap buffer]
      · iframe
      iframe
      iintro _
      itrivial
    iexact HΦ
  | SndWait v' =>
    iNamed phys
    wp_auto
    wp_apply Mutex.wp_Unlock $$ [$lock $Hlock state v slice slice_cap buffer offer]
    · iapply chanInvInner_intro _ _ _ (ChanPhysState.SndWait v')
      simp only [chanPhys]
      iframe
    icases HΦ with ⟨-, HΦ⟩
    iexact HΦ
  | RcvWait =>
    iNamed phys
    wp_auto
    wp_apply Mutex.wp_Unlock $$ [$lock $Hlock state v slice slice_cap buffer offer]
    · iapply chanInvInner_intro _ _ _ (ChanPhysState.RcvWait)
      simp only [chanPhys]
      iframe
    icases HΦ with ⟨-, HΦ⟩
    iexact HΦ
  | SndDone v' =>
    iNamed phys
    wp_auto
    wp_apply Mutex.wp_Unlock $$ [$lock $Hlock state v slice slice_cap buffer offer]
    · iapply chanInvInner_intro _ _ _ (ChanPhysState.SndDone v')
      simp only [chanPhys]
      iframe
    icases HΦ with ⟨-, HΦ⟩
    iexact HΦ
  | RcvDone =>
    iNamed phys
    wp_auto
    wp_apply Mutex.wp_Unlock $$ [$lock $Hlock state v slice slice_cap buffer offer]
    · iapply chanInvInner_intro _ _ _ (ChanPhysState.RcvDone)
      simp only [chanPhys]
      iframe
    icases HΦ with ⟨-, HΦ⟩
    iexact HΦ
  | Closed buff =>
    icases HΦ with ⟨HΦ, -⟩
    iapply fupd_wp
    unfold closeAu
    imod HΦ with HΦ
    imod lc_fupd_elim_later $$ Hlc1 HΦ with HΦ
    iNamed HΦ
    cases buff with
    | nil =>
      simp only [chanLogical]
      icases offer with ⟨offer1, -⟩
      ihave %Hseq := ownChan_agree _ _ _ _ $$ Hocinner offer1
      subst Hseq
      dsimp only
      iexfalso
      iexact Hcontinner
    | cons x xs =>
      simp only [chanLogical]
      ihave %Hseq := ownChan_agree _ _ _ _ $$ Hocinner offer
      subst Hseq
      dsimp only
      iexfalso
      iexact Hcontinner

set_option maxHeartbeats 400000 in
theorem wp_Close (ch : Loc) (γ : ChanNames) :
    ⊢ ∀ Φ : val → IProp GF, isChan ch γ V -∗
      (£ 1 ∗ £ 1 ∗ £ 1 ∗ £ 1 -∗ closeAu γ V (Φ #())) -∗
      WP (App (Val (ch @!! go.GoType.PointerType (channel.Channel t) @!! go!"Close")) (Val #())) {{ Φ }} := by
  wp_start as #Hic
  ihave %Hnn := isChan_not_null _ _ _ $$ Hic
  wp_auto_lc 4
  ispecialize HΦ $$ [Hlc1 Hlc2 Hlc3 Hlc4]
  · iframe
  wp_if_destruct
  · exact absurd rfl Hnn
  wp_for
  wp_apply wp_tryClose ch γ $$ Hic
  isplit
  · iapply closeAu_wand $$ HΦ
    iintro HΦ
    wp_auto
    simp only [val_bool_eq, Bool.false_eq_true, decide_false, decide_true, ↓reduceIte]
    wp_auto
    iexact HΦ
  · wp_auto
    simp only [val_bool_eq, Bool.false_eq_true, decide_false, decide_true, ↓reduceIte]
    wp_auto
    wp_for_post
    iframe

end atomic_specs

end Perennial
