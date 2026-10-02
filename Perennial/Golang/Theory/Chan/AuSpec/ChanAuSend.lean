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
open github_com.goose_lang.primitive (is_Mutex is_Mutex_unseal is_Mutex_def own_Mutex own_Mutex_unseal
  own_Mutex_def wp_Mutex__Lock wp_Mutex__Unlock)

section atomic_specs
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : heapGS HasLC.hasLC GF] [allG GF]
variable [sem_fn : GoSemanticsFunctions] [pre_sem : go.PreSemantics] [sem : go.ChanSemantics]
variable {V : Type} [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V] {t : go.type}
  [IntoValTyped (GF := GF) V t]

set_option goose.wp.extras true

omit [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V t] in
/-- `is_lock` is `is_Mutex` (the channel invariant is stated with `is_lock`, as in Rocq). -/
theorem is_lock_eq_is_Mutex (m : loc) (R : IProp GF) : is_lock m R = is_Mutex m R := by
  rw [is_Mutex_unseal]; rfl

set_option maxHeartbeats 400000 in
theorem wp_Cap (ch : loc) (γ : chan_names) :
    {{ is_chan (GF := GF) ch γ V }}
      (App (Val (ch @!! go.type.PointerType (channel.Channel t) @!! go!"Cap")) (Val #()))
    {{ RET #γ.chan_cap; True }} := by
  wp_start as #Hch
  wp_auto
  ihave %Hnn := is_chan_not_null _ _ _ $$ Hch
  rw [is_chan_unseal]
  iNamed Hch
  wp_if_destruct
  · exact absurd rfl Hnn
  iapply HΦ
  itrivial

set_option maxHeartbeats 400000 in
theorem wp_Len (ch : loc) (γ : chan_names) :
    {{ is_chan (GF := GF) ch γ V }}
      (App (Val (ch @!! go.type.PointerType (channel.Channel t) @!! go!"Len")) (Val #()))
    {{ (l : w64), RET #l; ⌜0 ≤ sint.Z l ∧ sint.Z l ≤ sint.Z γ.chan_cap⌝ }} := by
  wp_start as #His
  wp_auto
  ihave %Hnn := is_chan_not_null _ _ _ $$ His
  rw [is_chan_unseal]
  iNamed His
  wp_if_destruct
  · exact absurd rfl Hnn
  rw [is_lock_eq_is_Mutex] at *
  wp_apply wp_Mutex__Lock $$ [$lock] as ⟨Hlock, Hchan⟩
  iNamed Hchan
  cases s with
  | Buffered buffer =>
    iNamed phys
    wp_auto
    ihave %Hlen := own_slice_len _ _ _ $$ slice
    simp only [chan_logical]
    ihave %Hsz := own_chan_buffer_size _ _ _ $$ offer
    wp_apply wp_Mutex__Unlock $$ [$lock $Hlock state buffer slice slice_cap offer]
    · iapply chan_inv_inner_intro _ _ _ (chan_phys_state.Buffered buffer)
      simp only [chan_phys, chan_logical]
      iframe
    iapply HΦ
    ipureintro
    word
  | Idle =>
    iNamed phys
    wp_auto
    ihave %Hlen := own_slice_len _ _ _ $$ slice
    wp_apply wp_Mutex__Unlock $$ [$lock $Hlock state buffer slice slice_cap offer v]
    · iapply chan_inv_inner_intro _ _ _ (chan_phys_state.Idle)
      simp only [chan_phys]
      iframe
    iapply HΦ
    ipureintro
    simp at Hlen
    word
  | SndWait v =>
    iNamed phys
    wp_auto
    ihave %Hlen := own_slice_len _ _ _ $$ slice
    wp_apply wp_Mutex__Unlock $$ [$lock $Hlock state buffer slice slice_cap offer v]
    · iapply chan_inv_inner_intro _ _ _ (chan_phys_state.SndWait v)
      simp only [chan_phys]
      iframe
    iapply HΦ
    ipureintro
    simp at Hlen
    word
  | RcvWait =>
    iNamed phys
    wp_auto
    ihave %Hlen := own_slice_len _ _ _ $$ slice
    wp_apply wp_Mutex__Unlock $$ [$lock $Hlock state buffer slice slice_cap offer v]
    · iapply chan_inv_inner_intro _ _ _ (chan_phys_state.RcvWait)
      simp only [chan_phys]
      iframe
    iapply HΦ
    ipureintro
    simp at Hlen
    word
  | SndDone v =>
    iNamed phys
    wp_auto
    ihave %Hlen := own_slice_len _ _ _ $$ slice
    wp_apply wp_Mutex__Unlock $$ [$lock $Hlock state buffer slice slice_cap offer v]
    · iapply chan_inv_inner_intro _ _ _ (chan_phys_state.SndDone v)
      simp only [chan_phys]
      iframe
    iapply HΦ
    ipureintro
    simp at Hlen
    word
  | RcvDone =>
    iNamed phys
    wp_auto
    ihave %Hlen := own_slice_len _ _ _ $$ slice
    wp_apply wp_Mutex__Unlock $$ [$lock $Hlock state buffer slice slice_cap offer v]
    · iapply chan_inv_inner_intro _ _ _ (chan_phys_state.RcvDone)
      simp only [chan_phys]
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
      ihave %Hlen := own_slice_len _ _ _ $$ slice
      wp_apply wp_Mutex__Unlock $$ [$lock $Hlock state buffer slice slice_cap offer]
      · iapply chan_inv_inner_intro _ _ _ (chan_phys_state.Closed [])
        simp only [chan_phys]
        iframe
      iapply HΦ
      ipureintro
      simp at Hlen
      word
    | cons x buffer =>
      iNamed phys
      simp only [chan_logical]
      ihave %Hsz := own_chan_drain_size _ _ _ $$ offer
      wp_auto
      ihave %Hlen := own_slice_len _ _ _ $$ slice
      wp_apply wp_Mutex__Unlock $$ [$lock $Hlock state buffer slice slice_cap offer]
      · iapply chan_inv_inner_intro _ _ _ (chan_phys_state.Closed (x :: buffer))
        simp only [chan_phys, chan_logical]
        iframe
      iapply HΦ
      ipureintro
      word

set_option maxHeartbeats 400000 in
theorem wp_TrySend_blocking (ch : loc) (v : V) (γ : chan_names) :
    ⊢ ∀ Φ : val → IProp GF, is_chan ch γ V -∗ (send_au γ v (Φ #true) ∧ Φ #false) -∗
      WP (App (App (Val (ch @!! go.type.PointerType (channel.Channel t) @!! go!"TrySend")) (Val #v))
        (Val #true)) {{ Φ }} := by
  wp_start as Hunb
  rw [is_chan_unseal]
  iNamed Hunb
  wp_auto_lc 5
  rw [is_lock_eq_is_Mutex] at *
  wp_apply wp_Mutex__Lock $$ [$lock] as ⟨Hlock, Hchan⟩
  iNamed Hchan
  cases s with
  | Buffered buffer =>
    iNamed phys
    simp only [chan_logical]
    ihave %Hcv := own_chan_cap_valid _ _ _ $$ offer
    ihave %Hlen := own_slice_len _ _ _ $$ slice
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
      unfold send_au
      imod HΦ with HΦ
      imod lc_fupd_elim_later $$ Hlc1 HΦ with HΦ
      iNamed HΦ
      ihave %Heq := own_chan_agree _ _ _ _ $$ offer Hoc
      subst Heq
      imod own_chan_halves_update _ _ (chanstate.t.Buffered (buffer ++ [v])) _ _ ?_ $$ Hoc offer
        with ⟨Hgv1, Hgv2⟩
      · simp only [chan_cap_valid] at Hcv ⊢
        simp only [List.length_append, List.length_cons, List.length_nil]
        constructor <;> word
      dsimp only
      imod Hcont $$ Hgv1 with Hstep
      imodintro
      wp_apply wp_Mutex__Unlock $$ [$lock $Hlock state buffer Hfr Hfrsl Hgv2]
      · iapply chan_inv_inner_intro _ _ _ (chan_phys_state.Buffered (buffer ++ [v]))
        simp only [chan_phys, chan_logical]
        iframe
      iexact Hstep
    · wp_apply wp_Mutex__Unlock $$ [$lock $Hlock state buffer slice slice_cap offer]
      · iapply chan_inv_inner_intro _ _ _ (chan_phys_state.Buffered buffer)
        simp only [chan_phys, chan_logical]
        iframe
      icases HΦ with ⟨-, HΦ⟩
      iexact HΦ
  | Idle =>
    iNamed phys
    chan_unfold_consts
    wp_auto
    simp only [chan_logical]
    iNamed offer
    ihave %HcvIdle := own_chan_cap_valid _ _ _ $$ offer
    simp only [chan_cap_valid] at HcvIdle
    imod offer_idle_to_send γ V iprop(send_au γ v (Φ #true) ∧ Φ #false) (Φ #true) v $$ Hoffer
      with ⟨offer1, offer2⟩
    wp_apply wp_Mutex__Unlock $$ [$lock $Hlock state v slice slice_cap buffer offer1 Hpred offer HΦ]
    · iapply chan_inv_inner_intro _ _ _ (chan_phys_state.SndWait v)
      simp only [chan_phys, chan_logical]
      isplitl [state v slice slice_cap buffer]
      · iexists slice_val
        iframe
      iexists iprop(send_au γ v (Φ #true) ∧ Φ #false), (Φ #true), Φr0
      iframe
      iintro H
      icases H with ⟨H, -⟩
      iexact H
    wp_apply wp_Mutex__Lock $$ [$lock] as ⟨Hlock, Hchan⟩
    iNamed Hchan
    cases s with
    | Buffered buff =>
      simp only [chan_logical]
      ihave %Hcv2 := own_chan_cap_valid _ _ _ $$ offer
      simp only [chan_cap_valid] at Hcv2
      exfalso; word
    | Idle =>
      simp only [chan_logical]
      iNamed offer
      iexfalso
      iapply saved_offer_half_full_invalid $$ offer2 Hoffer
    | SndWait v' =>
      iNamed phys
      simp only [chan_logical]
      iNamed offer
      imod saved_offer_lc_agree γ V _ _ _ _ _ _ $$ Hlc1 offer2 Hoffer with ⟨%Heq, #Hpeq, #H, H1⟩
      wp_auto
      wp_apply wp_Mutex__Unlock $$ [$lock $Hlock state v slice slice_cap buffer Hpred H1 offer]
      · iapply chan_inv_inner_intro _ _ _ (chan_phys_state.Idle)
        simp only [chan_phys, chan_logical]
        isplitl [state v slice slice_cap buffer]
        · iexists _, slice_val
          iframe
        iexists Φr0
        iframe
      ihave HP := internal_eq_rewrite_wand $$ Hpeq HP
      icases HP with ⟨-, HP⟩
      iexact HP
    | RcvWait =>
      simp only [chan_logical]
      iNamed offer
      ihave ⟨%Heq, -⟩ := saved_offer_agree γ V _ _ _ _ _ _ _ _ $$ [$offer2 $Hoffer]
      cases Heq
    | SndDone v' =>
      simp only [chan_logical]
      iNamed offer
      ihave ⟨%Heq, -⟩ := saved_offer_agree γ V _ _ _ _ _ _ _ _ $$ [$offer2 $Hoffer]
      cases Heq
    | RcvDone =>
      iNamed phys
      simp only [chan_logical]
      iNamed offer
      iapply fupd_wp
      unfold send_nested_au
      imod Hau with Hau
      imod lc_fupd_elim_later $$ Hlc1 Hau with Hau
      iNamed Hau
      ihave %Hseq := own_chan_agree _ _ _ _ $$ Hocinner offer
      subst Hseq
      imod own_chan_halves_update _ _ chanstate.t.Idle _ _ HcvIdle $$ Hocinner offer with ⟨Hgv1, Hgv2⟩
      dsimp only
      imod Hcontinner $$ Hgv1 with Hcont
      imodintro
      imod saved_offer_lc_agree γ V _ _ _ _ _ _ $$ Hlc2 offer2 Hoffer with ⟨%Heq, #Hpeq, #H, H1⟩
      wp_auto
      wp_apply wp_Mutex__Unlock $$ [$lock $Hlock state v slice slice_cap buffer Hpred H1 Hgv2]
      · iapply chan_inv_inner_intro _ _ _ (chan_phys_state.Idle)
        simp only [chan_phys, chan_logical]
        isplitl [state v slice slice_cap buffer]
        · iexists _, slice_val
          iframe
        iexists Φr0
        iframe
      iapply internal_eq_rewrite_wand $$ H Hcont
    | Closed buff =>
      cases buff with
      | nil =>
        simp only [chan_logical]
        icases offer with ⟨Hoc, Hoffer⟩
        have hcap0 : γ.chan_cap = W64 0 := by word
        ispecialize Hoffer $$ %hcap0
        iexfalso
        iapply saved_offer_half_full_invalid $$ offer2 Hoffer
      | cons x xs =>
        simp only [chan_logical]
        ihave %Hcv2 := own_chan_cap_valid _ _ _ $$ offer
        simp only [chan_cap_valid] at Hcv2
        exfalso; word
  | SndWait v' =>
    iNamed phys
    wp_auto
    wp_apply wp_Mutex__Unlock $$ [$lock $Hlock state v slice slice_cap buffer offer]
    · iapply chan_inv_inner_intro _ _ _ (chan_phys_state.SndWait v')
      simp only [chan_phys]
      iframe
    icases HΦ with ⟨-, HΦ⟩
    iexact HΦ
  | RcvWait =>
    -- NOTE (Rocq): this leaves no freedom for picking the linearization order.
    iNamed phys
    chan_unfold_consts
    wp_auto
    simp only [chan_logical]
    iNamed offer
    ihave HP := Hau $$ HP
    iapply fupd_wp
    unfold recv_au
    imod HP with HP
    imod lc_fupd_elim_later $$ Hlc1 HP with HP
    iNamed HP
    ihave %Hseq := own_chan_agree _ _ _ _ $$ Hoc offer
    subst Hseq
    ihave %HcvIdle := own_chan_cap_valid _ _ _ $$ offer
    simp only [chan_cap_valid] at HcvIdle
    imod own_chan_halves_update _ _ chanstate.t.RcvPending _ _ HcvIdle $$ offer Hoc with ⟨Hgv1, Hgv2⟩
    dsimp only
    imod Hcont $$ Hgv2 with Hcont1
    icases HΦ with ⟨HΦ, -⟩
    unfold send_au
    imod HΦ with HΦ
    imod lc_fupd_elim_later $$ Hlc2 HΦ with HΦ
    iNamed HΦ
    ihave %Hseq := own_chan_agree _ _ _ _ $$ Hgv1 Hoc
    subst Hseq
    imod own_chan_halves_update _ _ (chanstate.t.SndCommit v) _ _ HcvIdle $$ Hgv1 Hoc
      with ⟨Hgv1, Hgv2⟩
    dsimp only
    imod Hcont $$ Hgv2 with Hcont
    imodintro
    wp_apply wp_Mutex__Unlock $$ [$lock $Hlock state v slice slice_cap buffer Hgv1 Hcont1 Hpred Hoffer]
    · iapply chan_inv_inner_intro _ _ _ (chan_phys_state.SndDone v)
      simp only [chan_phys, chan_logical]
      iframe
    iexact Hcont
  | SndDone v' =>
    iNamed phys
    wp_auto
    wp_apply wp_Mutex__Unlock $$ [$lock $Hlock state v slice slice_cap buffer offer]
    · iapply chan_inv_inner_intro _ _ _ (chan_phys_state.SndDone v')
      simp only [chan_phys]
      iframe
    icases HΦ with ⟨-, HΦ⟩
    iexact HΦ
  | RcvDone =>
    iNamed phys
    wp_auto
    wp_apply wp_Mutex__Unlock $$ [$lock $Hlock state v slice slice_cap buffer offer]
    · iapply chan_inv_inner_intro _ _ _ (chan_phys_state.RcvDone)
      simp only [chan_phys]
      iframe
    icases HΦ with ⟨-, HΦ⟩
    iexact HΦ
  | Closed buff =>
    icases HΦ with ⟨HΦ, -⟩
    iapply fupd_wp
    unfold send_au
    imod HΦ with HΦ
    imod lc_fupd_elim_later $$ Hlc1 HΦ with HΦ
    iNamed HΦ
    cases buff with
    | nil =>
      simp only [chan_logical]
      icases offer with ⟨offer1, -⟩
      ihave %Hseq := own_chan_agree _ _ _ _ $$ Hoc offer1
      subst Hseq
      dsimp only
      iexfalso
      iexact Hcont
    | cons x xs =>
      simp only [chan_logical]
      ihave %Hseq := own_chan_agree _ _ _ _ $$ Hoc offer
      subst Hseq
      dsimp only
      iexfalso
      iexact Hcont

set_option maxHeartbeats 400000 in
theorem wp_TrySend_nonblocking (ch : loc) (v : V) (γ : chan_names) :
    ⊢ ∀ Φ : val → IProp GF, is_chan ch γ V -∗ nonblocking_send_au γ v (Φ #true) (Φ #false) -∗
      WP (App (App (Val (ch @!! go.type.PointerType (channel.Channel t) @!! go!"TrySend")) (Val #v))
        (Val #false)) {{ Φ }} := by
  wp_start as Hunb
  rw [is_chan_unseal]
  iNamed Hunb
  wp_auto_lc 5
  rw [is_lock_eq_is_Mutex] at *
  wp_apply wp_Mutex__Lock $$ [$lock] as ⟨Hlock, Hchan⟩
  iNamed Hchan
  unfold nonblocking_send_au nonblocking_send_au_inner
  cases s with
  | Buffered buffer =>
    iNamed phys
    simp only [chan_logical]
    ihave %Hcv := own_chan_cap_valid _ _ _ $$ offer
    ihave %Hlen := own_slice_len _ _ _ $$ slice
    wp_auto
    wp_if_destruct
    · icases HΦ with ⟨HΦ, -⟩
      iapply fupd_wp
      imod HΦ with HΦ
      imod lc_fupd_elim_later $$ Hlc1 HΦ with HΦ
      iNamed HΦ
      ihave %Heq := own_chan_agree _ _ _ _ $$ offer Hoc
      subst Heq
      imod own_chan_halves_update _ _ (chanstate.t.Buffered (buffer ++ [v])) _ _ ?_ $$ Hoc offer
        with ⟨Hgv1, Hgv2⟩
      · simp only [chan_cap_valid] at Hcv ⊢
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
      wp_apply wp_Mutex__Unlock $$ [$lock $Hlock state buffer Hfr Hfrsl Hgv2]
      · iapply chan_inv_inner_intro _ _ _ (chan_phys_state.Buffered (buffer ++ [v]))
        simp only [chan_phys, chan_logical]
        iframe
      iexact Hstep
    · wp_apply wp_Mutex__Unlock $$ [$lock $Hlock state buffer slice slice_cap offer]
      · iapply chan_inv_inner_intro _ _ _ (chan_phys_state.Buffered buffer)
        simp only [chan_phys, chan_logical]
        iframe
      icases HΦ with ⟨-, HΦ⟩
      iexact HΦ
  | Idle =>
    iNamed phys
    wp_auto
    wp_apply wp_Mutex__Unlock $$ [$lock $Hlock state v slice slice_cap buffer offer]
    · iapply chan_inv_inner_intro _ _ _ (chan_phys_state.Idle)
      simp only [chan_phys]
      iframe
    icases HΦ with ⟨-, HΦ⟩
    iexact HΦ
  | SndWait v' =>
    iNamed phys
    wp_auto
    wp_apply wp_Mutex__Unlock $$ [$lock $Hlock state v slice slice_cap buffer offer]
    · iapply chan_inv_inner_intro _ _ _ (chan_phys_state.SndWait v')
      simp only [chan_phys]
      iframe
    icases HΦ with ⟨-, HΦ⟩
    iexact HΦ
  | RcvWait =>
    iNamed phys
    chan_unfold_consts
    wp_auto
    simp only [chan_logical]
    iNamed offer
    ihave HP := Hau $$ HP
    iapply fupd_wp
    unfold recv_au
    imod HP with HP
    imod lc_fupd_elim_later $$ Hlc1 HP with HP
    iNamed HP
    ihave %Hseq := own_chan_agree _ _ _ _ $$ Hoc offer
    subst Hseq
    ihave %HcvIdle := own_chan_cap_valid _ _ _ $$ offer
    simp only [chan_cap_valid] at HcvIdle
    imod own_chan_halves_update _ _ chanstate.t.RcvPending _ _ HcvIdle $$ offer Hoc with ⟨Hgv1, Hgv2⟩
    dsimp only
    imod Hcont $$ Hgv2 with Hcont1
    icases HΦ with ⟨HΦ, -⟩
    imod HΦ with HΦ
    imod lc_fupd_elim_later $$ Hlc2 HΦ with HΦ
    iNamed HΦ
    ihave %Hseq := own_chan_agree _ _ _ _ $$ Hgv1 Hoc
    subst Hseq
    imod own_chan_halves_update _ _ (chanstate.t.SndCommit v) _ _ HcvIdle $$ Hgv1 Hoc
      with ⟨Hgv1, Hgv2⟩
    dsimp only
    imod Hcont $$ Hgv2 with Hcont
    imodintro
    wp_apply wp_Mutex__Unlock $$ [$lock $Hlock state v slice slice_cap buffer Hgv1 Hcont1 Hpred Hoffer]
    · iapply chan_inv_inner_intro _ _ _ (chan_phys_state.SndDone v)
      simp only [chan_phys, chan_logical]
      iframe
    iexact Hcont
  | SndDone v' =>
    iNamed phys
    wp_auto
    wp_apply wp_Mutex__Unlock $$ [$lock $Hlock state v slice slice_cap buffer offer]
    · iapply chan_inv_inner_intro _ _ _ (chan_phys_state.SndDone v')
      simp only [chan_phys]
      iframe
    icases HΦ with ⟨-, HΦ⟩
    iexact HΦ
  | RcvDone =>
    iNamed phys
    wp_auto
    wp_apply wp_Mutex__Unlock $$ [$lock $Hlock state v slice slice_cap buffer offer]
    · iapply chan_inv_inner_intro _ _ _ (chan_phys_state.RcvDone)
      simp only [chan_phys]
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
      simp only [chan_logical]
      icases offer with ⟨offer1, -⟩
      ihave %Hseq := own_chan_agree _ _ _ _ $$ Hoc offer1
      subst Hseq
      dsimp only
      iexfalso
      iexact Hcont
    | cons x xs =>
      simp only [chan_logical]
      ihave %Hseq := own_chan_agree _ _ _ _ $$ Hoc offer
      subst Hseq
      dsimp only
      iexfalso
      iexact Hcont

set_option maxHeartbeats 400000 in
theorem wp_TrySend_nonblocking_alt (ch : loc) (v : V) (γ : chan_names) :
    ⊢ ∀ Φ : val → IProp GF, is_chan ch γ V -∗ nonblocking_send_au_alt γ v (Φ #true) (Φ #false) -∗
      WP (App (App (Val (ch @!! go.type.PointerType (channel.Channel t) @!! go!"TrySend")) (Val #v))
        (Val #false)) {{ Φ }} := by
  wp_start as Hunb
  rw [is_chan_unseal]
  iNamed Hunb
  wp_auto_lc 5
  rw [is_lock_eq_is_Mutex] at *
  wp_apply wp_Mutex__Lock $$ [$lock] as ⟨Hlock, Hchan⟩
  iNamed Hchan
  unfold nonblocking_send_au_alt
  cases s with
  | Buffered buffer =>
    iNamed phys
    simp only [chan_logical]
    ihave %Hcv := own_chan_cap_valid _ _ _ $$ offer
    ihave %Hlen := own_slice_len _ _ _ $$ slice
    wp_auto
    wp_if_destruct
    · iapply fupd_wp
      imod HΦ with HΦ
      imod lc_fupd_elim_later $$ Hlc1 HΦ with HΦ
      iNamed HΦ
      ihave %Heq := own_chan_agree _ _ _ _ $$ offer Hoc
      subst Heq
      dsimp only
      rw [ite_eq_left (by word)]
      imod own_chan_halves_update _ _ (chanstate.t.Buffered (buffer ++ [v])) _ _ ?_ $$ Hoc offer
        with ⟨Hgv1, Hgv2⟩
      · simp only [chan_cap_valid] at Hcv ⊢
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
      wp_apply wp_Mutex__Unlock $$ [$lock $Hlock state buffer Hfr Hfrsl Hgv2]
      · iapply chan_inv_inner_intro _ _ _ (chan_phys_state.Buffered (buffer ++ [v]))
        simp only [chan_phys, chan_logical]
        iframe
      iexact Hstep
    · iapply fupd_wp
      imod HΦ with HΦ
      imod lc_fupd_elim_later $$ Hlc1 HΦ with HΦ
      iNamed HΦ
      ihave %Heq := own_chan_agree _ _ _ _ $$ offer Hoc
      subst Heq
      dsimp only
      rw [ite_eq_right (by word)]
      imod Hcont $$ Hoc with HΦ
      imodintro
      wp_apply wp_Mutex__Unlock $$ [$lock $Hlock state buffer slice slice_cap offer]
      · iapply chan_inv_inner_intro _ _ _ (chan_phys_state.Buffered buffer)
        simp only [chan_phys, chan_logical]
        iframe
      iexact HΦ
  | Idle =>
    iNamed phys
    wp_auto
    iapply fupd_wp
    imod HΦ with HΦ
    imod lc_fupd_elim_later $$ Hlc1 HΦ with HΦ
    iNamed HΦ
    simp only [chan_logical]
    iNamed offer
    ihave %Hseq := own_chan_agree _ _ _ _ $$ Hoc offer
    subst Hseq
    dsimp only
    imod Hcont $$ Hoc with HΦ
    imodintro
    wp_apply wp_Mutex__Unlock $$ [$lock $Hlock state v slice slice_cap buffer Hoffer Hpred offer]
    · iapply chan_inv_inner_intro _ _ _ (chan_phys_state.Idle)
      simp only [chan_phys, chan_logical]
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
    simp only [chan_logical]
    iNamed offer
    ihave %Hseq := own_chan_agree _ _ _ _ $$ Hoc offer
    subst Hseq
    dsimp only
    imod Hcont $$ Hoc with HΦ
    imodintro
    wp_apply wp_Mutex__Unlock $$ [$lock $Hlock state v slice slice_cap buffer Hoffer HP Hpred Hau offer]
    · iapply chan_inv_inner_intro _ _ _ (chan_phys_state.SndWait v')
      simp only [chan_phys, chan_logical]
      isplitl [state v slice slice_cap buffer]
      · iframe
      iexists P0, Φ0, Φr0
      iframe
    iexact HΦ
  | RcvWait =>
    iNamed phys
    chan_unfold_consts
    wp_auto
    simp only [chan_logical]
    iNamed offer
    ihave HP := Hau $$ HP
    iapply fupd_wp
    unfold recv_au
    imod HP with HP
    imod lc_fupd_elim_later $$ Hlc1 HP with HP
    iNamed HP
    ihave %Hseq := own_chan_agree _ _ _ _ $$ Hoc offer
    subst Hseq
    ihave %HcvIdle := own_chan_cap_valid _ _ _ $$ offer
    simp only [chan_cap_valid] at HcvIdle
    imod own_chan_halves_update _ _ chanstate.t.RcvPending _ _ HcvIdle $$ offer Hoc with ⟨Hgv1, Hgv2⟩
    dsimp only
    imod Hcont $$ Hgv2 with Hcont1
    imod HΦ with HΦ
    imod lc_fupd_elim_later $$ Hlc2 HΦ with HΦ
    iNamed HΦ
    ihave %Hseq := own_chan_agree _ _ _ _ $$ Hgv1 Hoc
    subst Hseq
    imod own_chan_halves_update _ _ (chanstate.t.SndCommit v) _ _ HcvIdle $$ Hgv1 Hoc
      with ⟨Hgv1, Hgv2⟩
    dsimp only
    imod Hcont $$ Hgv2 with Hcont
    imodintro
    wp_apply wp_Mutex__Unlock $$ [$lock $Hlock state v slice slice_cap buffer Hgv1 Hcont1 Hpred Hoffer]
    · iapply chan_inv_inner_intro _ _ _ (chan_phys_state.SndDone v)
      simp only [chan_phys, chan_logical]
      iframe
    iexact Hcont
  | SndDone v' =>
    iNamed phys
    wp_auto
    iapply fupd_wp
    imod HΦ with HΦ
    imod lc_fupd_elim_later $$ Hlc1 HΦ with HΦ
    iNamed HΦ
    simp only [chan_logical]
    iNamed offer
    ihave %Hseq := own_chan_agree _ _ _ _ $$ Hoc offer
    subst Hseq
    dsimp only
    imod Hcont $$ Hoc with HΦ
    imodintro
    wp_apply wp_Mutex__Unlock $$ [$lock $Hlock state v slice slice_cap buffer Hoffer Hpred Hau offer]
    · iapply chan_inv_inner_intro _ _ _ (chan_phys_state.SndDone v')
      simp only [chan_phys, chan_logical]
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
    simp only [chan_logical]
    iNamed offer
    ihave %Hseq := own_chan_agree _ _ _ _ $$ Hoc offer
    subst Hseq
    dsimp only
    imod Hcont $$ Hoc with HΦ
    imodintro
    wp_apply wp_Mutex__Unlock $$ [$lock $Hlock state v slice slice_cap buffer Hoffer Hpred Hau offer]
    · iapply chan_inv_inner_intro _ _ _ (chan_phys_state.RcvDone)
      simp only [chan_phys, chan_logical]
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
      simp only [chan_logical]
      icases offer with ⟨offer1, -⟩
      ihave %Hseq := own_chan_agree _ _ _ _ $$ Hoc offer1
      subst Hseq
      dsimp only
      iexfalso
      iexact Hcont
    | cons x xs =>
      simp only [chan_logical]
      ihave %Hseq := own_chan_agree _ _ _ _ $$ Hoc offer
      subst Hseq
      dsimp only
      iexfalso
      iexact Hcont

theorem wp_TrySend (ch : loc) (v : V) (γ : chan_names) (blocking : Bool) :
    ⊢ ∀ Φ : val → IProp GF, is_chan ch γ V -∗
      (if blocking then iprop(send_au γ v (Φ #true) ∧ Φ #false)
       else iprop(nonblocking_send_au γ v (Φ #true) (Φ #false) ∨
         nonblocking_send_au_alt γ v (Φ #true) (Φ #false))) -∗
      WP (App (App (Val (ch @!! go.type.PointerType (channel.Channel t) @!! go!"TrySend")) (Val #v))
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
theorem wp_Send (ch : loc) (v : V) (γ : chan_names) :
    ⊢ ∀ Φ : val → IProp GF, is_chan ch γ V -∗
      (£ 1 ∗ £ 1 ∗ £ 1 ∗ £ 1 -∗ send_au γ v (Φ #())) -∗
      WP (App (Val (ch @!! go.type.PointerType (channel.Channel t) @!! go!"Send")) (Val #v)) {{ Φ }} := by
  wp_start as #Hic
  ihave %Hnn := is_chan_not_null _ _ _ $$ Hic
  wp_auto_lc 4
  ispecialize HΦ $$ [Hlc1 Hlc2 Hlc3 Hlc4]
  · iframe
  wp_if_destruct
  · exact absurd rfl Hnn
  wp_for
  wp_apply wp_TrySend ch v γ true $$ Hic
  simp only [↓reduceIte]
  isplit
  · iapply send_au_wand $$ HΦ
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
theorem wp_BlockingSend (ch : loc) (v : V) (γ : chan_names) (Hcapnz : sint.Z γ.chan_cap > 0) :
    ⊢ ∀ Φ : val → IProp GF, is_chan ch γ V -∗
      (£ 1 ∗ £ 1 ∗ £ 1 ∗ £ 1 -∗ buffered_send_au γ v (Φ #())) -∗
      WP (App (Val (ch @!! go.type.PointerType (channel.Channel t) @!! go!"Send")) (Val #v)) {{ Φ }} := by
  iintro %Φ #Hunb HΦ
  iapply wp_Send $$ Hunb
  iintro Hlc
  ispecialize HΦ $$ Hlc
  unfold buffered_send_au send_au
  imod HΦ with HΦ
  imodintro
  inext
  iNamed HΦ
  ihave %Hcv := own_chan_cap_valid _ _ _ $$ Hoc
  iexists s
  iframe Hoc
  rcases s with _ | _ | _ | _ | _ | _ | _
  all_goals first
    | iexact Hcont
    | (exfalso; simp only [chan_cap_valid] at Hcv; word)

set_option maxHeartbeats 400000 in
theorem wp_tryClose (ch : loc) (γ : chan_names) :
    ⊢ ∀ Φ : val → IProp GF, is_chan ch γ V -∗ (close_au γ V (Φ #true) ∧ Φ #false) -∗
      WP (App (Val (ch @!! go.type.PointerType (channel.Channel t) @!! go!"tryClose")) (Val #())) {{ Φ }} := by
  wp_start as #Hunb
  rw [is_chan_unseal]
  iNamed Hunb
  chan_unfold_consts
  wp_auto_lc 1
  rw [is_lock_eq_is_Mutex] at *
  wp_apply wp_Mutex__Lock $$ [$lock] as ⟨Hlock, Hchan⟩
  iNamed Hchan
  cases s with
  | Buffered buffer =>
    iNamed phys
    simp only [chan_logical]
    ihave %Hcv := own_chan_cap_valid _ _ _ $$ offer
    simp only [chan_cap_valid] at Hcv
    wp_auto
    icases HΦ with ⟨HΦ, -⟩
    iapply fupd_wp
    unfold close_au
    imod HΦ with HΦ
    imod lc_fupd_elim_later $$ Hlc1 HΦ with HΦ
    iNamed HΦ
    ihave %Heq := own_chan_agree _ _ _ _ $$ Hocinner offer
    subst Heq
    imod own_chan_halves_update _ _ (chanstate.t.Closed buffer) _ _ ?_ $$ Hocinner offer
      with ⟨Hgv1, Hgv2⟩
    · cases buffer <;> simp only [chan_cap_valid] <;> word
    dsimp only
    imod Hcontinner $$ Hgv1 with HΦ
    imodintro
    wp_apply wp_Mutex__Unlock $$ [$lock $Hlock state slice slice_cap buffer Hgv2]
    · iapply chan_inv_inner_intro _ _ _ (chan_phys_state.Closed buffer)
      cases buffer with
      | nil =>
        simp only [chan_phys, chan_logical]
        iframe
        iintro %Hcap0
        exfalso
        rw [Hcap0] at Hcv
        exact absurd Hcv.2 (by decide)
      | cons x xs =>
        simp only [chan_phys, chan_logical]
        iframe
    iexact HΦ
  | Idle =>
    iNamed phys
    simp only [chan_logical]
    iNamed offer
    ihave %Hcv := own_chan_cap_valid _ _ _ $$ offer
    simp only [chan_cap_valid] at Hcv
    wp_auto
    icases HΦ with ⟨HΦ, -⟩
    iapply fupd_wp
    unfold close_au
    imod HΦ with HΦ
    imod lc_fupd_elim_later $$ Hlc1 HΦ with HΦ
    iNamed HΦ
    ihave %Heq := own_chan_agree _ _ _ _ $$ Hocinner offer
    subst Heq
    imod own_chan_halves_update _ _ (chanstate.t.Closed []) _ _ ?_ $$ Hocinner offer
      with ⟨Hgv1, Hgv2⟩
    · simp only [chan_cap_valid]; word
    dsimp only
    imod Hcontinner $$ Hgv1 with HΦ
    imodintro
    wp_apply wp_Mutex__Unlock $$ [$lock $Hlock state slice slice_cap buffer Hgv2 Hoffer]
    · iapply chan_inv_inner_intro _ _ _ (chan_phys_state.Closed [])
      simp only [chan_phys, chan_logical]
      isplitl [state slice slice_cap buffer]
      · iframe
      iframe
      iintro _
      itrivial
    iexact HΦ
  | SndWait v' =>
    iNamed phys
    wp_auto
    wp_apply wp_Mutex__Unlock $$ [$lock $Hlock state v slice slice_cap buffer offer]
    · iapply chan_inv_inner_intro _ _ _ (chan_phys_state.SndWait v')
      simp only [chan_phys]
      iframe
    icases HΦ with ⟨-, HΦ⟩
    iexact HΦ
  | RcvWait =>
    iNamed phys
    wp_auto
    wp_apply wp_Mutex__Unlock $$ [$lock $Hlock state v slice slice_cap buffer offer]
    · iapply chan_inv_inner_intro _ _ _ (chan_phys_state.RcvWait)
      simp only [chan_phys]
      iframe
    icases HΦ with ⟨-, HΦ⟩
    iexact HΦ
  | SndDone v' =>
    iNamed phys
    wp_auto
    wp_apply wp_Mutex__Unlock $$ [$lock $Hlock state v slice slice_cap buffer offer]
    · iapply chan_inv_inner_intro _ _ _ (chan_phys_state.SndDone v')
      simp only [chan_phys]
      iframe
    icases HΦ with ⟨-, HΦ⟩
    iexact HΦ
  | RcvDone =>
    iNamed phys
    wp_auto
    wp_apply wp_Mutex__Unlock $$ [$lock $Hlock state v slice slice_cap buffer offer]
    · iapply chan_inv_inner_intro _ _ _ (chan_phys_state.RcvDone)
      simp only [chan_phys]
      iframe
    icases HΦ with ⟨-, HΦ⟩
    iexact HΦ
  | Closed buff =>
    icases HΦ with ⟨HΦ, -⟩
    iapply fupd_wp
    unfold close_au
    imod HΦ with HΦ
    imod lc_fupd_elim_later $$ Hlc1 HΦ with HΦ
    iNamed HΦ
    cases buff with
    | nil =>
      simp only [chan_logical]
      icases offer with ⟨offer1, -⟩
      ihave %Hseq := own_chan_agree _ _ _ _ $$ Hocinner offer1
      subst Hseq
      dsimp only
      iexfalso
      iexact Hcontinner
    | cons x xs =>
      simp only [chan_logical]
      ihave %Hseq := own_chan_agree _ _ _ _ $$ Hocinner offer
      subst Hseq
      dsimp only
      iexfalso
      iexact Hcontinner

set_option maxHeartbeats 400000 in
theorem wp_Close (ch : loc) (γ : chan_names) :
    ⊢ ∀ Φ : val → IProp GF, is_chan ch γ V -∗
      (£ 1 ∗ £ 1 ∗ £ 1 ∗ £ 1 -∗ close_au γ V (Φ #())) -∗
      WP (App (Val (ch @!! go.type.PointerType (channel.Channel t) @!! go!"Close")) (Val #())) {{ Φ }} := by
  wp_start as #Hic
  ihave %Hnn := is_chan_not_null _ _ _ $$ Hic
  wp_auto_lc 4
  ispecialize HΦ $$ [Hlc1 Hlc2 Hlc3 Hlc4]
  · iframe
  wp_if_destruct
  · exact absurd rfl Hnn
  wp_for
  wp_apply wp_tryClose ch γ $$ Hic
  isplit
  · iapply close_au_wand $$ HΦ
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
