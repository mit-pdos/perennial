/-
Port of `new/golang/theory/chan/au_spec/chan_au_recv.v`: specifications of the
channel model's `TryReceive` and `Receive`.
-/
import Perennial.Golang.Theory.Chan.AuSpec.ChanAuSend

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

omit [Pos.Countable V] [IntoValTyped (GF := GF) V t] in
/-- Dropping the first element of a slice (`s[1:]`), with its capacity. -/
theorem own_slice_pop (sl : slice.t) (x : V) (rest : List V) :
    ⊢ (sl ↦* (x :: rest) : IProp GF) -∗ own_slice_cap V sl (DFrac.own 1) -∗
      slice.slice sl V (W64 1) sl.len ↦* rest ∗
      own_slice_cap V (slice.slice sl V (W64 1) sl.len) (DFrac.own 1) := by
  iintro Hsl Hcap
  ihave %Hlen := own_slice_len _ _ _ $$ Hsl
  ihave %Hwf := own_slice_cap_wf (V := V) _ _ $$ Hcap
  simp only [List.length_cons] at Hlen
  icases (own_slice_split_all (W64 1) sl _ _ ⟨by decide, by word⟩).1 $$ Hsl with ⟨-, Hsl⟩
  have h1 : sint.nat (W64 1) = 1 := rfl
  rw [h1, List.drop_one, List.tail_cons]
  iframe
  iapply (own_slice_cap_slice sl (W64 1) _ ⟨by decide, by word, by word⟩).1 $$ Hcap

set_option maxHeartbeats 400000 in
theorem wp_TryReceive_blocking (ch : loc) (γ : chan_names) :
    ⊢ ∀ Φ : val → IProp GF, is_chan ch γ V -∗
      (recv_au γ V (fun v ok => Φ (PairV (PairV #true #v) #ok)) ∧
        Φ (PairV (PairV #false #(zero_val V)) #true)) -∗
      WP (App (Val (ch @!! go.type.PointerType (channel.Channel t) @!! go!"TryReceive"))
        (Val #true)) {{ Φ }} := by
  wp_start as Hch
  rw [is_chan_unseal]
  iNamed Hch
  chan_unfold_consts
  wp_auto_lc 9
  rw [is_lock_eq_is_Mutex] at *
  wp_apply wp_Mutex__Lock $$ [$lock] as ⟨Hlock, Hchan⟩
  iNamed Hchan
  cases s with
  | Buffered buffer =>
    iNamed phys
    simp only [chan_logical]
    ihave %Hcv := own_chan_cap_valid _ _ _ $$ offer
    -- `word` fails with an unfolded `chan_cap_valid` hypothesis in context
    simp only [chan_cap_valid] at Hcv
    ihave %Hlen := own_slice_len _ _ _ $$ slice
    ihave %Hwf := own_slice_cap_wf (V := V) _ _ $$ slice_cap
    wp_auto
    wp_if_destruct
    · cases buffer with
      | nil => exfalso; simp at Hlen; revert Hif Hlen; word
      | cons x rest =>
      icases HΦ with ⟨HΦ, -⟩
      iapply fupd_wp
      unfold recv_au
      imod HΦ with HΦ
      imod lc_fupd_elim_later $$ Hlc1 HΦ with HΦ
      iNamed HΦ
      ihave %Heq := own_chan_agree _ _ _ _ $$ offer Hoc
      subst Heq
      imod own_chan_halves_update _ _ (chanstate.t.Buffered rest) _ _ ?_ $$ Hoc offer
        with ⟨Hgv1, Hgv2⟩
      · simp only [chan_cap_valid, List.length_cons] at Hcv ⊢
        constructor <;> word
      dsimp only
      imod Hcont $$ Hgv1 with HΦ
      imodintro
      rw [ite_eq_left ⟨by decide, by word⟩]
      wp_apply wp_load_slice_index slice_val (sint.Z (W64 0)) _ _ x (by decide) $$ [$slice] as slice
      · ipureintro; rfl
      simp only [List.length_cons] at Hlen
      rw [ite_eq_left ⟨by decide, by word, Hwf.2⟩]
      wp_auto
      icases own_slice_pop _ _ _ $$ slice slice_cap with ⟨slice, slice_cap⟩
      wp_apply wp_Mutex__Unlock $$ [$lock $Hlock state buffer slice slice_cap Hgv2]
      · iapply chan_inv_inner_intro _ _ _ (chan_phys_state.Buffered rest)
        simp only [chan_phys, chan_logical]
        iframe
      iexact HΦ
    · cases buffer with
      | cons x rest => exfalso; simp at Hlen; revert Hif Hlen; word
      | nil =>
      wp_apply wp_Mutex__Unlock $$ [$lock $Hlock state buffer slice slice_cap offer]
      · iapply chan_inv_inner_intro _ _ _ (chan_phys_state.Buffered [])
        simp only [chan_phys, chan_logical]
        iframe
      icases HΦ with ⟨-, HΦ⟩
      iexact HΦ
  | Idle =>
    iNamed phys
    wp_auto
    simp only [chan_logical]
    iNamed offer
    ihave %HcvIdle := own_chan_cap_valid _ _ _ $$ offer
    simp only [chan_cap_valid] at HcvIdle
    imod offer_idle_to_recv γ V iprop((recv_au γ V fun v ok => Φ (PairV (PairV #true #v) #ok)) ∧
        Φ (PairV (PairV #false #(zero_val V)) #true)) iprop(True) $$ Hoffer
      with ⟨offer1, offer2⟩
    imod saved_pred_update (Function.uncurry (fun (v : V) (ok : Bool) => Φ (PairV (PairV #true #v) #ok)))
      _ _ $$ Hpred with Hpred
    icases saved_pred_halves _ _ $$ Hpred with ⟨Hpred1, Hpred2⟩
    wp_apply wp_Mutex__Unlock $$ [$lock $Hlock state v slice slice_cap buffer offer1 Hpred1 offer HΦ]
    · iapply chan_inv_inner_intro _ _ _ (chan_phys_state.RcvWait)
      simp only [chan_phys, chan_logical]
      isplitl [state v slice slice_cap buffer]
      · iframe
      iexists iprop((recv_au γ V fun v ok => Φ (PairV (PairV #true #v) #ok)) ∧
        Φ (PairV (PairV #false #(zero_val V)) #true)),
        (fun (v : V) (ok : Bool) => Φ (PairV (PairV #true #v) #ok))
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
      simp only [chan_logical]
      iNamed offer
      ihave ⟨%Heq, -⟩ := saved_offer_agree γ V _ _ _ _ _ _ _ _ $$ [$offer2 $Hoffer]
      cases Heq
    | RcvWait =>
      iNamed phys
      simp only [chan_logical]
      iNamed offer
      imod saved_offer_lc_agree γ V _ _ _ _ _ _ $$ Hlc1 offer2 Hoffer with ⟨%Heq, #Hpeq, #H, H1⟩
      imod saved_pred_update_halves (Function.uncurry Φr0) _ _ _ $$ Hpred2 Hpred with ⟨Hp1, Hp2⟩
      ihave Hp := saved_pred_combine_halves _ _ _ $$ [$Hp1 $Hp2]
      wp_auto
      wp_apply wp_Mutex__Unlock $$ [$lock $Hlock state v slice slice_cap buffer Hp H1 offer]
      · iapply chan_inv_inner_intro _ _ _ (chan_phys_state.Idle)
        simp only [chan_phys, chan_logical]
        isplitl [state v slice slice_cap buffer]
        · iframe
        iexists Φr0
        iframe
      ihave HP := internal_eq_rewrite_wand $$ Hpeq HP
      icases HP with ⟨-, HP⟩
      iexact HP
    | SndDone v' =>
      iNamed phys
      simp only [chan_logical]
      iNamed offer
      iapply fupd_wp
      unfold recv_nested_au
      imod Hau with Hau
      imod lc_fupd_elim_later $$ Hlc1 Hau with Hau
      iNamed Hau
      ihave %Hseq := own_chan_agree _ _ _ _ $$ Hocinner offer
      subst Hseq
      imod own_chan_halves_update _ _ chanstate.t.Idle _ _ HcvIdle $$ Hocinner offer with ⟨Hgv1, Hgv2⟩
      dsimp only
      imod Hcontinner $$ Hgv1 with Hcont
      icases saved_pred_agree_keep _ _ _ _ _ (v', true) $$ [$Hpred2 $Hpred]
        with ⟨⟨Hpred2, Hpred⟩, Hagree⟩
      imod lc_fupd_elim_later $$ Hlc2 Hagree with #Hagree
      ihave Hp := saved_pred_combine_halves _ _ _ $$ [$Hpred2 $Hpred]
      imod saved_offer_lc_agree γ V _ _ _ _ _ _ $$ Hlc3 offer2 Hoffer with ⟨%Heq, #Hpeq, #H, H1⟩
      imodintro
      wp_auto
      wp_apply wp_Mutex__Unlock $$ [$lock $Hlock state v slice slice_cap buffer Hp H1 Hgv2]
      · iapply chan_inv_inner_intro _ _ _ (chan_phys_state.Idle)
        simp only [chan_phys, chan_logical]
        isplitl [state v slice slice_cap buffer]
        · iframe
        iexists _
        iframe
      simp only [Function.uncurry]
      iapply internal_eq_rewrite_wand $$ Hagree Hcont
    | RcvDone =>
      simp only [chan_logical]
      iNamed offer
      ihave ⟨%Heq, -⟩ := saved_offer_agree γ V _ _ _ _ _ _ _ _ $$ [$offer2 $Hoffer]
      cases Heq
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
    simp only [chan_logical]
    iNamed offer
    ihave %HcvIdle := own_chan_cap_valid _ _ _ $$ offer
    simp only [chan_cap_valid] at HcvIdle
    ihave HP := Hau $$ HP
    iapply fupd_wp
    unfold send_au
    imod HP with HP
    imod lc_fupd_elim_later $$ Hlc1 HP with HP
    iNamed HP
    ihave %Hseq := own_chan_agree _ _ _ _ $$ Hoc offer
    subst Hseq
    imod own_chan_halves_update _ _ (chanstate.t.SndPending v') _ _ HcvIdle $$ offer Hoc
      with ⟨Hgv1, Hgv2⟩
    dsimp only
    imod Hcont $$ Hgv2 with Hcont1
    icases HΦ with ⟨HΦ, -⟩
    unfold recv_au
    imod HΦ with HΦ
    imod lc_fupd_elim_later $$ Hlc2 HΦ with HΦ
    iNamed HΦ
    ihave %Hseq := own_chan_agree _ _ _ _ $$ Hgv1 Hoc
    subst Hseq
    imod own_chan_halves_update _ _ chanstate.t.RcvCommit _ _ HcvIdle $$ Hgv1 Hoc
      with ⟨Hgv1, Hgv2⟩
    dsimp only
    imod Hcont $$ Hgv2 with HΦ
    imodintro
    wp_apply wp_Mutex__Unlock $$ [$lock $Hlock state v slice slice_cap buffer Hgv1 Hcont1 Hpred Hoffer]
    · iapply chan_inv_inner_intro _ _ _ (chan_phys_state.RcvDone)
      simp only [chan_phys, chan_logical]
      isplitl [state v slice slice_cap buffer]
      · iframe
      iexists P0, Φ0, Φr0, v'
      iframe
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
  | Closed buffer =>
    cases buffer with
    | nil =>
      iNamed phys
      simp only [chan_logical]
      icases offer with ⟨Hoc0, Hoffer⟩
      ihave %Hlen := own_slice_len _ _ _ $$ slice
      wp_auto
      icases HΦ with ⟨HΦ, -⟩
      iapply fupd_wp
      unfold recv_au
      imod HΦ with HΦ
      imod lc_fupd_elim_later $$ Hlc1 HΦ with HΦ
      iNamed HΦ
      ihave %Hseq := own_chan_agree _ _ _ _ $$ Hoc Hoc0
      subst Hseq
      dsimp only
      imod Hcont $$ Hoc with HΦ
      imodintro
      wp_if_destruct
      · exfalso; simp at Hlen; revert Hif Hlen; word
      wp_apply wp_Mutex__Unlock $$ [$lock $Hlock state slice slice_cap buffer Hoc0 Hoffer]
      · iapply chan_inv_inner_intro _ _ _ (chan_phys_state.Closed [])
        simp only [chan_phys, chan_logical]
        iframe
      iexact HΦ
    | cons x rest =>
      iNamed phys
      simp only [chan_logical]
      ihave %Hcv := own_chan_cap_valid _ _ _ $$ offer
      -- `word` fails with an unfolded `chan_cap_valid` hypothesis in context
      simp only [chan_cap_valid] at Hcv
      ihave %Hlen := own_slice_len _ _ _ $$ slice
      ihave %Hwf := own_slice_cap_wf (V := V) _ _ $$ slice_cap
      simp only [List.length_cons] at Hlen
      wp_auto
      wp_if_destruct
      · icases HΦ with ⟨HΦ, -⟩
        iapply fupd_wp
        unfold recv_au
        imod HΦ with HΦ
        imod lc_fupd_elim_later $$ Hlc1 HΦ with HΦ
        iNamed HΦ
        ihave %Heq := own_chan_agree _ _ _ _ $$ offer Hoc
        subst Heq
        imod own_chan_halves_update _ _ (chanstate.t.Closed rest) _ _ ?_ $$ Hoc offer
          with ⟨Hgv1, Hgv2⟩
        · simp only [chan_cap_valid, List.length_cons] at Hcv ⊢
          cases rest <;> simp only [List.length_cons, List.length_nil] at Hcv ⊢ <;> word
        dsimp only
        imod Hcont $$ Hgv1 with HΦ
        imodintro
        rw [ite_eq_left ⟨by decide, by word⟩]
        wp_apply wp_load_slice_index slice_val (sint.Z (W64 0)) _ _ x (by decide) $$ [$slice] as slice
        · ipureintro; rfl
        rw [ite_eq_left ⟨by decide, by word, Hwf.2⟩]
        wp_auto
        icases own_slice_pop _ _ _ $$ slice slice_cap with ⟨slice, slice_cap⟩
        wp_apply wp_Mutex__Unlock $$ [$lock $Hlock state buffer slice slice_cap Hgv2]
        · iapply chan_inv_inner_intro _ _ _ (chan_phys_state.Closed rest)
          cases rest with
          | nil =>
            simp only [chan_phys, chan_logical]
            iframe
            iintro %Hcap0
            exfalso
            simp only [chan_cap_valid, List.length_cons, List.length_nil] at Hcv
            rw [Hcap0] at Hcv
            exact absurd Hcv.2 (by decide)
          | cons y ys =>
            simp only [chan_phys, chan_logical]
            iframe
        iexact HΦ
      · exfalso; revert Hif Hlen; word

set_option maxHeartbeats 400000 in
theorem wp_TryReceive_nonblocking (ch : loc) (γ : chan_names) :
    ⊢ ∀ Φ : val → IProp GF, is_chan ch γ V -∗
      nonblocking_recv_au γ V (fun v ok => Φ (PairV (PairV #true #v) #ok))
        (Φ (PairV (PairV #false #(zero_val V)) #true)) -∗
      WP (App (Val (ch @!! go.type.PointerType (channel.Channel t) @!! go!"TryReceive"))
        (Val #false)) {{ Φ }} := by
  wp_start as Hch
  rw [is_chan_unseal]
  iNamed Hch
  chan_unfold_consts
  wp_auto_lc 9
  rw [is_lock_eq_is_Mutex] at *
  wp_apply wp_Mutex__Lock $$ [$lock] as ⟨Hlock, Hchan⟩
  iNamed Hchan
  unfold nonblocking_recv_au nonblocking_recv_au_inner
  cases s with
  | Buffered buffer =>
    iNamed phys
    simp only [chan_logical]
    ihave %Hcv := own_chan_cap_valid _ _ _ $$ offer
    -- `word` fails with an unfolded `chan_cap_valid` hypothesis in context
    simp only [chan_cap_valid] at Hcv
    ihave %Hlen := own_slice_len _ _ _ $$ slice
    ihave %Hwf := own_slice_cap_wf (V := V) _ _ $$ slice_cap
    wp_auto
    wp_if_destruct
    · cases buffer with
      | nil => exfalso; simp at Hlen; revert Hif Hlen; word
      | cons x rest =>
      icases HΦ with ⟨HΦ, -⟩
      iapply fupd_wp
      imod HΦ with HΦ
      imod lc_fupd_elim_later $$ Hlc1 HΦ with HΦ
      iNamed HΦ
      ihave %Heq := own_chan_agree _ _ _ _ $$ offer Hoc
      subst Heq
      imod own_chan_halves_update _ _ (chanstate.t.Buffered rest) _ _ ?_ $$ Hoc offer
        with ⟨Hgv1, Hgv2⟩
      · simp only [chan_cap_valid, List.length_cons] at Hcv ⊢
        constructor <;> word
      dsimp only
      imod Hcont $$ Hgv1 with HΦ
      imodintro
      rw [ite_eq_left ⟨by decide, by word⟩]
      wp_apply wp_load_slice_index slice_val (sint.Z (W64 0)) _ _ x (by decide) $$ [$slice] as slice
      · ipureintro; rfl
      simp only [List.length_cons] at Hlen
      rw [ite_eq_left ⟨by decide, by word, Hwf.2⟩]
      wp_auto
      icases own_slice_pop _ _ _ $$ slice slice_cap with ⟨slice, slice_cap⟩
      wp_apply wp_Mutex__Unlock $$ [$lock $Hlock state buffer slice slice_cap Hgv2]
      · iapply chan_inv_inner_intro _ _ _ (chan_phys_state.Buffered rest)
        simp only [chan_phys, chan_logical]
        iframe
      iexact HΦ
    · cases buffer with
      | cons x rest => exfalso; simp at Hlen; revert Hif Hlen; word
      | nil =>
      wp_apply wp_Mutex__Unlock $$ [$lock $Hlock state buffer slice slice_cap offer]
      · iapply chan_inv_inner_intro _ _ _ (chan_phys_state.Buffered [])
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
    simp only [chan_logical]
    iNamed offer
    ihave %HcvIdle := own_chan_cap_valid _ _ _ $$ offer
    simp only [chan_cap_valid] at HcvIdle
    ihave HP := Hau $$ HP
    iapply fupd_wp
    unfold send_au
    imod HP with HP
    imod lc_fupd_elim_later $$ Hlc1 HP with HP
    iNamed HP
    ihave %Hseq := own_chan_agree _ _ _ _ $$ Hoc offer
    subst Hseq
    imod own_chan_halves_update _ _ (chanstate.t.SndPending v') _ _ HcvIdle $$ offer Hoc
      with ⟨Hgv1, Hgv2⟩
    dsimp only
    imod Hcont $$ Hgv2 with Hcont1
    icases HΦ with ⟨HΦ, -⟩
    imod HΦ with HΦ
    imod lc_fupd_elim_later $$ Hlc2 HΦ with HΦ
    iNamed HΦ
    ihave %Hseq := own_chan_agree _ _ _ _ $$ Hgv1 Hoc
    subst Hseq
    imod own_chan_halves_update _ _ chanstate.t.RcvCommit _ _ HcvIdle $$ Hgv1 Hoc
      with ⟨Hgv1, Hgv2⟩
    dsimp only
    imod Hcont $$ Hgv2 with HΦ
    imodintro
    wp_apply wp_Mutex__Unlock $$ [$lock $Hlock state v slice slice_cap buffer Hgv1 Hcont1 Hpred Hoffer]
    · iapply chan_inv_inner_intro _ _ _ (chan_phys_state.RcvDone)
      simp only [chan_phys, chan_logical]
      isplitl [state v slice slice_cap buffer]
      · iframe
      iexists P0, Φ0, Φr0, v'
      iframe
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
  | Closed buffer =>
    cases buffer with
    | nil =>
      iNamed phys
      simp only [chan_logical]
      icases offer with ⟨Hoc0, Hoffer⟩
      ihave %Hlen := own_slice_len _ _ _ $$ slice
      wp_auto
      icases HΦ with ⟨HΦ, -⟩
      iapply fupd_wp
      imod HΦ with HΦ
      imod lc_fupd_elim_later $$ Hlc1 HΦ with HΦ
      iNamed HΦ
      ihave %Hseq := own_chan_agree _ _ _ _ $$ Hoc Hoc0
      subst Hseq
      dsimp only
      imod Hcont $$ Hoc with HΦ
      imodintro
      wp_if_destruct
      · exfalso; simp at Hlen; revert Hif Hlen; word
      wp_apply wp_Mutex__Unlock $$ [$lock $Hlock state slice slice_cap buffer Hoc0 Hoffer]
      · iapply chan_inv_inner_intro _ _ _ (chan_phys_state.Closed [])
        simp only [chan_phys, chan_logical]
        iframe
      iexact HΦ
    | cons x rest =>
      iNamed phys
      simp only [chan_logical]
      ihave %Hcv := own_chan_cap_valid _ _ _ $$ offer
      -- `word` fails with an unfolded `chan_cap_valid` hypothesis in context
      simp only [chan_cap_valid] at Hcv
      ihave %Hlen := own_slice_len _ _ _ $$ slice
      ihave %Hwf := own_slice_cap_wf (V := V) _ _ $$ slice_cap
      simp only [List.length_cons] at Hlen
      wp_auto
      wp_if_destruct
      · icases HΦ with ⟨HΦ, -⟩
        iapply fupd_wp
        imod HΦ with HΦ
        imod lc_fupd_elim_later $$ Hlc1 HΦ with HΦ
        iNamed HΦ
        ihave %Heq := own_chan_agree _ _ _ _ $$ offer Hoc
        subst Heq
        imod own_chan_halves_update _ _ (chanstate.t.Closed rest) _ _ ?_ $$ Hoc offer
          with ⟨Hgv1, Hgv2⟩
        · simp only [chan_cap_valid, List.length_cons] at Hcv ⊢
          cases rest <;> simp only [List.length_cons, List.length_nil] at Hcv ⊢ <;> word
        dsimp only
        imod Hcont $$ Hgv1 with HΦ
        imodintro
        rw [ite_eq_left ⟨by decide, by word⟩]
        wp_apply wp_load_slice_index slice_val (sint.Z (W64 0)) _ _ x (by decide) $$ [$slice] as slice
        · ipureintro; rfl
        rw [ite_eq_left ⟨by decide, by word, Hwf.2⟩]
        wp_auto
        icases own_slice_pop _ _ _ $$ slice slice_cap with ⟨slice, slice_cap⟩
        wp_apply wp_Mutex__Unlock $$ [$lock $Hlock state buffer slice slice_cap Hgv2]
        · iapply chan_inv_inner_intro _ _ _ (chan_phys_state.Closed rest)
          cases rest with
          | nil =>
            simp only [chan_phys, chan_logical]
            iframe
            iintro %Hcap0
            exfalso
            simp only [chan_cap_valid, List.length_cons, List.length_nil] at Hcv
            rw [Hcap0] at Hcv
            exact absurd Hcv.2 (by decide)
          | cons y ys =>
            simp only [chan_phys, chan_logical]
            iframe
        iexact HΦ
      · exfalso; revert Hif Hlen; word

set_option maxHeartbeats 400000 in
theorem wp_TryReceive_nonblocking_alt (ch : loc) (γ : chan_names) :
    ⊢ ∀ Φ : val → IProp GF, is_chan ch γ V -∗
      nonblocking_recv_au_alt γ V (fun v ok => Φ (PairV (PairV #true #v) #ok))
        (Φ (PairV (PairV #false #(zero_val V)) #true)) -∗
      WP (App (Val (ch @!! go.type.PointerType (channel.Channel t) @!! go!"TryReceive"))
        (Val #false)) {{ Φ }} := by
  wp_start as Hch
  rw [is_chan_unseal]
  iNamed Hch
  chan_unfold_consts
  wp_auto_lc 9
  rw [is_lock_eq_is_Mutex] at *
  wp_apply wp_Mutex__Lock $$ [$lock] as ⟨Hlock, Hchan⟩
  iNamed Hchan
  unfold nonblocking_recv_au_alt
  cases s with
  | Buffered buffer =>
    iNamed phys
    simp only [chan_logical]
    ihave %Hcv := own_chan_cap_valid _ _ _ $$ offer
    -- `word` fails with an unfolded `chan_cap_valid` hypothesis in context
    simp only [chan_cap_valid] at Hcv
    ihave %Hlen := own_slice_len _ _ _ $$ slice
    ihave %Hwf := own_slice_cap_wf (V := V) _ _ $$ slice_cap
    wp_auto
    wp_if_destruct
    · cases buffer with
      | nil => exfalso; simp at Hlen; revert Hif Hlen; word
      | cons x rest =>
      iapply fupd_wp
      imod HΦ with HΦ
      imod lc_fupd_elim_later $$ Hlc1 HΦ with HΦ
      iNamed HΦ
      ihave %Heq := own_chan_agree _ _ _ _ $$ offer Hoc
      subst Heq
      imod own_chan_halves_update _ _ (chanstate.t.Buffered rest) _ _ ?_ $$ Hoc offer
        with ⟨Hgv1, Hgv2⟩
      · simp only [chan_cap_valid, List.length_cons] at Hcv ⊢
        constructor <;> word
      dsimp only
      imod Hcont $$ Hgv1 with HΦ
      imodintro
      rw [ite_eq_left ⟨by decide, by word⟩]
      wp_apply wp_load_slice_index slice_val (sint.Z (W64 0)) _ _ x (by decide) $$ [$slice] as slice
      · ipureintro; rfl
      simp only [List.length_cons] at Hlen
      rw [ite_eq_left ⟨by decide, by word, Hwf.2⟩]
      wp_auto
      icases own_slice_pop _ _ _ $$ slice slice_cap with ⟨slice, slice_cap⟩
      wp_apply wp_Mutex__Unlock $$ [$lock $Hlock state buffer slice slice_cap Hgv2]
      · iapply chan_inv_inner_intro _ _ _ (chan_phys_state.Buffered rest)
        simp only [chan_phys, chan_logical]
        iframe
      iexact HΦ
    · cases buffer with
      | cons x rest => exfalso; simp at Hlen; revert Hif Hlen; word
      | nil =>
      iapply fupd_wp
      imod HΦ with HΦ
      imod lc_fupd_elim_later $$ Hlc1 HΦ with HΦ
      iNamed HΦ
      ihave %Hseq := own_chan_agree _ _ _ _ $$ Hoc offer
      subst Hseq
      dsimp only
      imod Hcont $$ Hoc with HΦ
      imodintro
      wp_apply wp_Mutex__Unlock $$ [$lock $Hlock state buffer slice slice_cap offer]
      · iapply chan_inv_inner_intro _ _ _ (chan_phys_state.Buffered [])
        simp only [chan_phys, chan_logical]
        iframe
      iexact HΦ
  | Idle =>
    iNamed phys
    wp_auto
    simp only [chan_logical]
    iNamed offer
    iapply fupd_wp
    imod HΦ with HΦ
    imod lc_fupd_elim_later $$ Hlc1 HΦ with HΦ
    iNamed HΦ
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
    simp only [chan_logical]
    iNamed offer
    ihave %HcvIdle := own_chan_cap_valid _ _ _ $$ offer
    simp only [chan_cap_valid] at HcvIdle
    ihave HP := Hau $$ HP
    iapply fupd_wp
    unfold send_au
    imod HP with HP
    imod lc_fupd_elim_later $$ Hlc1 HP with HP
    iNamed HP
    ihave %Hseq := own_chan_agree _ _ _ _ $$ Hoc offer
    subst Hseq
    imod own_chan_halves_update _ _ (chanstate.t.SndPending v') _ _ HcvIdle $$ offer Hoc
      with ⟨Hgv1, Hgv2⟩
    dsimp only
    imod Hcont $$ Hgv2 with Hcont1
    imod HΦ with HΦ
    imod lc_fupd_elim_later $$ Hlc2 HΦ with HΦ
    iNamed HΦ
    ihave %Hseq := own_chan_agree _ _ _ _ $$ Hgv1 Hoc
    subst Hseq
    imod own_chan_halves_update _ _ chanstate.t.RcvCommit _ _ HcvIdle $$ Hgv1 Hoc
      with ⟨Hgv1, Hgv2⟩
    dsimp only
    imod Hcont $$ Hgv2 with HΦ
    imodintro
    wp_apply wp_Mutex__Unlock $$ [$lock $Hlock state v slice slice_cap buffer Hgv1 Hcont1 Hpred Hoffer]
    · iapply chan_inv_inner_intro _ _ _ (chan_phys_state.RcvDone)
      simp only [chan_phys, chan_logical]
      isplitl [state v slice slice_cap buffer]
      · iframe
      iexists P0, Φ0, Φr0, v'
      iframe
    iexact HΦ
  | RcvWait =>
    iNamed phys
    wp_auto
    simp only [chan_logical]
    iNamed offer
    iapply fupd_wp
    imod HΦ with HΦ
    imod lc_fupd_elim_later $$ Hlc1 HΦ with HΦ
    iNamed HΦ
    ihave %Hseq := own_chan_agree _ _ _ _ $$ Hoc offer
    subst Hseq
    dsimp only
    imod Hcont $$ Hoc with HΦ
    imodintro
    wp_apply wp_Mutex__Unlock $$ [$lock $Hlock state v slice slice_cap buffer Hoffer HP Hpred Hau offer]
    · iapply chan_inv_inner_intro _ _ _ (chan_phys_state.RcvWait)
      simp only [chan_phys, chan_logical]
      isplitl [state v slice slice_cap buffer]
      · iframe
      iexists P0, Φr0
      iframe
    iexact HΦ
  | SndDone v' =>
    iNamed phys
    wp_auto
    simp only [chan_logical]
    iNamed offer
    iapply fupd_wp
    imod HΦ with HΦ
    imod lc_fupd_elim_later $$ Hlc1 HΦ with HΦ
    iNamed HΦ
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
    simp only [chan_logical]
    iNamed offer
    iapply fupd_wp
    imod HΦ with HΦ
    imod lc_fupd_elim_later $$ Hlc1 HΦ with HΦ
    iNamed HΦ
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
  | Closed buffer =>
    cases buffer with
    | nil =>
      iNamed phys
      simp only [chan_logical]
      icases offer with ⟨Hoc0, Hoffer⟩
      ihave %Hlen := own_slice_len _ _ _ $$ slice
      wp_auto
      iapply fupd_wp
      imod HΦ with HΦ
      imod lc_fupd_elim_later $$ Hlc1 HΦ with HΦ
      iNamed HΦ
      ihave %Hseq := own_chan_agree _ _ _ _ $$ Hoc Hoc0
      subst Hseq
      dsimp only
      imod Hcont $$ Hoc with HΦ
      imodintro
      wp_if_destruct
      · exfalso; simp at Hlen; revert Hif Hlen; word
      wp_apply wp_Mutex__Unlock $$ [$lock $Hlock state slice slice_cap buffer Hoc0 Hoffer]
      · iapply chan_inv_inner_intro _ _ _ (chan_phys_state.Closed [])
        simp only [chan_phys, chan_logical]
        iframe
      iexact HΦ
    | cons x rest =>
      iNamed phys
      simp only [chan_logical]
      ihave %Hcv := own_chan_cap_valid _ _ _ $$ offer
      -- `word` fails with an unfolded `chan_cap_valid` hypothesis in context
      simp only [chan_cap_valid] at Hcv
      ihave %Hlen := own_slice_len _ _ _ $$ slice
      ihave %Hwf := own_slice_cap_wf (V := V) _ _ $$ slice_cap
      simp only [List.length_cons] at Hlen
      wp_auto
      wp_if_destruct
      · iapply fupd_wp
        imod HΦ with HΦ
        imod lc_fupd_elim_later $$ Hlc1 HΦ with HΦ
        iNamed HΦ
        ihave %Heq := own_chan_agree _ _ _ _ $$ offer Hoc
        subst Heq
        imod own_chan_halves_update _ _ (chanstate.t.Closed rest) _ _ ?_ $$ Hoc offer
          with ⟨Hgv1, Hgv2⟩
        · simp only [chan_cap_valid, List.length_cons] at Hcv ⊢
          cases rest <;> simp only [List.length_cons, List.length_nil] at Hcv ⊢ <;> word
        dsimp only
        imod Hcont $$ Hgv1 with HΦ
        imodintro
        rw [ite_eq_left ⟨by decide, by word⟩]
        wp_apply wp_load_slice_index slice_val (sint.Z (W64 0)) _ _ x (by decide) $$ [$slice] as slice
        · ipureintro; rfl
        rw [ite_eq_left ⟨by decide, by word, Hwf.2⟩]
        wp_auto
        icases own_slice_pop _ _ _ $$ slice slice_cap with ⟨slice, slice_cap⟩
        wp_apply wp_Mutex__Unlock $$ [$lock $Hlock state buffer slice slice_cap Hgv2]
        · iapply chan_inv_inner_intro _ _ _ (chan_phys_state.Closed rest)
          cases rest with
          | nil =>
            simp only [chan_phys, chan_logical]
            iframe
            iintro %Hcap0
            exfalso
            simp only [chan_cap_valid, List.length_cons, List.length_nil] at Hcv
            rw [Hcap0] at Hcv
            exact absurd Hcv.2 (by decide)
          | cons y ys =>
            simp only [chan_phys, chan_logical]
            iframe
        iexact HΦ
      · exfalso; revert Hif Hlen; word

theorem wp_TryReceive (ch : loc) (γ : chan_names) (blocking : Bool) :
    ⊢ ∀ Φ : val → IProp GF, is_chan ch γ V -∗
      (if blocking then
        iprop(recv_au γ V (fun v ok => Φ (PairV (PairV #true #v) #ok)) ∧
          Φ (PairV (PairV #false #(zero_val V)) #true))
       else iprop(nonblocking_recv_au γ V (fun v ok => Φ (PairV (PairV #true #v) #ok))
           (Φ (PairV (PairV #false #(zero_val V)) #true)) ∨
         nonblocking_recv_au_alt γ V (fun v ok => Φ (PairV (PairV #true #v) #ok))
           (Φ (PairV (PairV #false #(zero_val V)) #true)))) -∗
      WP (App (Val (ch @!! go.type.PointerType (channel.Channel t) @!! go!"TryReceive"))
        (Val #blocking)) {{ Φ }} := by
  iintro %Φ #Hch HΦ
  cases blocking with
  | true =>
    simp only [↓reduceIte]
    iapply wp_TryReceive_blocking $$ Hch HΦ
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases HΦ with (HΦ | HΦ)
    · iapply wp_TryReceive_nonblocking $$ Hch HΦ
    · iapply wp_TryReceive_nonblocking_alt $$ Hch HΦ

set_option maxHeartbeats 400000 in
theorem wp_Receive (ch : loc) (γ : chan_names) :
    ⊢ ∀ Φ : val → IProp GF, is_chan ch γ V -∗
      (£ 1 ∗ £ 1 ∗ £ 1 ∗ £ 1 -∗ recv_au γ V (fun v ok => Φ (PairV #v #ok))) -∗
      WP (App (Val (ch @!! go.type.PointerType (channel.Channel t) @!! go!"Receive")) (Val #())) {{ Φ }} := by
  wp_start as #Hic
  ihave %Hnn := is_chan_not_null _ _ _ $$ Hic
  wp_auto_lc 4
  ispecialize HΦ $$ [Hlc1 Hlc2 Hlc3 Hlc4]
  · iframe
  wp_if_destruct
  · exact absurd rfl Hnn
  wp_for
  wp_apply wp_TryReceive ch γ true $$ Hic
  simp only [↓reduceIte]
  isplit
  · iapply recv_au_wand $$ HΦ
    iintro %v %ok HΦ
    wp_auto
    wp_for_post
    iexact HΦ
  · wp_auto
    wp_for_post
    iframe

end atomic_specs

end Perennial
