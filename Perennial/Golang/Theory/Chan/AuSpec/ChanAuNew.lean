/-
Port of `new/golang/theory/chan/au_spec/chan_au_new.v`: the specification of
`channel.NewChannel`.
-/
import Perennial.Golang.Theory.Chan.AuSpec.ChanAuBase

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE
open github_com.mit_pdos.perennial.goose.model

section new_spec
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF] [allG GF]
variable [sem_fn : GoSemanticsFunctions] [pre_sem : go.PreSemantics] [sem : go.ChanSemantics]
variable {V : Type} [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V] {t : go.type}
  [IntoValTyped (GF := GF) V t]

set_option goose.wp.extras true in
set_option maxHeartbeats 400000 in
theorem wp_NewChannel (cap : w64) :
    {{ (⌜0 ≤ sint.Z cap⌝ : IProp GF) }}
      (App (Val #(functions channel.NewChannel [t])) (Val #cap))
    {{ (ch : loc) (γ : chan_names), RET #ch;
        is_chan ch γ V ∗
        ⌜γ.chan_cap = cap⌝ ∗
        own_chan γ V (if cap = W64 0 then chanstate.t.Idle else chanstate.t.Buffered ([] : List V)) }} := by
  wp_start as %Hle
  wp_auto
  simp only [channel.idle, channel.buffered]
  wp_auto
  wp_if_destruct
  · wp_apply wp_slice_make2 (V := V) $$ [] as %sl ⟨Hsl, Hslcap⟩
    · ipureintro; decide
    iapply wp_fupd
    wp_alloc ch as Hch
    wp_auto
    ihave %Hnot_null := typed_pointsto_not_null _ _ _ $$ Hch
    iStructNamed Hch
    imod ghost_var_alloc (chanstate.t.Buffered ([] : List V)) with ⟨%state_gname, Hstate⟩
    icases ghost_var_halves _ _ $$ Hstate with ⟨Hstate_auth, Hstate_frag⟩
    imod ghost_var_alloc (none : Option (offer_lock V)) with ⟨%offer_lock_gname, Hoffer_lock⟩
    imod saved_prop_alloc iprop(True) (DFrac.own 1) DFrac.valid_own_one
      with ⟨%offer_parked_prop_gname, Hparked_prop⟩
    imod saved_pred_alloc (Function.uncurry (fun (_ : V) (_ : Bool) => (iprop(True) : IProp GF)))
      (DFrac.own 1) DFrac.valid_own_one with ⟨%offer_parked_pred_gname, Hparked_pred⟩
    imod saved_prop_alloc iprop(True) (DFrac.own 1) DFrac.valid_own_one
      with ⟨%offer_continuation_gname, Hcontinuation⟩
    ipersist cap
    ipersist mu
    imod init_lock (chan_inv_inner ch ⟨state_gname, offer_lock_gname, offer_parked_prop_gname,
      offer_parked_pred_gname, offer_continuation_gname, cap⟩ V) ⊤ «$v1_ptr» $$ «$v1»
      [-HΦ Hstate_frag] with #Hlock
    · inext
      unfold chan_inv_inner
      iexists (chan_phys_state.Buffered [])
      simp only [chan_phys, chan_logical, show sint.nat (W64 0) = 0 from rfl, List.replicate,
        own_chan_unseal, own_chan_def, chanstate]
      isplitl [Hsl Hslcap state buffer]
      · iexists sl
        iframe
      · isplitl [Hstate_auth]
        · iexact Hstate_auth
        · ipureintro
          simp only [chan_cap_valid, List.length_nil]
          constructor <;> word
    imodintro
    ispecialize HΦ $$ %ch %(chan_names.mk state_gname offer_lock_gname offer_parked_prop_gname
      offer_parked_pred_gname offer_continuation_gname cap)
    iapply HΦ
    have hne : cap ≠ W64 0 := by intro h; subst h; exact absurd Hif (by decide)
    simp only [hne, ↓reduceIte, is_chan_unseal, is_chan_def, own_chan_unseal, own_chan_def, chanstate]
    isplitl []
    · iexists «$v1_ptr»
      iframe #
      ipureintro
      exact ⟨Hnot_null, Hle⟩
    isplitl []
    · ipureintro; trivial
    isplitl [Hstate_frag]
    · iexact Hstate_frag
    · ipureintro
      simp only [chan_cap_valid, List.length_nil]
      constructor <;> word
  · have hcap : cap = W64 0 := by word
    subst hcap
    wp_apply wp_slice_make2 (V := V) $$ [] as %sl ⟨Hsl, Hslcap⟩
    · ipureintro; decide
    iapply wp_fupd
    wp_alloc ch as Hch
    wp_auto
    ihave %Hnot_null := typed_pointsto_not_null _ _ _ $$ Hch
    iStructNamed Hch
    imod ghost_var_alloc (chanstate.t.Idle (V := V)) with ⟨%state_gname, Hstate⟩
    icases ghost_var_halves _ _ $$ Hstate with ⟨Hstate_auth, Hstate_frag⟩
    imod ghost_var_alloc (none : Option (offer_lock V)) with ⟨%offer_lock_gname, Hoffer_lock⟩
    imod saved_prop_alloc iprop(True) (DFrac.own 1) DFrac.valid_own_one
      with ⟨%offer_parked_prop_gname, Hparked_prop⟩
    imod saved_pred_alloc (Function.uncurry (fun (_ : V) (_ : Bool) => (iprop(True) : IProp GF)))
      (DFrac.own 1) DFrac.valid_own_one with ⟨%offer_parked_pred_gname, Hparked_pred⟩
    imod saved_prop_alloc iprop(True) (DFrac.own 1) DFrac.valid_own_one
      with ⟨%offer_continuation_gname, Hcontinuation⟩
    ipersist cap
    ipersist mu
    imod init_lock (chan_inv_inner ch ⟨state_gname, offer_lock_gname, offer_parked_prop_gname,
      offer_parked_pred_gname, offer_continuation_gname, W64 0⟩ V) ⊤ «$v1_ptr» $$ «$v1»
      [-HΦ Hstate_frag] with #Hlock
    · inext
      unfold chan_inv_inner
      iexists (chan_phys_state.Idle (V := V))
      simp only [chan_phys, chan_logical, show sint.nat (W64 0) = 0 from rfl, List.replicate,
        own_chan_unseal, own_chan_def, chanstate, saved_offer]
      isplitl [Hsl Hslcap state buffer v]
      · iexists _, sl
        iframe
      · iexists (fun (_ : V) (_ : Bool) => (iprop(True) : IProp GF))
        iframe
        isplitl [Hoffer_lock Hparked_prop Hcontinuation]
        · isplitl [Hoffer_lock]
          · iexact Hoffer_lock
          · iframe
        · ipureintro
          simp only [chan_cap_valid]
          decide
    imodintro
    ispecialize HΦ $$ %ch %(chan_names.mk state_gname offer_lock_gname offer_parked_prop_gname
      offer_parked_pred_gname offer_continuation_gname (W64 0))
    iapply HΦ
    simp only [↓reduceIte, is_chan_unseal, is_chan_def, own_chan_unseal, own_chan_def, chanstate]
    isplitl []
    · iexists «$v1_ptr»
      iframe #
      ipureintro
      exact ⟨Hnot_null, by decide⟩
    isplitl []
    · ipureintro; trivial
    isplitl [Hstate_frag]
    · iexact Hstate_frag
    · ipureintro
      simp only [chan_cap_valid]
      decide

end new_spec

end Perennial
