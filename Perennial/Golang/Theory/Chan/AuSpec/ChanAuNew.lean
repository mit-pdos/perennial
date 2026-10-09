/-
The specification of
`channel.NewChannel`.
-/
module

public import Perennial.Golang.Theory.Chan.AuSpec.ChanAuBase

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE
open github_com.mit_pdos.perennial.goose.model

section new_spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem_fn : GoSemanticsFunctions] [pre_sem : go.PreSemantics] [sem : go.ChanSemantics]
variable {V : Type} [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V] {t : go.GoType}
  [IntoValTyped (GF := GF) V t]

set_option goose.wp.extras true in
set_option maxHeartbeats 400000 in
theorem wp_NewChannel (cap : w64) :
    {{ (⌜0 ≤ sint.Z cap⌝ : IProp GF) }}
      (App (Val #(functions channel.NewChannel [t])) (Val #cap))
    {{ (ch : Loc) (γ : ChanNames), RET #ch;
        isChan ch γ V ∗
        ⌜γ.chanCap = cap⌝ ∗
        ownChan γ V (if cap = W64 0 then ChanState.Idle else ChanState.Buffered ([] : List V)) }} := by
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
    ihave %Hnot_null := typedPointsto_not_null _ _ _ $$ Hch
    iStructNamed Hch
    imod ghostVar_alloc (ChanState.Buffered ([] : List V)) with ⟨%state_gname, Hstate⟩
    icases ghostVar_halves _ _ $$ Hstate with ⟨Hstate_auth, Hstate_frag⟩
    imod ghostVar_alloc (none : Option (OfferLock V)) with ⟨%offer_lock_gname, Hoffer_lock⟩
    imod saved_prop_alloc iprop(True) (DFrac.own 1) DFrac.valid_own_one
      with ⟨%offer_parked_prop_gname, Hparked_prop⟩
    imod saved_pred_alloc (Function.uncurry (fun (_ : V) (_ : Bool) => (iprop(True) : IProp GF)))
      (DFrac.own 1) DFrac.valid_own_one with ⟨%offer_parked_pred_gname, Hparked_pred⟩
    imod saved_prop_alloc iprop(True) (DFrac.own 1) DFrac.valid_own_one
      with ⟨%offer_continuation_gname, Hcontinuation⟩
    ipersist cap
    ipersist mu
    imod init_lock (chanInvInner ch ⟨state_gname, offer_lock_gname, offer_parked_prop_gname,
      offer_parked_pred_gname, offer_continuation_gname, cap⟩ V) ⊤ «$v1_ptr» $$ «$v1»
      [-HΦ Hstate_frag] with #Hlock
    · inext
      unfold chanInvInner
      iexists (ChanPhysState.Buffered [])
      simp only [chanPhys, chanLogical, show sint.nat (W64 0) = 0 from rfl, List.replicate,
        ownChan_unseal, ownChanDef, chanstate]
      isplitl [Hsl Hslcap state buffer]
      · iexists sl
        iframe
      · isplitl [Hstate_auth]
        · iexact Hstate_auth
        · ipureintro
          simp only [ChanCapValid, List.length_nil]
          constructor <;> word
    imodintro
    ispecialize HΦ $$ %ch %(ChanNames.mk state_gname offer_lock_gname offer_parked_prop_gname
      offer_parked_pred_gname offer_continuation_gname cap)
    iapply HΦ
    have hne : cap ≠ W64 0 := by intro h; subst h; exact absurd Hif (by decide)
    simp only [hne, ↓reduceIte, isChan_unseal, isChanDef, ownChan_unseal, ownChanDef, chanstate]
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
      simp only [ChanCapValid, List.length_nil]
      constructor <;> word
  · have hcap : cap = W64 0 := by word
    subst hcap
    wp_apply wp_slice_make2 (V := V) $$ [] as %sl ⟨Hsl, Hslcap⟩
    · ipureintro; decide
    iapply wp_fupd
    wp_alloc ch as Hch
    wp_auto
    ihave %Hnot_null := typedPointsto_not_null _ _ _ $$ Hch
    iStructNamed Hch
    imod ghostVar_alloc (ChanState.Idle (V := V)) with ⟨%state_gname, Hstate⟩
    icases ghostVar_halves _ _ $$ Hstate with ⟨Hstate_auth, Hstate_frag⟩
    imod ghostVar_alloc (none : Option (OfferLock V)) with ⟨%offer_lock_gname, Hoffer_lock⟩
    imod saved_prop_alloc iprop(True) (DFrac.own 1) DFrac.valid_own_one
      with ⟨%offer_parked_prop_gname, Hparked_prop⟩
    imod saved_pred_alloc (Function.uncurry (fun (_ : V) (_ : Bool) => (iprop(True) : IProp GF)))
      (DFrac.own 1) DFrac.valid_own_one with ⟨%offer_parked_pred_gname, Hparked_pred⟩
    imod saved_prop_alloc iprop(True) (DFrac.own 1) DFrac.valid_own_one
      with ⟨%offer_continuation_gname, Hcontinuation⟩
    ipersist cap
    ipersist mu
    imod init_lock (chanInvInner ch ⟨state_gname, offer_lock_gname, offer_parked_prop_gname,
      offer_parked_pred_gname, offer_continuation_gname, W64 0⟩ V) ⊤ «$v1_ptr» $$ «$v1»
      [-HΦ Hstate_frag] with #Hlock
    · inext
      unfold chanInvInner
      iexists (ChanPhysState.Idle (V := V))
      simp only [chanPhys, chanLogical, show sint.nat (W64 0) = 0 from rfl, List.replicate,
        ownChan_unseal, ownChanDef, chanstate, savedOffer]
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
          simp only [ChanCapValid]
          decide
    imodintro
    ispecialize HΦ $$ %ch %(ChanNames.mk state_gname offer_lock_gname offer_parked_prop_gname
      offer_parked_pred_gname offer_continuation_gname (W64 0))
    iapply HΦ
    simp only [↓reduceIte, isChan_unseal, isChanDef, ownChan_unseal, ownChanDef, chanstate]
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
      simp only [ChanCapValid]
      decide

set_option goose.wp.extras true in
set_option maxHeartbeats 400000 in
/-- `wp_NewChannel` for an unbuffered channel, given the (persistent) `cap` field of an
existing channel `l`: the new channel is not `l` (its `cap` field is freshly allocated). -/
theorem wp_NewChannel_unbuffered_ne (l : Loc) (x : w64) :
    {{ (l.[channel.Channel V, go!"cap"] ↦□ x : IProp GF) }}
      (App (Val #(functions channel.NewChannel [t])) (Val #(W64 0)))
    {{ (ch : Loc) (γ : ChanNames), RET #ch;
        isChan ch γ V ∗
        ⌜γ.chanCap = W64 0⌝ ∗
        ownChan γ V ChanState.Idle ∗ ⌜ch ≠ l⌝ }} := by
  wp_start as #Hl
  wp_auto
  simp only [channel.idle, channel.buffered]
  wp_auto
  wp_apply wp_slice_make2 (V := V) $$ [] as %sl ⟨Hsl, Hslcap⟩
  · ipureintro; decide
  iapply wp_fupd
  wp_alloc ch as Hch
  wp_auto
  ihave %Hnot_null := typedPointsto_not_null _ _ _ $$ Hch
  iStructNamed Hch
  by_cases hcl : ch = l
  · subst hcl
    iexfalso
    simp only [typedPointsto_unseal, typedPointstoWrap, typedPointstoDef_heap]
    icases cap with ⟨Hc1, -⟩
    icases Hl with ⟨Hc2, -⟩
    icombine Hc1 Hc2 gives %H
    exact absurd (DFrac.valid_own_op_discard.1 H.1) (by simp)
  imod ghostVar_alloc (ChanState.Idle (V := V)) with ⟨%state_gname, Hstate⟩
  icases ghostVar_halves _ _ $$ Hstate with ⟨Hstate_auth, Hstate_frag⟩
  imod ghostVar_alloc (none : Option (OfferLock V)) with ⟨%offer_lock_gname, Hoffer_lock⟩
  imod saved_prop_alloc iprop(True) (DFrac.own 1) DFrac.valid_own_one
    with ⟨%offer_parked_prop_gname, Hparked_prop⟩
  imod saved_pred_alloc (Function.uncurry (fun (_ : V) (_ : Bool) => (iprop(True) : IProp GF)))
    (DFrac.own 1) DFrac.valid_own_one with ⟨%offer_parked_pred_gname, Hparked_pred⟩
  imod saved_prop_alloc iprop(True) (DFrac.own 1) DFrac.valid_own_one
    with ⟨%offer_continuation_gname, Hcontinuation⟩
  ipersist cap
  ipersist mu
  imod init_lock (chanInvInner ch ⟨state_gname, offer_lock_gname, offer_parked_prop_gname,
    offer_parked_pred_gname, offer_continuation_gname, W64 0⟩ V) ⊤ «$v1_ptr» $$ «$v1»
    [-HΦ Hstate_frag Hl] with #Hlock
  · inext
    unfold chanInvInner
    iexists (ChanPhysState.Idle (V := V))
    simp only [chanPhys, chanLogical, show sint.nat (W64 0) = 0 from rfl, List.replicate,
      ownChan_unseal, ownChanDef, chanstate, savedOffer]
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
        simp only [ChanCapValid]
        decide
  imodintro
  ispecialize HΦ $$ %ch %(ChanNames.mk state_gname offer_lock_gname offer_parked_prop_gname
    offer_parked_pred_gname offer_continuation_gname (W64 0))
  iapply HΦ
  simp only [↓reduceIte, isChan_unseal, isChanDef, ownChan_unseal, ownChanDef, chanstate]
  isplitl []
  · iexists «$v1_ptr»
    iframe #
    ipureintro
    exact ⟨Hnot_null, by decide⟩
  isplitl []
  · ipureintro; trivial
  isplitl [Hstate_frag]
  · iframe
    ipureintro
    simp only [ChanCapValid]
    decide
  · ipureintro; exact hcl


end new_spec

end Perennial
