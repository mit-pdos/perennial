/-
Port of `new/golang/theory/chan/idioms/dsp/dsp_proofmode.v`: normalization of protocols
(`ProtoNormalize`) and the symbolic execution lemmas for DSP receive/send.

Lean notes / deviations:
* `ProtoNormalize d p pas q` has `q` as an `outParam`: Lean's type class resolution does not
  backtrack on the output, so instead of Rocq's cost-based search with backtracking the
  instances are prioritized to compute a canonical normal form (messages, `END`, duals and
  appends are decomposed first; an opaque protocol is left in place).
* Rocq's `tac_wp_recv`/`tac_wp_send` operate on proof-mode environments, and the
  `wp_recv`/`wp_send` tactics are Ltac. Here they are stated as Texan triples
  (`tac_wp_recv`, `tac_wp_send`) to be used with `wp_apply`; the received payload is
  returned as `tP x` (Rocq additionally strips one later from it with `MaybeIntoLaterN`).
  The `solve_proto_contractive` tactic is not ported.
-/
import Perennial.Golang.Theory.Chan.Idioms.Dsp.Dsp

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE ProofMode

/-! ## Normalization of protocols -/

class ActionDualIf (d : Bool) (a1 : action) (a2 : outParam action) : Prop where
  dual_action_if : a2 = if d then action_dual a1 else a1

instance action_dual_if_false (a : action) : ActionDualIf false a a := ⟨rfl⟩
instance action_dual_if_true_send : ActionDualIf true Send Recv := ⟨rfl⟩
instance action_dual_if_true_recv : ActionDualIf true Recv Send := ⟨rfl⟩

section classes
variable {GF : BundledGFunctors} {V : Type}

/-- The appended remainder `foldr (iProto_app ∘ uncurry iProto_dual_if) END pas`. -/
def proto_pas (pas : List (Bool × iProto GF V)) : iProto GF V :=
  pas.foldr (fun pa acc => iProto_app (iProto_dual_if pa.1 pa.2) acc) END

class ProtoNormalize (d : Bool) (p : iProto GF V) (pas : List (Bool × iProto GF V))
    (q : outParam (iProto GF V)) : Prop where
  proto_normalize : ⊢ iProto_le (iProto_app (iProto_dual_if d p) (proto_pas pas)) q

class MsgNormalize (d : Bool) (m1 : iMsg GF V) (pas : List (Bool × iProto GF V))
    (m2 : outParam (iMsg GF V)) : Prop where
  msg_normalize (a : action) :
    ProtoNormalize d (iProto_message a m1) pas
      (iProto_message (if d then action_dual a else a) m2)

/-- The message of `iProto_dual_if d (<a> m) <++> proto_pas pas`. -/
def msg_pas (d : Bool) (pas : List (Bool × iProto GF V)) (m : iMsg GF V) : iMsg GF V :=
  iMsg_map (fun p => iProto_app p (proto_pas pas)) (if d then iMsg_dual m else m)

theorem dual_if_message_app (d : Bool) (a : action) (m : iMsg GF V)
    (pas : List (Bool × iProto GF V)) :
    iProto_app (iProto_dual_if d (iProto_message a m)) (proto_pas pas) =
      iProto_message (if d then action_dual a else a) (msg_pas d pas m) := by
  cases d <;> simp [iProto_dual_if, msg_pas, iProto_dual_message, iProto_app_message]

theorem msg_pas_base (d : Bool) (pas : List (Bool × iProto GF V)) (v : V) (P : IProp GF)
    (p : iProto GF V) :
    msg_pas d pas (iMsg_base v P p) =
      iMsg_base v P (iProto_app (iProto_dual_if d p) (proto_pas pas)) := by
  cases d <;> simp [msg_pas, iProto_dual_if, iMsg_dual_base, iMsg_app_base]

theorem msg_pas_exist {A : Type _} (d : Bool) (pas : List (Bool × iProto GF V))
    (m : A → iMsg GF V) :
    msg_pas d pas (iMsg_exist m) = iMsg_exist fun x => msg_pas d pas (m x) := by
  cases d <;> simp [msg_pas, iMsg_dual_exist, iMsg_app_exist]

theorem proto_unfold_eq (p1 p2 : iProto GF V) (Hp : p1 = p2) (d : Bool)
    (pas : List (Bool × iProto GF V)) (q : iProto GF V) [h : ProtoNormalize d p2 pas q] :
    ProtoNormalize d p1 pas q := Hp ▸ h

instance (priority := low) proto_normalize_done (p : iProto GF V) : ProtoNormalize false p [] p :=
  ⟨by simp only [iProto_dual_if, proto_pas, List.foldr, iProto_app_end_r, Bool.false_eq_true,
        ↓reduceIte]
      exact iProto_le_refl p⟩

instance (priority := low) proto_normalize_done_dual (p : iProto GF V) :
    ProtoNormalize true p [] (iProto_dual p) :=
  ⟨by simp only [iProto_dual_if, proto_pas, List.foldr, iProto_app_end_r, ↓reduceIte]
      exact iProto_le_refl _⟩

instance (priority := low + 1) proto_normalize_done_dual_end :
    ProtoNormalize (GF := GF) (V := V) true END [] END :=
  ⟨by simp only [iProto_dual_if, proto_pas, List.foldr, iProto_app_end_r, ↓reduceIte,
        iProto_dual_end]
      exact iProto_le_refl _⟩

instance proto_normalize_dual (p : iProto GF V) (pas : List (Bool × iProto GF V))
    (q : iProto GF V) [h : ProtoNormalize true p pas q] :
    ProtoNormalize false (iProto_dual p) pas q := by
  constructor
  have := h.proto_normalize
  simpa [iProto_dual_if] using this

/-- (Rocq has a single instance with `negb d`; Lean's instance resolution does not reduce
`!d`, so there is one instance per value of `d`.) -/
instance proto_normalize_dual_dual (p : iProto GF V) (pas : List (Bool × iProto GF V))
    (q : iProto GF V) [h : ProtoNormalize false p pas q] :
    ProtoNormalize true (iProto_dual p) pas q := by
  constructor
  have := h.proto_normalize
  simpa [iProto_dual_if, iProto_dual_involutive] using this

instance proto_normalize_app_l (d : Bool) (p1 p2 : iProto GF V) (pas : List (Bool × iProto GF V))
    (q : iProto GF V) [h : ProtoNormalize d p1 ((d, p2) :: pas) q] :
    ProtoNormalize d (iProto_app p1 p2) pas q := by
  constructor
  have := h.proto_normalize
  simp only [proto_pas, List.foldr] at this
  cases d <;> simpa [iProto_dual_if, iProto_dual_app, ← iProto_app_assoc, proto_pas] using this

instance proto_normalize_end (d d' : Bool) (p : iProto GF V) (pas : List (Bool × iProto GF V))
    (q : iProto GF V) [h : ProtoNormalize d p pas q] :
    ProtoNormalize d' END ((d, p) :: pas) q := by
  constructor
  have := h.proto_normalize
  cases d' <;> simpa [iProto_dual_if, proto_pas] using this

instance (priority := low + 2) proto_normalize_app_r (d : Bool) (p1 p2 : iProto GF V)
    (pas : List (Bool × iProto GF V)) (q : iProto GF V) [h : ProtoNormalize d p2 pas q] :
    ProtoNormalize false p1 ((d, p2) :: pas) (iProto_app p1 q) := by
  constructor
  show ⊢ iProto_le (iProto_app p1 (iProto_app (iProto_dual_if d p2) (proto_pas pas)))
    (iProto_app p1 q)
  istart
  iapply iProto_le_app $$ [] []
  · iapply iProto_le_refl
  · iapply h.proto_normalize

instance (priority := low + 2) proto_normalize_app_r_dual (d : Bool) (p1 p2 : iProto GF V)
    (pas : List (Bool × iProto GF V)) (q : iProto GF V) [h : ProtoNormalize d p2 pas q] :
    ProtoNormalize true p1 ((d, p2) :: pas) (iProto_app (iProto_dual p1) q) := by
  constructor
  show ⊢ iProto_le (iProto_app (iProto_dual p1)
    (iProto_app (iProto_dual_if d p2) (proto_pas pas))) (iProto_app (iProto_dual p1) q)
  istart
  iapply iProto_le_app $$ [] []
  · iapply iProto_le_refl
  · iapply h.proto_normalize

instance msg_normalize_base (d : Bool) (v : V) (P : IProp GF) (p q : iProto GF V)
    (pas : List (Bool × iProto GF V)) [h : ProtoNormalize d p pas q] :
    MsgNormalize d (iMsg_base v P p) pas (iMsg_base v P q) where
  msg_normalize a := by
    constructor
    rw [dual_if_message_app, msg_pas_base]
    exact h.proto_normalize.trans (later_intro.trans (iProto_le_base _ v P _ _))

instance msg_normalize_exist {A : Type _} (d : Bool) (m1 m2 : A → iMsg GF V)
    (pas : List (Bool × iProto GF V)) [h : ∀ x, MsgNormalize d (m1 x) pas (m2 x)] :
    MsgNormalize d (iMsg_exist m1) pas (iMsg_exist m2) where
  msg_normalize a := by
    constructor
    rw [dual_if_message_app, msg_pas_exist]
    have H : ∀ x, ⊢ iProto_le (iProto_message (if d then action_dual a else a) (msg_pas d pas (m1 x)))
        (iProto_message (if d then action_dual a else a) (m2 x)) := fun x => by
      have := ((h x).msg_normalize a).proto_normalize
      rwa [dual_if_message_app] at this
    generalize (if d then action_dual a else a) = a' at H ⊢
    cases a'
    · -- Send
      istart
      iapply iProto_le_exist_elim_r
      iintro %x
      iapply iProto_le_trans $$ [] []
      · iapply iProto_le_exist_intro_l _ x
      · iapply H x
    · -- Recv
      istart
      iapply iProto_le_exist_elim_l
      iintro %x
      iapply iProto_le_trans $$ [] []
      · iapply H x
      · iapply iProto_le_exist_intro_r _ x

instance proto_normalize_message (d : Bool) (a1 a2 : action) (m1 m2 : iMsg GF V)
    (pas : List (Bool × iProto GF V)) [ha : ActionDualIf d a1 a2] [hm : MsgNormalize d m1 pas m2] :
    ProtoNormalize d (iProto_message a1 m1) pas (iProto_message a2 m2) := by
  rw [ha.dual_action_if]
  exact hm.msg_normalize a1

end classes

section lang
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : heapGS HasLC.hasLC GF] [allG GF]
variable [sem : go.Semantics]
variable {V : Type} [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V] {t : go.type}
  [IntoValTyped (GF := GF) V t]

omit [IntoValTyped (GF := GF) V t] in
theorem proto_normalize_le (p1 p2 : iProto GF V) [h : ProtoNormalize false p1 [] p2] :
    ⊢ iProto_le p1 p2 := by
  have := h.proto_normalize
  simpa [iProto_dual_if, proto_pas] using this

set_option synthInstance.checkSynthOrder false in
omit [IntoValTyped (GF := GF) V t] in
/-- Automatically perform normalization of protocols in the proof mode when using
`iexact`/`iassumption`. -/
instance pointsto_proto_from_assumption (q : Bool) (c : chan.t × chan.t) (p1 p2 : iProto GF V)
    (γ : dsp_names) [ProtoNormalize false p1 [] p2] :
    FromAssumption q .in (c ↣{γ} p1) (c ↣{γ} p2) where
  from_assumption := by
    refine intuitionisticallyIf_elim.trans ?_
    iintro H
    iapply iProto_pointsto_le $$ H
    inext
    iapply proto_normalize_le

omit [IntoValTyped (GF := GF) V t] in
/-- Automatically perform normalization of protocols in the proof mode when using `iframe`. -/
instance pointsto_proto_from_frame (q : Bool) (c : chan.t × chan.t) (p1 p2 : iProto GF V)
    (γ : dsp_names) [ProtoNormalize false p1 [] p2] :
    Frame q (c ↣{γ} p1) (c ↣{γ} p2) iprop(True) where
  frame := by
    refine (sep_mono intuitionisticallyIf_elim .rfl).trans ?_
    iintro ⟨H, -⟩
    iapply iProto_pointsto_le $$ H
    inext
    iapply proto_normalize_le

omit [IntoValTyped (GF := GF) V t] in
theorem iProto_le_recv_payload_later (v : V) (P : IProp GF) (p : iProto GF V) :
    ⊢ iProto_le (<?> iMsg_base v P p) (<?> iMsg_base v iprop(▷ P) p) := by
  iapply iProto_le_recv
  iintro %v' %p1' Hm
  simp only [iMsg_base_car]
  icases Hm with ⟨%Hv, Heq, HP⟩
  iexists p1'
  isplitr [Heq HP]
  · inext
    iapply iProto_le_refl
  isplitl []
  · ipureintro; exact Hv
  iframe

/-- Symbolic execution of a receive on a DSP endpoint (Rocq `tac_wp_recv`, here as a
Texan triple for `wp_apply`). -/
theorem tac_wp_recv {TT : Tele} (γ : dsp_names) (lr_chan rl_chan : loc) (p : iProto GF V)
    (m : iMsg GF V) (tv : TT -t> V) (tP : TT -t> IProp GF) (tp : TT -t> iProto GF V)
    [ProtoNormalize false p [] (<?> m)] [hm : MsgTele m tv tP tp] :
    {{ (lr_chan, rl_chan) ↣{γ} p }}
      (App (Val (chan.receive t)) (Val #rl_chan))
    {{ (x : TT.Arg), RET (PairV #(Tele.app tv x) #true);
        ((lr_chan, rl_chan) ↣{γ} Tele.app tp x) ∗ Tele.app tP x }} := by
  iintro %Φ Hc HΦ
  ihave Hc := iProto_pointsto_le γ _ _
    (<?> iMsg_texist fun x => iMsg_base (Tele.app tv x) iprop(▷ Tele.app tP x) (Tele.app tp x))
    $$ Hc []
  · inext
    iapply iProto_le_trans $$ [] []
    · iapply proto_normalize_le
    rw [hm.msg_tele]
    iapply iProto_le_texist_elim_l
    iintro %x
    iapply iProto_le_trans $$ [] []
    · iapply iProto_le_recv_payload_later
    · iapply iProto_le_texist_intro_r
        (fun x => iMsg_base (Tele.app tv x) iprop(▷ Tele.app tP x) (Tele.app tp x)) x
  iapply wp_dsp_recv (t := t) γ lr_chan rl_chan (Tele.app tv) (Tele.app tP) (Tele.app tp) $$ Hc HΦ

/-- Symbolic execution of a send on a DSP endpoint (Rocq `tac_wp_send`, here as a Texan
triple for `wp_apply`). -/
theorem tac_wp_send {TT : Tele} (x : TT.Arg) (γ : dsp_names) (lr_chan rl_chan : loc)
    (p : iProto GF V) (m : iMsg GF V) (tv : TT -t> V) (tP : TT -t> IProp GF)
    (tp : TT -t> iProto GF V) [ProtoNormalize false p [] (<!> m)] [hm : MsgTele m tv tP tp] :
    {{ ((lr_chan, rl_chan) ↣{γ} p) ∗ Tele.app tP x }}
      (App (App (Val (chan.send t)) (Val #lr_chan)) (Val #(Tele.app tv x)))
    {{ RET #(); (lr_chan, rl_chan) ↣{γ} Tele.app tp x }} := by
  iintro %Φ ⟨Hc, HP⟩ HΦ
  ihave Hc := iProto_pointsto_le γ _ _
    (<!> iMsg_texist fun x => iMsg_base (Tele.app tv x) (Tele.app tP x) (Tele.app tp x))
    $$ Hc []
  · inext
    rw [← hm.msg_tele]
    iapply proto_normalize_le
  iapply wp_dsp_send_tele (t := t) x lr_chan rl_chan γ (Tele.app tv) (Tele.app tP) (Tele.app tp)
    $$ [$Hc $HP] HΦ

omit [IntoValTyped (GF := GF) V t] in
/-- Normalization test: the dual of a send is a receive. -/
example (v : V) (P : IProp GF) (p : iProto GF V) :
    ⊢ iProto_le (iProto_dual (<!> iMsg_base v P p)) (<?> iMsg_base v P (iProto_dual p)) :=
  proto_normalize_le _ _

omit [IntoValTyped (GF := GF) V t] in
/-- Normalization test: appending distributes into messages. -/
example (v : V) (P : IProp GF) (p q : iProto GF V) :
    ⊢ iProto_le (iProto_app (<!> iMsg_base v P p) q) (<!> iMsg_base v P (iProto_app p q)) :=
  proto_normalize_le _ _

/-- `tac_wp_recv` test: receiving on the dual of a send protocol. -/
example (γ : dsp_names) (lr_chan rl_chan : loc) (v : V) (P : IProp GF) (p : iProto GF V) :
    {{ (lr_chan, rl_chan) ↣{γ} iProto_dual (<!> iMsg_base v P p) }}
      (App (Val (chan.receive t)) (Val #rl_chan))
    {{ RET (PairV #v #true); ((lr_chan, rl_chan) ↣{γ} iProto_dual p) ∗ P }} := by
  iintro %Φ Hc HΦ
  -- (`MsgTele`'s outputs are not `outParam`s, so they are given explicitly)
  wp_apply tac_wp_recv (TT := Tele.nil.{0}) γ lr_chan rl_chan _ _ (ULift.up v) (ULift.up P)
    (ULift.up (iProto_dual p)) $$ Hc as %x ⟨Hc, HP⟩
  cases x
  simp only [Tele.app]
  iapply HΦ
  iframe

end lang

end Perennial
