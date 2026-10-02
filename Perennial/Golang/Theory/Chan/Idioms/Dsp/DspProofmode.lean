/-
Port of `new/golang/theory/chan/idioms/dsp/dsp_proofmode.v`: normalization of protocols
(`ProtoNormalize`) and the symbolic execution lemmas for DSP receive/send.

Lean notes / deviations:
* `ProtoNormalize d p pas q` has `q` as an `outParam`: Lean's type class resolution does not
  backtrack on the output, so instead of Rocq's cost-based search with backtracking the
  instances are prioritized to compute a canonical normal form (messages, `END`, duals and
  appends are decomposed first; an opaque protocol is left in place).
* Rocq's `tac_wp_recv`/`tac_wp_send` operate on proof-mode environments. Here they are
  stated as (curried) Texan triples, usable with `wp_apply` (the telescope is found by the
  `MsgTele` instances, whose outputs are `outParam`s); the received payload is returned as
  `tP x` (Rocq strips one later from it with `MaybeIntoLaterN`; here the later is removed by
  `iProto_le_recv_payload_later`).
* The tactics `wp_recv (x₁ … xₙ) as pat` and `wp_send (t₁ … tₙ) with spat` are Lean
  elaborators that find the endpoint hypothesis (keeping its name, as in Rocq) and apply
  `tac_wp_recv`/`tac_wp_send` with `wp_apply_raw`. `pat` is a single iris-lean cases pattern
  for the payload, the binders are `rcases` patterns (Rocq's `wp_recv (xs) as (ys) "pat"` is
  covered by `%` patterns in `pat`), and `spat` is a single specialization pattern (`[$H]`,
  `[//]`, ...). Both default (`wp_recv`, `wp_send`) to an anonymous payload / `[]`.
* Rocq's `ProtoUnfold` notation (a `ProtoNormalize` rule, used with backtracking) is a
  separate class here; it is only used to unfold the head of a protocol, through
  `ProtoNormalizeMsg` (see the section on unfolding).
* `solve_proto_contractive` is a `repeat'` of `solve_proto_contractive_step`, which applies
  the non-expansiveness/contractiveness lemmas of the protocol constructors (Rocq uses
  `solve_proper_core` with `f_contractive`/`f_equiv`/`f_dist_le`).
-/
import Perennial.Golang.Theory.Chan.Idioms.Dsp.Dsp

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE ProofMode

/-! ## Proving contractiveness of protocols -/

/-- One step of `solve_proto_contractive`: close a goal `a ≡{n}≡ a`, close `x ≡{m}≡ y` from
the hypothesis `h : DistLater n x y` (when `m < n` follows by `omega`; Rocq `f_dist_le`), go
under a `DistLater` (Rocq `f_contractive`), or decompose a protocol/message constructor on
both sides (Rocq `f_equiv`). -/
syntax "solve_proto_contractive_step " ident : tactic
macro_rules
  | `(tactic| solve_proto_contractive_step $h) => `(tactic| first
    | exact OFE.Dist.rfl
    | exact OFE.DistLater.rfl
    | exact $h _ (by omega)
    | refine (iProto_message_ne _).ne ?_
    | refine iMsg_exist_ne fun _ => ?_
    | refine iMsg_contractive _ ?_ ?_
    | refine iProto_app_ne.ne ?_ ?_
    | refine iProto_dual_ne.ne ?_
    | (show OFE.DistLater _ _ _; intro _ _))

/-- `solve_proto_contractive` (Rocq `solve_proto_contractive`) proves `Contractive f` for a
protocol body `f : iProto GF V → iProto GF V` built from messages (`<a> m`, `iMsg_exist`,
`iMsg_base`), `iProto_app` and `iProto_dual`, in which the recursive argument occurs only
guarded by a message. -/
macro "solve_proto_contractive" : tactic => `(tactic| (
  constructor
  intro n x y h
  repeat' solve_proto_contractive_step h
  done))

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

/-! ### Unfolding recursive protocols

Rocq registers the unfolding of a recursive protocol as a `ProtoUnfold p1 p2` instance (a
`ProtoNormalize` rule), relying on backtracking to only unfold when the head of the protocol
is needed. Here `ProtoUnfold p1 p2` is a separate class (with `p2` an `outParam`), and
unfolding is only done at the head of the protocol, when `wp_recv`/`wp_send` need a message:
`ProtoNormalizeMsg p a m` first normalizes `p`, and only if that is not a message `<a> m`,
unfolds the head of `p` (`ProtoUnfoldHead`, through `iProto_dual` and the left of
`iProto_app`) and tries again. -/

/-- Rocq `ProtoUnfold p1 p2`: the (recursive) protocol `p1` unfolds to `p2`. Instances are
typically proved with `fixpoint_unfold`. -/
class ProtoUnfold (p1 : iProto GF V) (p2 : outParam (iProto GF V)) : Prop where
  proto_unfold : p1 = p2

/-- One `ProtoUnfold` step at the head of a protocol. -/
class ProtoUnfoldHead (p1 : iProto GF V) (p2 : outParam (iProto GF V)) : Prop where
  proto_unfold_head : p1 = p2

instance proto_unfold_head_base (p1 p2 : iProto GF V) [h : ProtoUnfold p1 p2] :
    ProtoUnfoldHead p1 p2 := ⟨h.proto_unfold⟩

instance proto_unfold_head_dual (p1 p2 : iProto GF V) [h : ProtoUnfoldHead p1 p2] :
    ProtoUnfoldHead (iProto_dual p1) (iProto_dual p2) := ⟨by rw [h.proto_unfold_head]⟩

instance proto_unfold_head_app (p1 p2 q : iProto GF V) [h : ProtoUnfoldHead p1 p2] :
    ProtoUnfoldHead (iProto_app p1 q) (iProto_app p2 q) := ⟨by rw [h.proto_unfold_head]⟩

/-- `p` normalizes (`ProtoNormalize`, after unfolding the head with `ProtoUnfold` if needed) to
the message `<a> m`. Used by `tac_wp_recv`/`tac_wp_send`. -/
class ProtoNormalizeMsg (p : iProto GF V) (a : action) (m : outParam (iMsg GF V)) : Prop where
  proto_normalize_msg : ⊢ iProto_le p (iProto_message a m)

instance (priority := high) proto_normalize_msg_normalize (p : iProto GF V) (a : action)
    (m : iMsg GF V) [h : ProtoNormalize false p [] (iProto_message a m)] :
    ProtoNormalizeMsg p a m :=
  ⟨by simpa [iProto_dual_if, proto_pas] using h.proto_normalize⟩

instance proto_normalize_msg_unfold (p p' : iProto GF V) (a : action) (m : iMsg GF V)
    [h : ProtoUnfoldHead p p'] [h' : ProtoNormalizeMsg p' a m] : ProtoNormalizeMsg p a m :=
  ⟨h.proto_unfold_head ▸ h'.proto_normalize_msg⟩

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
    [hn : ProtoNormalizeMsg p Recv m] [hm : MsgTele m tv tP tp] :
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
    · iapply hn.proto_normalize_msg
    rw [hm.msg_tele]
    iapply iProto_le_texist_elim_l
    iintro %x
    iapply iProto_le_trans $$ [] []
    · iapply iProto_le_recv_payload_later
    · iapply iProto_le_texist_intro_r
        (fun x => iMsg_base (Tele.app tv x) iprop(▷ Tele.app tP x) (Tele.app tp x)) x
  iapply wp_dsp_recv (t := t) γ lr_chan rl_chan (Tele.app tv) (Tele.app tP) (Tele.app tp) $$ Hc HΦ

/-- Symbolic execution of a send on a DSP endpoint (Rocq `tac_wp_send`, here as a curried
Texan triple for `wp_apply`: endpoint, then payload). -/
theorem tac_wp_send {TT : Tele} (x : TT.Arg) (γ : dsp_names) (lr_chan rl_chan : loc)
    (p : iProto GF V) (m : iMsg GF V) (tv : TT -t> V) (tP : TT -t> IProp GF)
    (tp : TT -t> iProto GF V) [hn : ProtoNormalizeMsg p Send m] [hm : MsgTele m tv tP tp] :
    ⊢ ∀ Φ : val → IProp GF, ((lr_chan, rl_chan) ↣{γ} p) -∗ Tele.app tP x -∗
      ▷ (((lr_chan, rl_chan) ↣{γ} Tele.app tp x) -∗ Φ #()) -∗
      WP (App (App (Val (chan.send t)) (Val #lr_chan)) (Val #(Tele.app tv x))) {{ Φ }} := by
  iintro %Φ Hc HP HΦ
  ihave Hc := iProto_pointsto_le γ _ _
    (<!> iMsg_texist fun x => iMsg_base (Tele.app tv x) (Tele.app tP x) (Tele.app tp x))
    $$ Hc []
  · inext
    rw [← hm.msg_tele]
    iapply hn.proto_normalize_msg
  iapply wp_dsp_send_tele (t := t) x lr_chan rl_chan γ (Tele.app tv) (Tele.app tP) (Tele.app tp)
    $$ [$Hc $HP] HΦ


end lang

/-! ## Symbolic execution tactics -/

section tactics
open Lean Elab Tactic Meta Iris.ProofMode

/-- The spatial DSP endpoint hypotheses `c ↣{γ} p` of the current Iris goal, as
`(name, γ, c, p)`. -/
def dspEndpointHyps : TacticM (Array (Name × Expr × Expr × Expr)) := do
  let some g := parseIrisGoal? (← instantiateMVars (← getMainTarget))
    | throwError "not in the Iris proof mode"
  let mut out := #[]
  for ivar in g.hyps.spatialIVarIds .topToBottom do
    if let some (name, _, _, ty) := g.hyps.getDecl? ivar then
      let ty := (← instantiateMVars ty).consumeMData
      if ty.isAppOf ``dsp_endpoint then
        let args := ty.getAppArgs
        let popt := args[args.size - 1]!.consumeMData
        if popt.isAppOfArity ``Option.some 2 then
          out := out.push (name, args[args.size - 3]!, args[args.size - 2]!, popt.appArg!)
  return out

/-- The element types `t` of the `chan.receive t`/`chan.send t` (`fn`) in the WP of the
current goal. -/
def dspChanElemTypes (fn : Name) : TacticM (Array Expr) := do
  let some g := parseIrisGoal? (← instantiateMVars (← getMainTarget))
    | throwError "not in the Iris proof mode"
  let some wp ← parseGooseWp? g.goal | throwError "the goal {g.goal} is not a GooseLang WP"
  let r ← IO.mkRef (#[] : Array Expr)
  wp.e.forEachWhere (·.isAppOfArity fn 3) fun s => r.modify fun ts =>
    if ts.contains s.appArg! then ts else ts.push s.appArg!
  r.get

/-- The two components of a channel pair `c`. -/
def dspChanPair (c : Expr) : MetaM (Expr × Expr) := do
  if c.isAppOfArity ``Prod.mk 4 then return (c.getArg! 2, c.getArg! 3)
  return (← mkAppM ``Prod.fst #[c], ← mkAppM ``Prod.snd #[c])

/-- Unfold `Tele.app` (on literal telescopes and arguments), `tele_fun_nil` and `tele_fun_cons`
in `e`. -/
def dspTeleAppDsimp (e : Expr) : MetaM Expr := do
  let mut thms : SimpTheorems := {}
  for d in [``Iris.Std.Tele.app, ``tele_fun_nil, ``tele_fun_cons] do
    thms ← thms.addDeclToUnfold d
  let ctx ← Simp.mkContext (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
  return (← dsimp e ctx).1

/-- Build a telescope argument of `TT` from the terms `ts` (missing ones are fresh
metavariables, to be found by unification). -/
partial def dspMkTeleArg (TT : Expr) (ts : List Term) : TermElabM Expr := do
  let TT ← whnf TT
  if TT.isAppOfArity ``Iris.Std.Tele.cons 2 then
    let X := TT.getArg! 0
    let b := TT.getArg! 1
    let (a, ts') ← match ts with
      | t :: ts' => pure (← Term.elabTermEnsuringType t X, ts')
      | [] => pure (← mkFreshExprMVar X, [])
    let rest ← dspMkTeleArg (b.beta #[a]) ts'
    mkAppOptM ``Iris.Std.Tele.Arg.cons #[some X, some b, some a, some rest]
  else if TT.isConstOf ``Iris.Std.Tele.nil then
    unless ts.isEmpty do throwError "too many witnesses given"
    let teleTy ← whnf (← inferType TT)
    unless teleTy.isConstOf ``Iris.Std.Tele do throwError "unexpected telescope {TT}"
    return mkConst ``Iris.Std.Tele.Arg.nil teleTy.constLevels!
  else throwError "the telescope {TT} is not a literal telescope"

/-- Set the remaining universe metavariables of `e` (the universe of an empty telescope) to
`0`. -/
def dspDefaultLevelMVars (e : Expr) : MetaM Unit := do
  let s := CollectLevelMVars.main (← instantiateMVars e) {}
  for l in s.result do
    if ← isLevelMVarAssignable l then assignLevelMVar l Level.zero

/-- The number of binders of the literal telescope `TT`. -/
def dspTeleArity (TT : Expr) : MetaM Nat := do
  let some n := Iris.Std.Tele.literalArity? (← instantiateMVars TT)
    | throwError "the telescope {TT} is not a literal telescope"
  return n

/-- The (first) telescope argument `TT : Tele` of an application `e`. -/
def dspTeleOf (e : Expr) : MetaM Expr := do
  for a in e.getAppArgs do
    if (← whnfR (← inferType a)).isConstOf ``Iris.Std.Tele then return ← instantiateMVars a
  throwError "no telescope in {e}"

/-- Run `k` on each candidate (endpoint hypothesis, element type), returning the first
success. -/
def dspTryCandidates (tacName : String) (fn : Name) (what : String)
    (k : Name → Expr → Expr → Expr → Expr → Expr → TacticM Unit) : TacticM Unit := do
  let hyps ← withMainContext dspEndpointHyps
  let ts ← withMainContext (dspChanElemTypes fn)
  if ts.isEmpty then throwError "{tacName}: cannot find '{what}' in the goal"
  if hyps.isEmpty then throwError "{tacName}: cannot find a DSP endpoint `c ↣{"{"}γ} p`"
  let s ← saveState
  let mut errs : Array MessageData := #[]
  for (name, γ, c, p) in hyps do
    for t in ts do
      let (lr, rl) ← withMainContext (dspChanPair c)
      try
        withMainContext (k name γ lr rl p t)
        return
      catch e =>
        errs := errs.push m!"{name}: {e.toMessageData}"
        s.restore
  throwError "{tacName}: no DSP endpoint applies:{indentD (MessageData.joinSep errs.toList Format.line)}"

/-- `wp_recv (x₁ … xₙ) as pat` (Rocq `wp_recv (x1 .. xn) as "pat"`): symbolically execute a
`chan.receive` on a DSP endpoint `(lr, rl) ↣{γ} p` whose protocol normalizes
(`ProtoNormalize`) to a receive `<?> ∃ x₁ … xₙ, MSG v {{ P }}; p'`. The endpoint is found in
the Iris context and keeps its name (now with protocol `p'`), the binders are introduced as
`x₁ … xₙ` (`rcases` patterns, `_` by default), and the payload `P` is destructed with the
cases pattern `pat` (default `_`). Runs `wp_pures` first, but no automation afterwards. -/
syntax (name := wpRecv) "wp_recv" (" (" (colGt rcasesPat)* ")")? (" as " icasesPat)? : tactic

elab_rules : tactic
  | `(tactic| wp_recv $[($xs*)]? $[as $pat?]?) => do
    let xs := (xs.getD #[]).toList
    let pat ← match pat? with | some p => pure p | none => `(icasesPat| _)
    let pat ← `(Iris.ProofMode.icasesPatAlts| $pat:icasesPat)
    evalTactic (← `(tactic| try wp_pures))
    dspTryCandidates "wp_recv" ``chan.receive "chan.receive" fun name γ lr rl p t => do
      let e ← withNoSorry `wp_recv do
        let stx ← `(tac_wp_recv (t := $(← Term.exprToSyntax t)) $(← Term.exprToSyntax γ)
          $(← Term.exprToSyntax lr) $(← Term.exprToSyntax rl) $(← Term.exprToSyntax p) _ _ _ _)
        let e ← Term.elabTerm stx none
        Term.synthesizeSyntheticMVarsNoPostponing
        dspDefaultLevelMVars e
        instantiateMVars e
      let n ← dspTeleArity (← dspTeleOf e)
      if xs.length > n then
        throwError "wp_recv: {xs.length} binders given, but the message has {n}"
      let mut pats : Array (TSyntax ``Lean.Parser.Tactic.rcasesPatLo) := #[]
      for i in [:n] do
        let p ← match xs[i]? with | some p => pure p | none => `(rcasesPat| _)
        pats := pats.push (← `(Lean.Parser.Tactic.rcasesPatLo| $p:rcasesPat))
      pats := pats.push (← `(Lean.Parser.Tactic.rcasesPatLo| ⟨⟩))
      let H := mkIdent name
      let eS ← Term.exprToSyntax e
      evalTactic (← `(tactic| (
        focus ((wp_apply_raw $eS:term $$ $H:ident) <;> wp_apply_post)
        wp_focus_cont (
          iintro %x
          rcases x with ⟨$pats,*⟩
          try dsimp only [Iris.Std.Tele.app, tele_fun_nil, tele_fun_cons]
          iintro ⟨$H:ident, $pat⟩)
        wp_untag_cont)))

/-- `wp_send (t₁ … tₙ) with spat` (Rocq `wp_send (t1 .. tn) with "spat"`): symbolically
execute a `chan.send` on a DSP endpoint `(lr, rl) ↣{γ} p` whose protocol normalizes
(`ProtoNormalize`) to a send `<!> ∃ x₁ … xₙ, MSG v {{ P }}; p'`. The endpoint is found in the
Iris context and keeps its name. The witnesses `xᵢ` are `tᵢ` or, when omitted, found by
unifying `v` with the sent value. The payload `P` is proved with the specialization pattern
`spat` (default `[]`; e.g. `[$H]`, `[H //]`). Runs `wp_pures` first, but no automation
afterwards. -/
syntax (name := wpSend) "wp_send" (" (" (colGt term:max)* ")")? (" with " wpSpecPat)? : tactic

elab_rules : tactic
  | `(tactic| wp_send $[($ts*)]? $[with $sp?]?) => do
    let ts := (ts.getD #[]).toList
    let sp ← match sp? with
      | some s => liftMacroM <| wpSpecPatToSpecPat s
      | none => `(specPat| [])
    evalTactic (← `(tactic| try wp_pures))
    dspTryCandidates "wp_send" ``chan.send "chan.send" fun name γ lr rl p t => do
      let e ← withNoSorry `wp_send do
        let stx ← `(tac_wp_send (t := $(← Term.exprToSyntax t)) _ $(← Term.exprToSyntax γ)
          $(← Term.exprToSyntax lr) $(← Term.exprToSyntax rl) $(← Term.exprToSyntax p) _ _ _ _)
        let e ← Term.elabTerm stx none
        Term.synthesizeSyntheticMVarsNoPostponing
        dspDefaultLevelMVars e
        let e ← instantiateMVars e
        let TT ← dspTeleOf e
        -- the witness argument `x : TT.Arg`
        let some x ← e.getAppArgs.findM? fun a => do
            return a.isMVar && (← whnfR (← inferType a)).isAppOf ``Iris.Std.Tele.Arg
          | throwError "wp_send: cannot find the telescope argument"
        let xv ← dspMkTeleArg TT ts
        unless ← isDefEq x xv do throwError "wp_send: cannot instantiate the witnesses"
        let e ← instantiateMVars e
        let ty ← dspTeleAppDsimp (← instantiateMVars (← inferType e))
        mkExpectedTypeHint e ty
      let H := mkIdent name
      let eS ← Term.exprToSyntax e
      evalTactic (← `(tactic| (
        focus ((wp_apply_raw $eS:term $$ $H:ident $sp:specPat) <;> wp_apply_post)
        wp_focus_cont (iintro $H:ident)
        wp_untag_cont)))

end tactics

/-! ## Tests -/

section tests
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : heapGS HasLC.hasLC GF] [allG GF]
variable [sem : go.Semantics]
variable {V : Type} [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V] {t : go.type}
  [IntoValTyped (GF := GF) V t]

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
  wp_recv as HP
  iapply HΦ
  iframe

/-- `tac_wp_recv` with `wp_apply`: the telescope is found by `MsgTele`. -/
example (γ : dsp_names) (lr_chan rl_chan : loc) (v : Nat → V) (P : Nat → IProp GF)
    (p : Nat → iProto GF V) :
    {{ (lr_chan, rl_chan) ↣{γ} (<?> iMsg_exist fun n => iMsg_base (v n) (P n) (p n)) }}
      (App (Val (chan.receive t)) (Val #rl_chan))
    {{ (n : Nat), RET (PairV #(v n) #true); ((lr_chan, rl_chan) ↣{γ} p n) ∗ P n }} := by
  iintro %Φ Hc HΦ
  wp_apply tac_wp_recv $$ Hc as %x ⟨Hc, HP⟩
  obtain ⟨n, ⟨⟩⟩ := x
  simp only [Tele.app]
  iapply HΦ $$ %n
  iframe

/-- `wp_send` with an explicit witness, and `wp_recv` with a binder. -/
example (γ : dsp_names) (lr_chan rl_chan : loc) (v : Nat → V) (P : Nat → IProp GF)
    (p : Nat → iProto GF V) :
    ⊢ ∀ Φ : val → IProp GF, ((lr_chan, rl_chan) ↣{γ} (<!> iMsg_exist fun n => iMsg_base (v n) (P n) (p n))) -∗
      P 3 -∗ ▷ (((lr_chan, rl_chan) ↣{γ} p 3) -∗ Φ #()) -∗
      WP (App (App (Val (chan.send t)) (Val #lr_chan)) (Val #(v 3))) {{ Φ }} := by
  iintro %Φ Hc HP HΦ
  wp_send (3) with [$HP]
  iapply HΦ $$ Hc

omit [IntoValTyped (GF := GF) V t] in
/-- `solve_proto_contractive` on a recursive protocol body. -/
example (v : V) (P : IProp GF) (q : iProto GF V) :
    Contractive fun r : iProto GF V =>
      iProto_app (<!> iMsg_exist fun _ : Nat => iMsg_base v P (iProto_dual (<?> iMsg_base v P r))) q := by
  solve_proto_contractive

end tests

end Perennial
