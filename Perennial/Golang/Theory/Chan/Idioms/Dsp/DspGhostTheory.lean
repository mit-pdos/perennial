import Perennial.Golang.Theory.Chan.Idioms.Dsp.ProtoModel
import Perennial.Ghost.Own

/-!
Port of `new/golang/theory/chan/idioms/dsp/dsp_ghost_theory.v` (from Actris): dependent
separation protocols `iProto GF V`, messages `iMsg GF V`, dual, append, the subprotocol
relation `⊑` (`iProto_le`), and the protocol ghost theory (`iProto_ctx`, `iProto_own`).

Lean notes / deviations:
* iris-lean's OFE equivalence is `=`, so `iProto_case` gives an equality and Rocq `≡`
  lemmas on protocols are stated with `=`.
* Ghost state. Rocq's `protoG Σ V := inG Σ (excl_authR (laterO (iProto Σ V)))` cannot be
  expressed with the `allG` codes for an arbitrary `V` (codes cannot mention types). We use
  the `allG` code `protoO pos` (see `Perennial/Ghost/All.lean`) and require
  `[Pos.Countable V]`: the ghost state stores `Next (iProto_enc p) : Later (iProto GF Pos)`
  where `iProto_enc : iProto GF V -n> iProto GF Pos` re-indexes messages along
  `encode`/`decode`; it has a non-expansive retraction `iProto_dec`, so agreement of the
  encodings gives agreement of the protocols. `protoG` is therefore just `allG`.
* Notation: `END`, `<!> m`, `<?> m`, `p ⊑ q`, `p <++> q` (scoped in `Perennial`); the
  `MSG v {{ P }}; p` and `<a @ x> m` notations are not provided (use `iMsg_base` and
  `iMsg_exist`).
-/

set_option autoImplicit false

noncomputable section

namespace Perennial
open Iris OFE COFE BI

/-! ## Types -/

abbrev iProto (GF : BundledGFunctors) (V : Type) : Type := proto V (IProp GF) (IProp GF)

/-! ## Messages -/

structure iMsg (GF : BundledGFunctors) (V : Type) where
  IMsg ::
  car : V → (Later (iProto GF V) -n> IProp GF)

export iMsg (IMsg)

section imsg_ofe
variable {GF : BundledGFunctors} {V : Type}

instance iMsg_inhabited : Inhabited (iMsg GF V) := ⟨⟨fun _ => Hom.const iprop(False)⟩⟩

instance iMsgO : OFE (iMsg GF V) where
  Dist n m1 m2 := ∀ w, m1.car w ≡{n}≡ m2.car w
  dist_eqv := ⟨fun _ _ => .rfl, fun h w => (h w).symm, fun h1 h2 w => (h1 w).trans (h2 w)⟩
  eq_dist' {m1 m2} := by
    obtain ⟨m1⟩ := m1; obtain ⟨m2⟩ := m2
    simp only [iMsg.IMsg.injEq]
    exact (OFE.eq_dist (α := V → (Later (iProto GF V) -n> IProp GF)))
  dist_lt h hlt w := (h w).lt hlt

instance iMsg_cofe : IsCOFE (iMsg GF V) :=
  isoCofe (α := V → (Later (iProto GF V) -n> IProp GF)) iMsg.IMsg
    ⟨iMsg.car, ⟨fun {_ _ _} h => h⟩⟩ (fun _ _ _ => Iff.rfl) (fun _ => rfl)

theorem iMsg_dist_iff {n} {m1 m2 : iMsg GF V} :
    m1 ≡{n}≡ m2 ↔ ∀ w p, m1.car w p ≡{n}≡ m2.car w p := Iff.rfl

end imsg_ofe

section ops
variable {GF : BundledGFunctors} {V : Type}

def iMsg_base_def (v : V) (P : IProp GF) (p : iProto GF V) : iMsg GF V :=
  ⟨fun v' => ⟨fun p' => iprop(⌜v = v'⌝ ∗ Later.next p ≡ p' ∗ P),
    ⟨fun {_ _ _} h => sep_ne.ne .rfl (sep_ne.ne ((internalEq.ne_r _).ne h) .rfl)⟩⟩⟩
@[irreducible] def iMsg_base (v : V) (P : IProp GF) (p : iProto GF V) : iMsg GF V :=
  iMsg_base_def v P p
theorem iMsg_base_unseal : @iMsg_base = @iMsg_base_def := by
  funext; with_unfolding_all rfl

def iMsg_exist_def {A : Type _} (m : A → iMsg GF V) : iMsg GF V :=
  ⟨fun v' => ⟨fun p' => iprop(∃ x, (m x).car v' p'),
    ⟨fun {_ _ _} h => exists_ne fun x => ((m x).car v').ne.ne h⟩⟩⟩
@[irreducible] def iMsg_exist {A : Type _} (m : A → iMsg GF V) : iMsg GF V := iMsg_exist_def m
theorem iMsg_exist_unseal : @iMsg_exist = @iMsg_exist_def := by
  funext; with_unfolding_all rfl

/-- Rocq `iMsg_texist`: telescopic existential quantification over messages. -/
def iMsg_texist {TT : Iris.Std.Tele} (m : TT.Arg → iMsg GF V) : iMsg GF V :=
  Iris.Std.Tele.fold (fun _ => iMsg_exist) (Iris.Std.Tele.bind m)

def iProto_end_def : iProto GF V := proto_end
@[irreducible] def iProto_end : iProto GF V := iProto_end_def
theorem iProto_end_unseal : @iProto_end = @iProto_end_def := by
  funext; with_unfolding_all rfl

def iProto_message_def (a : action) (m : iMsg GF V) : iProto GF V := proto_message a m.car
@[irreducible] def iProto_message (a : action) (m : iMsg GF V) : iProto GF V :=
  iProto_message_def a m
theorem iProto_message_unseal : @iProto_message = @iProto_message_def := by
  funext; with_unfolding_all rfl

end ops

scoped notation "END" => iProto_end
scoped notation:200 "<!> " m:200 => iProto_message Send m
scoped notation:200 "<?> " m:200 => iProto_message Recv m

section ops2
variable {GF : BundledGFunctors} {V : Type}

/-! ## Operations -/

def iMsg_map (r : iProto GF V → iProto GF V) (m : iMsg GF V) : iMsg GF V :=
  ⟨fun v => ⟨fun p1' => iprop(∃ p1, m.car v (Later.next p1) ∗ p1' ≡ Later.next (r p1)),
    ⟨fun {_ _ _} h => exists_ne fun _ => sep_ne.ne .rfl ((internalEq.ne_l _).ne h)⟩⟩⟩

theorem iMsg_map_ne_r {n} (r1 r2 : iProto GF V → iProto GF V) (m : iMsg GF V)
    (h : ∀ p, DistLater n (r1 p) (r2 p)) : iMsg_map r1 m ≡{n}≡ iMsg_map r2 m :=
  fun v p' => exists_ne fun p1 => sep_ne.ne .rfl
    ((internalEq.ne_r _).ne (NextContractive.distLater_dist (h p1)))

theorem iMsg_map_ne_m {n} (r : iProto GF V → iProto GF V) (m1 m2 : iMsg GF V)
    (h : m1 ≡{n}≡ m2) : iMsg_map r m1 ≡{n}≡ iMsg_map r m2 :=
  fun v p' => exists_ne fun p1 => sep_ne.ne (h v _) .rfl

def iProto_map_app_aux (f : action → action) (p2 : iProto GF V)
    (r : iProto GF V -n> iProto GF V) : iProto GF V -n> iProto GF V where
  f p := proto_elim p2 (fun a m => proto_message (f a) (iMsg_map r ⟨m⟩).car) p
  ne := ⟨fun {_ p1 p1'} h => proto_elim_ne _ _ _ p1 p1'
    (fun a _ _ hm => proto_message_ne _ fun v => iMsg_map_ne_m r ⟨_⟩ ⟨_⟩ hm v) h⟩

instance iProto_map_app_aux_contractive (f : action → action) (p2 : iProto GF V) :
    Contractive (iProto_map_app_aux f p2) where
  distLater_dist {_ r1 r2} h p := proto_elim_ne p2
    (fun a m => proto_message (f a) (iMsg_map r1 ⟨m⟩).car)
    (fun a m => proto_message (f a) (iMsg_map r2 ⟨m⟩).car) p p
    (fun a m1 m2 hm => proto_message_ne _ fun v =>
      ((iMsg_map_ne_m r1 ⟨m1⟩ ⟨m2⟩ hm).trans (iMsg_map_ne_r r1 r2 _ fun q k hk => h k hk q)) v) .rfl

def iProto_map_app (f : action → action) (p2 : iProto GF V) : iProto GF V -n> iProto GF V :=
  fixpoint (iProto_map_app_aux f p2)

theorem iProto_map_app_unfold (f : action → action) (p2 : iProto GF V) (p : iProto GF V) :
    iProto_map_app f p2 p = iProto_map_app_aux f p2 (iProto_map_app f p2) p :=
  congrArg (fun g => Hom.f g p) (fixpoint_unfold (iProto_map_app_aux f p2).toContractiveHom)

def iProto_app_def (p1 p2 : iProto GF V) : iProto GF V := iProto_map_app id p2 p1
@[irreducible] def iProto_app (p1 p2 : iProto GF V) : iProto GF V := iProto_app_def p1 p2
theorem iProto_app_unseal : @iProto_app = @iProto_app_def := by
  funext; with_unfolding_all rfl

def iProto_dual_def (p : iProto GF V) : iProto GF V := iProto_map_app action_dual proto_end p
@[irreducible] def iProto_dual (p : iProto GF V) : iProto GF V := iProto_dual_def p
theorem iProto_dual_unseal : @iProto_dual = @iProto_dual_def := by
  funext; with_unfolding_all rfl

/-- Rocq `iMsg_dual`. -/
abbrev iMsg_dual (m : iMsg GF V) : iMsg GF V := iMsg_map iProto_dual m

def iProto_dual_if (d : Bool) (p : iProto GF V) : iProto GF V :=
  if d then iProto_dual p else p

end ops2

scoped infixl:60 " <++> " => iProto_app

/-! ## Protocol entailment -/

section le
variable {GF : BundledGFunctors} {V : Type}

/-- The body of the `Recv`/`Send` cases of `iProto_le_pre`. -/
def iProto_le_body (r : iProto GF V → iProto GF V → IProp GF) (a1 a2 : action)
    (m1 m2 : iMsg GF V) : IProp GF :=
  match a1, a2 with
  | Recv, Recv => iprop(∀ v p1', m1.car v (Later.next p1') -∗
      ∃ p2', ▷ r p1' p2' ∗ m2.car v (Later.next p2'))
  | Send, Send => iprop(∀ v p2', m2.car v (Later.next p2') -∗
      ∃ p1', ▷ r p1' p2' ∗ m1.car v (Later.next p1'))
  | _, _ => iprop(False)

def iProto_le_pre (r : iProto GF V → iProto GF V → IProp GF) (p1 p2 : iProto GF V) : IProp GF :=
  iprop((p1 ≡ END ∗ p2 ≡ END) ∨
    ∃ a1 a2 m1 m2, (p1 ≡ iProto_message a1 m1) ∗ (p2 ≡ iProto_message a2 m2) ∗
      iProto_le_body r a1 a2 m1 m2)

theorem iProto_le_body_ne {n} (r1 r2 : iProto GF V → iProto GF V → IProp GF)
    (h : ∀ p1 p2, DistLater n (r1 p1 p2) (r2 p1 p2)) a1 a2 (m1 m2 : iMsg GF V) :
    iProto_le_body r1 a1 a2 m1 m2 ≡{n}≡ iProto_le_body r2 a1 a2 m1 m2 := by
  cases a1 <;> cases a2 <;> simp only [iProto_le_body]
  · exact forall_ne fun _ => forall_ne fun _ => wand_ne.ne .rfl <| exists_ne fun _ =>
      sep_ne.ne (Contractive.distLater_dist (f := BIBase.later) (h _ _)) .rfl
  · exact .rfl
  · exact .rfl
  · exact forall_ne fun _ => forall_ne fun _ => wand_ne.ne .rfl <| exists_ne fun _ =>
      sep_ne.ne (Contractive.distLater_dist (f := BIBase.later) (h _ _)) .rfl

theorem iProto_le_pre_ne_r {n} (r1 r2 : iProto GF V → iProto GF V → IProp GF)
    (h : ∀ p1 p2, DistLater n (r1 p1 p2) (r2 p1 p2)) (p1 p2 : iProto GF V) :
    iProto_le_pre r1 p1 p2 ≡{n}≡ iProto_le_pre r2 p1 p2 :=
  or_ne.ne .rfl <| exists_ne fun _ => exists_ne fun _ => exists_ne fun _ => exists_ne fun _ =>
    sep_ne.ne .rfl <| sep_ne.ne .rfl <| iProto_le_body_ne r1 r2 h _ _ _ _

instance iProto_le_pre_ne (r : iProto GF V → iProto GF V → IProp GF) :
    NonExpansive₂ (iProto_le_pre r) where
  ne {_ _ _} h1 {_ _} h2 :=
    or_ne.ne (sep_ne.ne ((internalEq.ne_l _).ne h1) ((internalEq.ne_l _).ne h2)) <|
      exists_ne fun _ => exists_ne fun _ => exists_ne fun _ => exists_ne fun _ =>
        sep_ne.ne ((internalEq.ne_l _).ne h1) <| sep_ne.ne ((internalEq.ne_l _).ne h2) .rfl

def iProto_le_pre' (r : iProto GF V -n> iProto GF V -n> IProp GF) :
    iProto GF V -n> iProto GF V -n> IProp GF where
  f p1 := ⟨fun p2 => iProto_le_pre (fun p1' p2' => r p1' p2') p1 p2,
    ⟨fun {_ _ _} h => (iProto_le_pre_ne _).ne .rfl h⟩⟩
  ne := ⟨fun {_ _ _} h _ => (iProto_le_pre_ne _).ne h .rfl⟩

instance iProto_le_pre_contractive : Contractive (iProto_le_pre' (GF := GF) (V := V)) where
  distLater_dist {_ _ _} h p1 p2 :=
    iProto_le_pre_ne_r _ _ (fun q1 q2 k hk => h k hk q1 q2) p1 p2

def iProto_le (p1 p2 : iProto GF V) : IProp GF := fixpoint iProto_le_pre' p1 p2

instance iProto_le_ne : NonExpansive₂ (iProto_le (GF := GF) (V := V)) where
  ne {_ _ _} h1 {_ _} h2 := ((fixpoint iProto_le_pre').ne.ne h1 _).trans (((fixpoint iProto_le_pre') _).ne.ne h2)

theorem iProto_le_unfold (p1 p2 : iProto GF V) :
    iProto_le p1 p2 = iProto_le_pre iProto_le p1 p2 :=
  congrArg (fun g => Hom.f (Hom.f g p1) p2) (fixpoint_unfold iProto_le_pre'.toContractiveHom)

end le

scoped notation:25 p:26 " ⊑ " q:26 => iProto_le p q

/-! ## Auxiliary definitions -/

section interp
variable {GF : BundledGFunctors} {V : Type}

def iProto_app_recvs (vs : List V) (p : iProto GF V) : iProto GF V :=
  match vs with
  | [] => p
  | v :: vs => <?> iMsg_base v iprop(True) (iProto_app_recvs vs p)

def iProto_interp (vsl vsr : List V) (pl pr : iProto GF V) : IProp GF :=
  iprop(∃ p, iProto_le (iProto_app_recvs vsr p) pl ∗ iProto_le (iProto_app_recvs vsl (iProto_dual p)) pr)

end interp

/-! ## Proofs -/

section proofs
open ProofMode
attribute [local instance] internalEq.ne_l internalEq.ne_r
private instance idfun_ne {α : Type _} [OFE α] : NonExpansive (fun x : α => x) := ⟨fun _ _ _ h => h⟩
variable {GF : BundledGFunctors} {V : Type}

/-- Rocq `MsgTele`: `m` is (equal to) the telescopic message `∃.. x, MSG tv x {{ tP x }}; tp x`.
The telescope `TT` and `tv`, `tP`, `tp` are `outParam`s (Rocq: `Hint Mode MsgTele ! ! - ! - - -`),
computed from `m` by the instances `msg_tele_base` and `msg_tele_exist`. -/
class MsgTele {TT : outParam Iris.Std.Tele} (m : iMsg GF V) (tv : outParam (TT -t> V))
    (tP : outParam (TT -t> IProp GF)) (tp : outParam (TT -t> iProto GF V)) : Prop where
  msg_tele : m = iMsg_texist fun x =>
    iMsg_base (Iris.Std.Tele.app tv x) (Iris.Std.Tele.app tP x) (Iris.Std.Tele.app tp x)

theorem iMsg_ext {m1 m2 : iMsg GF V} (h : ∀ v p, m1.car v p ⊣⊢ m2.car v p) : m1 = m2 := by
  obtain ⟨m1⟩ := m1; obtain ⟨m2⟩ := m2
  congr; funext v; apply Hom.ext; funext p; exact BI.equiv_iff.mpr (h v p)

@[simp] theorem iMsg_base_car (v : V) (P : IProp GF) (p : iProto GF V) v' p' :
    (iMsg_base v P p).car v' p' = iprop(⌜v = v'⌝ ∗ Later.next p ≡ p' ∗ P) := by
  rw [iMsg_base_unseal]; rfl

@[simp] theorem iMsg_exist_car {A : Type _} (m : A → iMsg GF V) v' p' :
    (iMsg_exist m).car v' p' = iprop(∃ x, (m x).car v' p') := by
  rw [iMsg_exist_unseal]; rfl

@[simp] theorem iMsg_map_car (r : iProto GF V → iProto GF V) (m : iMsg GF V) v p1' :
    (iMsg_map r m).car v p1' = iprop(∃ p1, m.car v (Later.next p1) ∗ p1' ≡ Later.next (r p1)) :=
  rfl

instance iProto_le_ne_l (q : iProto GF V) : NonExpansive (fun p => iProto_le p q) :=
  ⟨fun {_ _ _} h => iProto_le_ne.ne h .rfl⟩
instance iProto_le_ne_r (q : iProto GF V) : NonExpansive (fun p => iProto_le q p) :=
  ⟨fun {_ _ _} h => iProto_le_ne.ne .rfl h⟩

theorem next_f_equivI {SPROP : Type _} [Sbi SPROP] {A B : Type _} [OFE A] [OFE B] (f : A → B)
    [hf : NonExpansive f] (x y : A) :
    (iprop(Later.next x ≡ Later.next y) : SPROP) ⊢ Later.next (f x) ≡ Later.next (f y) := by
  haveI : NonExpansive (fun z : Later A => Later.next (f z.car)) :=
    ⟨fun {_ _ _} h k hk => hf.ne (h k hk)⟩
  exact internalEq.of_internalEquiv_ne (fun z : Later A => Later.next (f z.car))

/-! ### Equality -/

theorem iProto_case (p : iProto GF V) : p = END ∨ ∃ a m, p = iProto_message a m := by
  rw [iProto_message_unseal, iProto_end_unseal]
  rcases proto_case p with h | ⟨a, m, h⟩
  · exact .inl h
  · exact .inr ⟨a, ⟨m⟩, h⟩

theorem iProto_message_equivI {SPROP : Type _} [Sbi SPROP] (a1 a2 : action) (m1 m2 : iMsg GF V) :
    (iprop(iProto_message a1 m1 ≡ iProto_message a2 m2) : SPROP) ⊣⊢
      iprop(⌜a1 = a2⌝ ∧ ∀ v lp, m1.car v lp ≡ m2.car v lp) := by
  rw [iProto_message_unseal]; exact proto_message_equivI a1 a2 m1.car m2.car

theorem iProto_message_end_equivI {SPROP : Type _} [Sbi SPROP] (a : action) (m : iMsg GF V) :
    (iprop(iProto_message a m ≡ END) : SPROP) ⊢ False := by
  rw [iProto_message_unseal, iProto_end_unseal]; exact proto_message_end_equivI a m.car

theorem iProto_end_message_equivI {SPROP : Type _} [Sbi SPROP] (a : action) (m : iMsg GF V) :
    (iprop(END ≡ iProto_message a m) : SPROP) ⊢ False :=
  internalEq.symm.trans (iProto_message_end_equivI a m)

/-! ### Non-expansiveness of operators -/

theorem iMsg_contractive (v : V) {n} {P1 P2 : IProp GF} {p1 p2 : iProto GF V}
    (HP : P1 ≡{n}≡ P2) (Hp : DistLater n p1 p2) :
    iMsg_base v P1 p1 ≡{n}≡ iMsg_base v P2 p2 := by
  rw [iMsg_base_unseal]
  exact fun w q => sep_ne.ne .rfl (sep_ne.ne ((internalEq.ne_l _).ne (NextContractive.distLater_dist Hp)) HP)

theorem iMsg_ne (v : V) {n} {P1 P2 : IProp GF} {p1 p2 : iProto GF V}
    (HP : P1 ≡{n}≡ P2) (Hp : p1 ≡{n}≡ p2) :
    iMsg_base v P1 p1 ≡{n}≡ iMsg_base v P2 p2 :=
  iMsg_contractive v HP Hp.distLater

theorem iMsg_exist_ne {A : Type _} {n} {m1 m2 : A → iMsg GF V} (Hm : ∀ x, m1 x ≡{n}≡ m2 x) :
    iMsg_exist m1 ≡{n}≡ iMsg_exist m2 := by
  rw [iMsg_exist_unseal]; exact fun w q => exists_ne fun x => Hm x w q

instance iProto_message_ne (a : action) : NonExpansive (iProto_message (GF := GF) (V := V) a) := by
  rw [iProto_message_unseal]
  exact ⟨fun {_ _ _} h => proto_message_ne a h⟩

/-! ### Helpers -/

theorem iMsg_map_base (f : iProto GF V → iProto GF V) [NonExpansive f] (v : V) (P : IProp GF)
    (p : iProto GF V) : iMsg_map f (iMsg_base v P p) = iMsg_base v P (f p) := by
  rw [iMsg_base_unseal]
  refine iMsg_ext fun v' p' => ⟨?_, ?_⟩
  · simp only [iMsg_map, iMsg_base_def]
    refine exists_elim fun p'' => ?_
    iintro ⟨⟨%Hv, #Hp, HP⟩, #Hp'⟩
    isplitl []
    · ipureintro; exact Hv
    · isplitl []
      · irewrite [Hp']
        iapply (next_f_equivI f p p'') $$ Hp
      · iexact HP
  · simp only [iMsg_map, iMsg_base_def]
    iintro ⟨%Hv, #Hp, HP⟩
    iexists p
    isplitl [HP]
    · isplitl []
      · ipureintro; exact Hv
      · isplitl []
        · istop; exact internalEq.refl
        · iexact HP
    · iapply internalEq.symm $$ Hp

theorem iMsg_map_exist {A : Type _} (f : iProto GF V → iProto GF V) (m : A → iMsg GF V) :
    iMsg_map f (iMsg_exist m) = iMsg_exist fun x => iMsg_map f (m x) := by
  rw [iMsg_exist_unseal]
  refine iMsg_ext fun v' p' => ⟨?_, ?_⟩
  · simp only [iMsg_map, iMsg_exist_def]
    iintro ⟨%p'', ⟨%x, H⟩, Hp'⟩
    iexists x
    iexists p''
    isplitl [H]
    · iexact H
    · iexact Hp'
  · simp only [iMsg_map, iMsg_exist_def]
    iintro ⟨%x, %p'', H, Hp'⟩
    iexists p''
    isplitl [H]
    · iexists x
      iexact H
    · iexact Hp'

theorem iMsg_map_id (m : iMsg GF V) : iMsg_map id m = m := by
  refine iMsg_ext fun v p' => ⟨?_, ?_⟩
  · simp only [iMsg_map, id]
    iintro ⟨%p1, Hm, #Heq⟩
    irewrite [Heq]
    iexact Hm
  · obtain ⟨q, rfl⟩ := Later.uninj p'
    simp only [iMsg_map, id]
    iintro Hm
    iexists q
    isplitl [Hm]
    · iexact Hm
    · istop; exact internalEq.refl

theorem iMsg_map_map (f g : iProto GF V → iProto GF V) [NonExpansive f] (m : iMsg GF V) :
    iMsg_map f (iMsg_map g m) = iMsg_map (fun p => f (g p)) m := by
  refine iMsg_ext fun v p' => ⟨?_, ?_⟩
  · simp only [iMsg_map]
    iintro ⟨%p1, ⟨%p0, Hm, #Heq0⟩, #Heq1⟩
    iexists p0
    isplitl [Hm]
    · iexact Hm
    · irewrite [Heq1]
      iapply (next_f_equivI f p1 (g p0)) $$ Heq0
  · simp only [iMsg_map]
    iintro ⟨%p0, Hm, #Heq⟩
    iexists g p0
    isplitl [Hm]
    · iexists p0
      isplitl [Hm]
      · iexact Hm
      · istop; exact internalEq.refl
    · iexact Heq

/-! ### Dual -/

instance iProto_dual_ne : NonExpansive (iProto_dual (GF := GF) (V := V)) := by
  rw [iProto_dual_unseal]; unfold iProto_dual_def; infer_instance

instance iProto_dual_if_ne (d : Bool) : NonExpansive (iProto_dual_if (GF := GF) (V := V) d) := by
  cases d
  · exact ⟨fun _ _ _ h => h⟩
  · show NonExpansive iProto_dual; infer_instance

@[simp] theorem iProto_dual_end : iProto_dual (GF := GF) (V := V) END = END := by
  rw [iProto_dual_unseal, iProto_end_unseal]
  simp only [iProto_dual_def, iProto_end_def]
  rw [iProto_map_app_unfold]; rfl

theorem iProto_dual_message (a : action) (m : iMsg GF V) :
    iProto_dual (iProto_message a m) = iProto_message (action_dual a) (iMsg_dual m) := by
  simp only [iMsg_dual, iProto_dual_unseal, iProto_message_unseal, iProto_dual_def,
    iProto_message_def]
  rw [iProto_map_app_unfold]
  simp only [iProto_map_app_aux, proto_elim_message]
  rfl

theorem iMsg_dual_base (v : V) (P : IProp GF) (p : iProto GF V) :
    iMsg_dual (iMsg_base v P p) = iMsg_base v P (iProto_dual p) := iMsg_map_base _ v P p

theorem iMsg_dual_exist {A : Type _} (m : A → iMsg GF V) :
    iMsg_dual (iMsg_exist m) = iMsg_exist fun x => iMsg_dual (m x) := iMsg_map_exist _ m

private theorem iProto_dual_involutive_dist (n : Nat) :
    ∀ p : iProto GF V, iProto_dual (iProto_dual p) ≡{n}≡ p := by
  induction n using Nat.strongRecOn with
  | _ n IH =>
  intro p
  rcases iProto_case p with rfl | ⟨a, m, rfl⟩
  · simp only [iProto_dual_end]; exact .rfl
  · rw [iProto_dual_message, iProto_dual_message, action_dual_involutive, iMsg_dual, iMsg_dual,
      iMsg_map_map]
    refine ((iProto_message_ne a).ne (iMsg_map_ne_r _ id m fun q k hk => IH k hk q)).trans ?_
    rw [iMsg_map_id]

theorem iProto_dual_involutive (p : iProto GF V) : iProto_dual (iProto_dual p) = p :=
  OFE.eq_dist_2 fun n => iProto_dual_involutive_dist n p

/-! ### Append -/

instance iProto_app_ne_l (p2 : iProto GF V) : NonExpansive (fun p => iProto_app p p2) := by
  rw [iProto_app_unseal]; unfold iProto_app_def; infer_instance

@[simp] theorem iProto_app_end_l (p : iProto GF V) : iProto_app END p = p := by
  rw [iProto_app_unseal, iProto_end_unseal]
  simp only [iProto_app_def, iProto_end_def]
  rw [iProto_map_app_unfold]; rfl

theorem iProto_app_message (a : action) (m : iMsg GF V) (p2 : iProto GF V) :
    iProto_app (iProto_message a m) p2 = iProto_message a (iMsg_map (fun p => iProto_app p p2) m) := by
  simp only [iProto_app_unseal, iProto_message_unseal, iProto_app_def, iProto_message_def]
  rw [iProto_map_app_unfold]
  simp only [iProto_map_app_aux, proto_elim_message]
  rfl

private theorem iProto_app_ne_r_dist (n : Nat) :
    ∀ (p1 p2 p2' : iProto GF V), p2 ≡{n}≡ p2' → iProto_app p1 p2 ≡{n}≡ iProto_app p1 p2' := by
  induction n using Nat.strongRecOn with
  | _ n IH =>
  intro p1 p2 p2' h
  rcases iProto_case p1 with rfl | ⟨a, m, rfl⟩
  · simpa using h
  · rw [iProto_app_message, iProto_app_message]
    exact (iProto_message_ne a).ne (iMsg_map_ne_r _ _ m fun q k hk => IH k hk q _ _ (h.lt hk))

instance iProto_app_ne : NonExpansive₂ (iProto_app (GF := GF) (V := V)) where
  ne {_ p1 p1'} h1 {p2 p2'} h2 :=
    ((iProto_app_ne_l p2).ne h1).trans (iProto_app_ne_r_dist _ p1' p2 p2' h2)

theorem iMsg_app_base (v : V) (P : IProp GF) (p1 p2 : iProto GF V) :
    iMsg_map (fun p => iProto_app p p2) (iMsg_base v P p1) = iMsg_base v P (iProto_app p1 p2) :=
  iMsg_map_base _ v P p1

theorem iMsg_app_exist {A : Type _} (m : A → iMsg GF V) (p2 : iProto GF V) :
    iMsg_map (fun p => iProto_app p p2) (iMsg_exist m) =
      iMsg_exist fun x => iMsg_map (fun p => iProto_app p p2) (m x) := iMsg_map_exist _ m

private theorem iProto_app_end_r_dist (n : Nat) :
    ∀ p : iProto GF V, iProto_app p END ≡{n}≡ p := by
  induction n using Nat.strongRecOn with
  | _ n IH =>
  intro p
  rcases iProto_case p with rfl | ⟨a, m, rfl⟩
  · simp only [iProto_app_end_l]; exact .rfl
  · rw [iProto_app_message]
    refine ((iProto_message_ne a).ne (iMsg_map_ne_r _ id m fun q k hk => IH k hk q)).trans ?_
    rw [iMsg_map_id]

@[simp] theorem iProto_app_end_r (p : iProto GF V) : iProto_app p END = p :=
  OFE.eq_dist_2 fun n => iProto_app_end_r_dist n p

private theorem iProto_app_assoc_dist (n : Nat) :
    ∀ p1 p2 p3 : iProto GF V,
      iProto_app p1 (iProto_app p2 p3) ≡{n}≡ iProto_app (iProto_app p1 p2) p3 := by
  induction n using Nat.strongRecOn with
  | _ n IH =>
  intro p1 p2 p3
  rcases iProto_case p1 with rfl | ⟨a, m, rfl⟩
  · simp only [iProto_app_end_l]; exact .rfl
  · rw [iProto_app_message, iProto_app_message, iProto_app_message, iMsg_map_map]
    exact (iProto_message_ne a).ne (iMsg_map_ne_r _ _ m fun q k hk => IH k hk q p2 p3)

theorem iProto_app_assoc (p1 p2 p3 : iProto GF V) :
    iProto_app p1 (iProto_app p2 p3) = iProto_app (iProto_app p1 p2) p3 :=
  OFE.eq_dist_2 fun n => iProto_app_assoc_dist n p1 p2 p3

private theorem iProto_dual_app_dist (n : Nat) :
    ∀ p1 p2 : iProto GF V,
      iProto_dual (iProto_app p1 p2) ≡{n}≡ iProto_app (iProto_dual p1) (iProto_dual p2) := by
  induction n using Nat.strongRecOn with
  | _ n IH =>
  intro p1 p2
  rcases iProto_case p1 with rfl | ⟨a, m, rfl⟩
  · simp only [iProto_app_end_l, iProto_dual_end]; exact .rfl
  · rw [iProto_app_message, iProto_dual_message, iProto_dual_message, iProto_app_message,
      iMsg_dual, iMsg_dual, iMsg_map_map, iMsg_map_map]
    exact (iProto_message_ne _).ne (iMsg_map_ne_r _ _ m fun q k hk => IH k hk q p2)

theorem iProto_dual_app (p1 p2 : iProto GF V) :
    iProto_dual (iProto_app p1 p2) = iProto_app (iProto_dual p1) (iProto_dual p2) :=
  OFE.eq_dist_2 fun n => iProto_dual_app_dist n p1 p2

/-! ### Protocol entailment -/

theorem iProto_le_end : ⊢ iProto_le (GF := GF) (V := V) END END := by
  rw [iProto_le_unfold]; unfold iProto_le_pre
  ileft
  isplitl []
  · istop; exact internalEq.refl
  · istop; exact internalEq.refl

theorem iProto_le_send (m1 m2 : iMsg GF V) :
    iprop(∀ v p2', m2.car v (Later.next p2') -∗
      ∃ p1', ▷ iProto_le p1' p2' ∗ m1.car v (Later.next p1')) ⊢
    iProto_le (<!> m1) (<!> m2) := by
  rw [iProto_le_unfold]; unfold iProto_le_pre
  iintro H
  iright
  iexists Send, Send, m1, m2
  isplitl []
  · istop; exact internalEq.refl
  isplitl []
  · istop; exact internalEq.refl
  iunfold iProto_le_body
  iexact H

theorem iProto_le_recv (m1 m2 : iMsg GF V) :
    iprop(∀ v p1', m1.car v (Later.next p1') -∗
      ∃ p2', ▷ iProto_le p1' p2' ∗ m2.car v (Later.next p2')) ⊢
    iProto_le (<?> m1) (<?> m2) := by
  rw [iProto_le_unfold]; unfold iProto_le_pre
  iintro H
  iright
  iexists Recv, Recv, m1, m2
  isplitl []
  · istop; exact internalEq.refl
  isplitl []
  · istop; exact internalEq.refl
  iunfold iProto_le_body
  iexact H

theorem iProto_le_end_inv_l (p : iProto GF V) : iProto_le p END ⊢ p ≡ END := by
  rw [iProto_le_unfold]; unfold iProto_le_pre
  iintro (⟨Hp, _⟩ | ⟨%a1, %a2, %m1, %m2, _, Heq, _⟩)
  · iexact Hp
  · iexfalso
    iapply (iProto_end_message_equivI a2 m2) $$ Heq

theorem iProto_le_end_inv_r (p : iProto GF V) : iProto_le END p ⊢ p ≡ END := by
  rw [iProto_le_unfold]; unfold iProto_le_pre
  iintro (⟨_, Hp⟩ | ⟨%a1, %a2, %m1, %m2, Heq, _, _⟩)
  · iexact Hp
  · iexfalso
    iapply (iProto_end_message_equivI a1 m1) $$ Heq

theorem iProto_le_send_inv (p1 : iProto GF V) (m2 : iMsg GF V) :
    iProto_le p1 (<!> m2) ⊢ ∃ m1, (p1 ≡ <!> m1) ∗
      ∀ v p2', m2.car v (Later.next p2') -∗
        ∃ p1', ▷ iProto_le p1' p2' ∗ m1.car v (Later.next p1') := by
  rw [iProto_le_unfold]; unfold iProto_le_pre
  iintro (⟨_, Heq⟩ | ⟨%a1, %a2, %m1, %m2', Hp1, Hp2, H⟩)
  · iexfalso
    iapply (iProto_message_end_equivI Send m2) $$ Heq
  · icases (iProto_message_equivI Send a2 m2 m2').1 $$ Hp2 with ⟨%Ha, #Hm⟩
    subst Ha
    cases a1 <;> iunfold iProto_le_body at H
    · iexists m1
      isplitl [Hp1]
      · iexact Hp1
      · iintro %v %p2' Hm2
        iapply H $$ %v %p2'
        ihave Heqv := Hm $$ %v %(Later.next p2')
        irewrite [← Heqv]
        iexact Hm2
    · iexfalso
      iexact H

theorem iProto_le_recv_inv (p1 : iProto GF V) (m2 : iMsg GF V) :
    iProto_le p1 (<?> m2) ⊢ ∃ m1, (p1 ≡ <?> m1) ∗
      ∀ v p1', m1.car v (Later.next p1') -∗
        ∃ p2', ▷ iProto_le p1' p2' ∗ m2.car v (Later.next p2') := by
  rw [iProto_le_unfold]; unfold iProto_le_pre
  iintro (⟨_, Heq⟩ | ⟨%a1, %a2, %m1, %m2', Hp1, Hp2, H⟩)
  · iexfalso
    iapply (iProto_message_end_equivI Recv m2) $$ Heq
  · icases (iProto_message_equivI Recv a2 m2 m2').1 $$ Hp2 with ⟨%Ha, #Hm⟩
    subst Ha
    cases a1 <;> iunfold iProto_le_body at H
    · iexfalso
      iexact H
    · iexists m1
      isplitl [Hp1]
      · iexact Hp1
      · iintro %v %p1' Hm1
        icases H $$ %v %p1' Hm1 with ⟨%p2', Hle, Hm2⟩
        iexists p2'
        isplitl [Hle]
        · iexact Hle
        · ihave Heqv := Hm $$ %v %(Later.next p2')
          irewrite [Heqv]
          iexact Hm2

theorem iProto_le_send_send_inv (m1 m2 : iMsg GF V) (v : V) (p2' : iProto GF V) :
    iProto_le (<!> m1) (<!> m2) ⊢ m2.car v (Later.next p2') -∗
      ∃ p1', ▷ iProto_le p1' p2' ∗ m1.car v (Later.next p1') := by
  iintro H Hm2
  icases (iProto_le_send_inv _ m2) $$ H with ⟨%m1', Hm1, H⟩
  icases (iProto_message_equivI Send Send m1 m1').1 $$ Hm1 with ⟨_, #Hm1⟩
  icases H $$ %v %p2' Hm2 with ⟨%p1', Hle, Hm⟩
  iexists p1'
  isplitl [Hle]
  · iexact Hle
  · ihave Heqv := Hm1 $$ %v %(Later.next p1')
    irewrite [Heqv]
    iexact Hm

theorem iProto_le_recv_send_inv (m1 m2 : iMsg GF V) :
    iProto_le (<?> m1) (<!> m2) ⊢ False := by
  iintro H
  icases (iProto_le_send_inv _ m2) $$ H with ⟨%m1', Hm1, _⟩
  icases (iProto_message_equivI Recv Send m1 m1').1 $$ Hm1 with ⟨%Ha, _⟩
  cases Ha

theorem iProto_le_recv_recv_inv (m1 m2 : iMsg GF V) (v : V) (p1' : iProto GF V) :
    iProto_le (<?> m1) (<?> m2) ⊢ m1.car v (Later.next p1') -∗
      ∃ p2', ▷ iProto_le p1' p2' ∗ m2.car v (Later.next p2') := by
  iintro H Hm1
  icases (iProto_le_recv_inv _ m2) $$ H with ⟨%m1', Heq, H⟩
  icases (iProto_message_equivI Recv Recv m1 m1').1 $$ Heq with ⟨_, #Heq⟩
  ihave Heqv := Heq $$ %v %(Later.next p1')
  irewrite [Heqv] at Hm1
  iapply H $$ %v %p1' Hm1

private theorem iProto_le_refl_all : ⊢ ∀ p : iProto GF V, iProto_le p p := by
  iloeb as IH
  iintro %p
  rcases iProto_case p with rfl | ⟨a, m, rfl⟩
  · iapply iProto_le_end
  · cases a
    · iapply iProto_le_send
      iintro %v %p2' Hm
      iexists p2'
      isplitr [Hm]
      · inext
        iapply IH
      · iexact Hm
    · iapply iProto_le_recv
      iintro %v %p1' Hm
      iexists p1'
      isplitr [Hm]
      · inext
        iapply IH
      · iexact Hm

theorem iProto_le_refl (p : iProto GF V) : ⊢ iProto_le p p :=
  iProto_le_refl_all.trans (forall_elim p)

private theorem iProto_le_trans_all : ⊢ ∀ p1 p2 p3,
    iProto_le (GF := GF) (V := V) p1 p2 -∗ iProto_le p2 p3 -∗ iProto_le p1 p3 := by
  iloeb as IH
  iintro %p1 %p2 %p3 H1 H2
  rcases iProto_case p3 with rfl | ⟨a, m3, rfl⟩
  · ihave H2 := (iProto_le_end_inv_l p2) $$ H2
    irewrite [H2] at H1
    iexact H1
  · cases a
    · icases (iProto_le_send_inv p2 m3) $$ H2 with ⟨%m2, Hp2, H2⟩
      irewrite [Hp2] at H1
      icases (iProto_le_send_inv p1 m2) $$ H1 with ⟨%m1, Hp1, H1⟩
      irewrite [Hp1]
      iapply iProto_le_send
      iintro %v %p3' Hm3
      icases H2 $$ %v %p3' Hm3 with ⟨%p2', Hle, Hm2⟩
      icases H1 $$ %v %p2' Hm2 with ⟨%p1', Hle', Hm1⟩
      iexists p1'
      isplitr [Hm1]
      · inext
        iapply IH $$ %p1' %p2' %p3' Hle' Hle
      · iexact Hm1
    · icases (iProto_le_recv_inv p2 m3) $$ H2 with ⟨%m2, Hp2, H3⟩
      irewrite [Hp2] at H1
      icases (iProto_le_recv_inv p1 m2) $$ H1 with ⟨%m1, Hp1, H2⟩
      irewrite [Hp1]
      iapply iProto_le_recv
      iintro %v %p1' Hm1
      icases H2 $$ %v %p1' Hm1 with ⟨%p2', Hle, Hm2⟩
      icases H3 $$ %v %p2' Hm2 with ⟨%p3', Hle', Hm3⟩
      iexists p3'
      isplitr [Hm3]
      · inext
        iapply IH $$ %p1' %p2' %p3' Hle Hle'
      · iexact Hm3

theorem iProto_le_trans (p1 p2 p3 : iProto GF V) :
    iProto_le p1 p2 ⊢ iProto_le p2 p3 -∗ iProto_le p1 p3 := by
  iintro H1 H2
  iapply iProto_le_trans_all $$ %p1 %p2 %p3 H1 H2

theorem iProto_le_payload_elim_l (m : iMsg GF V) (v : V) (P : IProp GF) (p : iProto GF V) :
    iprop(P -∗ iProto_le (<?> iMsg_base v iprop(True) p) (<?> m)) ⊢
      iProto_le (<?> iMsg_base v P p) (<?> m) := by
  iintro H
  iapply iProto_le_recv
  iintro %v' %p' Hb
  isimp only [iMsg_base_car] at Hb
  icases Hb with ⟨%Hv, #Hp, HP⟩
  ispecialize H $$ HP
  iapply (iProto_le_recv_recv_inv _ m v' p') $$ H
  isimp only [iMsg_base_car]
  isplitl []
  · ipureintro; exact Hv
  · isplitl []
    · iexact Hp
    · ipureintro; trivial

theorem iProto_le_payload_elim_r (m : iMsg GF V) (v : V) (P : IProp GF) (p : iProto GF V) :
    iprop(P -∗ iProto_le (<!> m) (<!> iMsg_base v iprop(True) p)) ⊢
      iProto_le (<!> m) (<!> iMsg_base v P p) := by
  iintro H
  iapply iProto_le_send
  iintro %v' %p' Hb
  isimp only [iMsg_base_car] at Hb
  icases Hb with ⟨%Hv, #Hp, HP⟩
  ispecialize H $$ HP
  iapply (iProto_le_send_send_inv m _ v' p') $$ H
  isimp only [iMsg_base_car]
  isplitl []
  · ipureintro; exact Hv
  · isplitl []
    · iexact Hp
    · ipureintro; trivial

theorem iProto_le_payload_intro_l (v : V) (P : IProp GF) (p : iProto GF V) :
    P ⊢ iProto_le (<!> iMsg_base v P p) (<!> iMsg_base v iprop(True) p) := by
  iintro HP
  iapply iProto_le_send
  iintro %v' %p' Hb
  isimp only [iMsg_base_car] at Hb
  icases Hb with ⟨%Hv, #Hp, _⟩
  iexists p'
  isplitl []
  · iapply later_intro
    iapply iProto_le_refl
  · isimp only [iMsg_base_car]
    isplitl []
    · ipureintro; exact Hv
    · isplitl []
      · iexact Hp
      · iexact HP

theorem iProto_le_payload_intro_r (v : V) (P : IProp GF) (p : iProto GF V) :
    P ⊢ iProto_le (<?> iMsg_base v iprop(True) p) (<?> iMsg_base v P p) := by
  iintro HP
  iapply iProto_le_recv
  iintro %v' %p' Hb
  isimp only [iMsg_base_car] at Hb
  icases Hb with ⟨%Hv, #Hp, _⟩
  iexists p'
  isplitl []
  · iapply later_intro
    iapply iProto_le_refl
  · isimp only [iMsg_base_car]
    isplitl []
    · ipureintro; exact Hv
    · isplitl []
      · iexact Hp
      · iexact HP

theorem iProto_le_exist_elim_l {A : Type _} (m1 : A → iMsg GF V) (m2 : iMsg GF V) :
    iprop(∀ x, iProto_le (<?> m1 x) (<?> m2)) ⊢ iProto_le (<?> iMsg_exist m1) (<?> m2) := by
  iintro H
  iapply iProto_le_recv
  iintro %v %p1' Hm
  isimp only [iMsg_exist_car] at Hm
  icases Hm with ⟨%x, Hm⟩
  iapply (iProto_le_recv_recv_inv (m1 x) m2 v p1') $$ [H] Hm
  iapply H

theorem iProto_le_exist_elim_r {A : Type _} (m1 : iMsg GF V) (m2 : A → iMsg GF V) :
    iprop(∀ x, iProto_le (<!> m1) (<!> m2 x)) ⊢ iProto_le (<!> m1) (<!> iMsg_exist m2) := by
  iintro H
  iapply iProto_le_send
  iintro %v %p2' Hm
  isimp only [iMsg_exist_car] at Hm
  icases Hm with ⟨%x, Hm⟩
  iapply (iProto_le_send_send_inv m1 (m2 x) v p2') $$ [H] Hm
  iapply H

theorem iProto_le_exist_intro_l {A : Type _} (m : A → iMsg GF V) (a : A) :
    ⊢ iProto_le (<!> iMsg_exist m) (<!> m a) := by
  iapply iProto_le_send
  iintro %v %p' Hm
  iexists p'
  isplitr [Hm]
  · inext
    iapply iProto_le_refl
  · isimp only [iMsg_exist_car]
    iexists a
    iexact Hm

theorem iProto_le_exist_intro_r {A : Type _} (m : A → iMsg GF V) (a : A) :
    ⊢ iProto_le (<?> m a) (<?> iMsg_exist m) := by
  iapply iProto_le_recv
  iintro %v %p' Hm
  iexists p'
  isplitr [Hm]
  · inext
    iapply iProto_le_refl
  · isimp only [iMsg_exist_car]
    iexists a
    iexact Hm

theorem iProto_le_base (a : action) (v : V) (P : IProp GF) (p1 p2 : iProto GF V) :
    ▷ iProto_le p1 p2 ⊢ iProto_le (iProto_message a (iMsg_base v P p1)) (iProto_message a (iMsg_base v P p2)) := by
  iintro H
  cases a
  · iapply iProto_le_send
    iintro %v' %p' Hb
    isimp only [iMsg_base_car] at Hb
    icases Hb with ⟨%Hv, #Hp, HP⟩
    iexists p1
    ihave Hp' := (later_equivI_mp p2 p') $$ Hp
    isplitr [HP]
    · iclear Hp
      inext
      irewrite [← Hp']
      iexact H
    · isimp only [iMsg_base_car]
      isplitl []
      · ipureintro; exact Hv
      · isplitl []
        · istop; exact internalEq.refl
        · iexact HP
  · iapply iProto_le_recv
    iintro %v' %p' Hb
    isimp only [iMsg_base_car] at Hb
    icases Hb with ⟨%Hv, #Hp, HP⟩
    iexists p2
    ihave Hp' := (later_equivI_mp p1 p') $$ Hp
    isplitr [HP]
    · iclear Hp
      inext
      irewrite [← Hp']
      iexact H
    · isimp only [iMsg_base_car]
      isplitl []
      · ipureintro; exact Hv
      · isplitl []
        · istop; exact internalEq.refl
        · iexact HP

private theorem iProto_le_dual_all : ⊢ ∀ p1 p2,
    iProto_le (GF := GF) (V := V) p2 p1 -∗ iProto_le (iProto_dual p1) (iProto_dual p2) := by
  iloeb as IH
  iintro %p1 %p2 H
  rcases iProto_case p1 with rfl | ⟨a, m1, rfl⟩
  · ihave H := (iProto_le_end_inv_l p2) $$ H
    ihave H := (internalEq.of_internalEquiv_ne iProto_dual) $$ H
    irewrite [H]
    iapply iProto_le_refl
  · cases a
    · icases (iProto_le_send_inv p2 m1) $$ H with ⟨%m2, Hp2, H⟩
      ihave Hp2 := (internalEq.of_internalEquiv_ne iProto_dual) $$ Hp2
      irewrite [Hp2]
      rw [iProto_dual_message, iProto_dual_message, show action_dual Send = Recv from rfl]
      iapply iProto_le_recv
      iintro %v %p1d Hm
      isimp only [iMsg_dual, iMsg_map_car] at Hm
      icases Hm with ⟨%p1', Hm1, #Hp1d⟩
      icases H $$ %v %p1' Hm1 with ⟨%p2', H, Hm2⟩
      iexists (iProto_dual p2')
      isplitl [H]
      · ihave HH := (later_equivI_mp p1d (iProto_dual p1')) $$ Hp1d
        iclear Hp1d
        inext
        irewrite [HH]
        iapply IH $$ %p1' %p2' H
      · isimp only [iMsg_dual, iMsg_map_car]
        iexists p2'
        isplitl [Hm2]
        · iexact Hm2
        · istop; exact internalEq.refl
    · icases (iProto_le_recv_inv p2 m1) $$ H with ⟨%m2, Hp2, H⟩
      ihave Hp2 := (internalEq.of_internalEquiv_ne iProto_dual) $$ Hp2
      irewrite [Hp2]
      rw [iProto_dual_message, iProto_dual_message, show action_dual Recv = Send from rfl]
      iapply iProto_le_send
      iintro %v %p2d Hm
      isimp only [iMsg_dual, iMsg_map_car] at Hm
      icases Hm with ⟨%p2', Hm2, #Hp2d⟩
      icases H $$ %v %p2' Hm2 with ⟨%p1', H, Hm1⟩
      iexists (iProto_dual p1')
      isplitl [H]
      · ihave HH := (later_equivI_mp p2d (iProto_dual p2')) $$ Hp2d
        iclear Hp2d
        inext
        irewrite [HH]
        iapply IH $$ %p1' %p2' H
      · isimp only [iMsg_dual, iMsg_map_car]
        iexists p1'
        isplitl [Hm1]
        · iexact Hm1
        · istop; exact internalEq.refl

theorem iProto_le_dual (p1 p2 : iProto GF V) :
    iProto_le p2 p1 ⊢ iProto_le (iProto_dual p1) (iProto_dual p2) := by
  iintro H
  iapply iProto_le_dual_all $$ %p1 %p2 H

theorem iProto_le_amber_internal (p1 p2 : iProto GF V → iProto GF V) [Contractive p1]
    [Contractive p2] :
    iprop(□ (∀ rec1 rec2, ▷ iProto_le rec1 rec2 → iProto_le (p1 rec1) (p2 rec2))) ⊢
      iProto_le (fixpoint p1) (fixpoint p2) := by
  have e : iProto_le (fixpoint p1) (fixpoint p2) =
      iProto_le (p1 (fixpoint p1)) (p2 (fixpoint p2)) :=
    congr (congrArg iProto_le (fixpoint_unfold p1.toContractiveHom)) (fixpoint_unfold p2.toContractiveHom)
  iintro #H
  iloeb as IH
  rw [e]
  iapply H
  rw [← e]
  iexact IH

theorem iProto_le_amber_external (p1 p2 : iProto GF V → iProto GF V) [Contractive p1]
    [Contractive p2]
    (IH : ∀ rec1 rec2, (⊢ iProto_le rec1 rec2) → ⊢ iProto_le (p1 rec1) (p2 rec2)) :
    ⊢ iProto_le (fixpoint p1) (fixpoint p2) := by
  refine OFE.ContractiveHom.fixpoint_ind p1.toContractiveHom
    (fun x => ⊢ iProto_le x (fixpoint p2)) (fun _ _ h hA => h ▸ hA) (fixpoint p2)
    (iProto_le_refl _) (fun x hx => ?_) (limitPreserving_emp_valid _)
  have e : fixpoint p2 = p2 (fixpoint p2) := fixpoint_unfold p2.toContractiveHom
  show ⊢ iProto_le (p1 x) (fixpoint p2)
  rw [e]; exact IH _ _ hx

theorem iProto_le_dual_l (p1 p2 : iProto GF V) :
    iProto_le (iProto_dual p2) p1 ⊢ iProto_le (iProto_dual p1) p2 := by
  have h := iProto_le_dual p1 (iProto_dual p2)
  rwa [iProto_dual_involutive] at h

theorem iProto_le_dual_r (p1 p2 : iProto GF V) :
    iProto_le p2 (iProto_dual p1) ⊢ iProto_le p1 (iProto_dual p2) := by
  have h := iProto_le_dual (iProto_dual p1) p2
  rwa [iProto_dual_involutive] at h

private theorem iProto_le_app_all : ⊢ ∀ p1 p2 p3 p4,
    iProto_le (GF := GF) (V := V) p1 p2 -∗ iProto_le p3 p4 -∗
      iProto_le (iProto_app p1 p3) (iProto_app p2 p4) := by
  iloeb as IH
  iintro %p1 %p2 %p3 %p4 H1 H2
  rcases iProto_case p2 with rfl | ⟨a, m2, rfl⟩
  · ihave H1 := (iProto_le_end_inv_l p1) $$ H1
    ihave H1 := (internalEq.of_internalEquiv_ne (fun x => iProto_app x p3)) $$ H1
    irewrite [H1]
    rw [iProto_app_end_l, iProto_app_end_l]
    iexact H2
  · cases a
    · icases (iProto_le_send_inv p1 m2) $$ H1 with ⟨%m1, Hp1, H1⟩
      ihave Hp1 := (internalEq.of_internalEquiv_ne (fun x => iProto_app x p3)) $$ Hp1
      irewrite [Hp1]
      rw [iProto_app_message, iProto_app_message]
      iapply iProto_le_send
      iintro %v %p24 Hm
      isimp only [iMsg_map_car] at Hm
      icases Hm with ⟨%p2', Hm2, #Hp24⟩
      icases H1 $$ %v %p2' Hm2 with ⟨%p1', H1, Hm1⟩
      iexists (iProto_app p1' p3)
      isplitr [Hm1]
      · ihave HH := (later_equivI_mp p24 (iProto_app p2' p4)) $$ Hp24
        iclear Hp24
        inext
        irewrite [HH]
        iapply IH $$ %p1' %p2' %p3 %p4 H1 H2
      · isimp only [iMsg_map_car]
        iexists p1'
        isplitl [Hm1]
        · iexact Hm1
        · istop; exact internalEq.refl
    · icases (iProto_le_recv_inv p1 m2) $$ H1 with ⟨%m1, Hp1, H1⟩
      ihave Hp1 := (internalEq.of_internalEquiv_ne (fun x => iProto_app x p3)) $$ Hp1
      irewrite [Hp1]
      rw [iProto_app_message, iProto_app_message]
      iapply iProto_le_recv
      iintro %v %p13 Hm
      isimp only [iMsg_map_car] at Hm
      icases Hm with ⟨%p1', Hm1, #Hp13⟩
      icases H1 $$ %v %p1' Hm1 with ⟨%p2'', H1, Hm2⟩
      iexists (iProto_app p2'' p4)
      isplitr [Hm2]
      · ihave HH := (later_equivI_mp p13 (iProto_app p1' p3)) $$ Hp13
        iclear Hp13
        inext
        irewrite [HH]
        iapply IH $$ %p1' %p2'' %p3 %p4 H1 H2
      · isimp only [iMsg_map_car]
        iexists p2''
        isplitl [Hm2]
        · iexact Hm2
        · istop; exact internalEq.refl

theorem iProto_le_app (p1 p2 p3 p4 : iProto GF V) :
    iProto_le p1 p2 ⊢ iProto_le p3 p4 -∗ iProto_le (iProto_app p1 p3) (iProto_app p2 p4) := by
  iintro H1 H2
  iapply iProto_le_app_all $$ %p1 %p2 %p3 %p4 H1 H2

/-! ### Lemmas about the auxiliary definitions and invariants -/

instance iProto_app_recvs_ne (vs : List V) :
    NonExpansive (iProto_app_recvs (GF := GF) vs) := by
  induction vs with
  | nil => exact ⟨fun _ _ _ h => h⟩
  | cons v vs ih =>
    exact ⟨fun {_ _ _} h => (iProto_message_ne Recv).ne (iMsg_ne v .rfl (ih.ne h))⟩

instance iProto_interp_ne (vsl vsr : List V) :
    NonExpansive₂ (iProto_interp (GF := GF) vsl vsr) where
  ne {_ _ _} h1 {_ _} h2 :=
    exists_ne fun _ => sep_ne.ne (iProto_le_ne.ne .rfl h1) (iProto_le_ne.ne .rfl h2)

@[simp] theorem iProto_app_recvs_nil (p : iProto GF V) : iProto_app_recvs [] p = p := rfl
@[simp] theorem iProto_app_recvs_cons (v : V) (vs : List V) (p : iProto GF V) :
    iProto_app_recvs (v :: vs) p = <?> iMsg_base v iprop(True) (iProto_app_recvs vs p) := rfl

theorem iProto_interp_nil (p : iProto GF V) : ⊢ iProto_interp [] [] p (iProto_dual p) := by
  simp only [iProto_interp, iProto_app_recvs_nil]
  iexists p
  isplitl []
  · iapply iProto_le_refl
  · iapply iProto_le_refl

theorem iProto_interp_sym (vsl vsr : List V) (pl pr : iProto GF V) :
    iProto_interp vsl vsr pl pr ⊢ iProto_interp vsr vsl pr pl := by
  unfold iProto_interp
  iintro ⟨%p, Hp, Hdp⟩
  iexists (iProto_dual p)
  rw [iProto_dual_involutive]
  isplitl [Hdp]
  · iexact Hdp
  · iexact Hp

theorem iProto_interp_le_l (vsl vsr : List V) (pl pl' pr : iProto GF V) :
    iProto_interp vsl vsr pl pr ⊢ iProto_le pl pl' -∗ iProto_interp vsl vsr pl' pr := by
  unfold iProto_interp
  iintro ⟨%p, Hp, Hdp⟩ Hle
  iexists p
  isplitl [Hp Hle]
  · iapply (iProto_le_trans _ pl _) $$ Hp Hle
  · iexact Hdp

theorem iProto_interp_le_r (vsl vsr : List V) (pl pr pr' : iProto GF V) :
    iProto_interp vsl vsr pl pr ⊢ iProto_le pr pr' -∗ iProto_interp vsl vsr pl pr' := by
  iintro H Hle
  iapply iProto_interp_sym
  iapply (iProto_interp_le_l vsr vsl pr pr' pl) $$ [H] Hle
  iapply iProto_interp_sym $$ H

theorem iProto_interp_end_inv (vsl vsr : List V) (pr : iProto GF V) :
    iProto_interp vsl vsr END pr ⊢ ⌜vsr = []⌝ := by
  unfold iProto_interp
  iintro ⟨%p, Hp, _⟩
  cases vsr with
  | nil => ipureintro; rfl
  | cons v vs =>
    isimp only [iProto_app_recvs] at Hp
    ihave Heq := (iProto_le_end_inv_l _) $$ Hp
    iexfalso
    iapply (iProto_message_end_equivI Recv _) $$ Heq

theorem iProto_interp_end_inv' (vsl vsr : List V) (pr : iProto GF V) :
    iProto_interp vsl vsr END pr ⊢ iProto_interp vsl vsr END pr ∗ ⌜vsr = []⌝ :=
  persistent_entails_left (iProto_interp_end_inv vsl vsr pr)

theorem iProto_interp_send_end_inv (vsl vsr : List V) (vl : V) (pl : iProto GF V) :
    iProto_interp vsl vsr (<!> iMsg_base vl iprop(True) pl) END ⊢ False := by
  iintro H
  ihave H := (iProto_interp_sym _ _ _ _) $$ H
  icases (iProto_interp_end_inv' _ _ _) $$ H with ⟨H, %Hv⟩
  subst Hv
  ihave H := (iProto_interp_sym _ _ _ _) $$ H
  unfold iProto_interp
  icases H with ⟨%p, Hp, Hdp⟩
  isimp only [iProto_app_recvs_nil] at Hdp
  ihave Hdp := (iProto_le_dual_l END p) $$ Hdp
  rw [iProto_dual_end]
  ihave Heq := (iProto_le_end_inv_r p) $$ Hdp
  ihave Heq := (internalEq.of_internalEquiv_ne (iProto_app_recvs vsr)) $$ Heq
  irewrite [Heq] at Hp
  cases vsr with
  | nil =>
    isimp only [iProto_app_recvs_nil] at Hp
    ihave Hp := (iProto_le_end_inv_r _) $$ Hp
    iapply (iProto_message_end_equivI Send _) $$ Hp
  | cons v vs =>
    isimp only [iProto_app_recvs_cons] at Hp
    iapply (iProto_le_recv_send_inv _ _) $$ Hp

theorem iProto_interp_recv_end_inv (vsl : List V) (m : iMsg GF V) :
    iProto_interp vsl [] (<?> m) END ⊢ False := by
  iintro H
  ihave H := (iProto_interp_sym _ _ _ _) $$ H
  icases (iProto_interp_end_inv' _ _ _) $$ H with ⟨H, %Hv⟩
  subst Hv
  ihave H := (iProto_interp_sym _ _ _ _) $$ H
  unfold iProto_interp
  icases H with ⟨%p, Hp, Hdp⟩
  isimp only [iProto_app_recvs_nil] at Hdp Hp
  ihave Hdp := (iProto_le_dual_l END p) $$ Hdp
  rw [iProto_dual_end]
  ihave Heq := (iProto_le_end_inv_r p) $$ Hdp
  irewrite [Heq] at Hp
  ihave Hp := (iProto_le_end_inv_r _) $$ Hp
  iapply (iProto_message_end_equivI Recv _) $$ Hp

private theorem iProto_interp_send_aux (vl : V) (pl' p : iProto GF V) :
    ∀ vsl : List V, iProto_le p (<!> iMsg_base vl iprop(True) pl') ⊢
      iProto_le (iProto_app_recvs (vsl ++ [vl]) (iProto_dual pl')) (iProto_app_recvs vsl (iProto_dual p))
  | [] => by
    have h := iProto_le_dual_r (<?> iMsg_base vl iprop(True) (iProto_dual pl')) p
    rw [iProto_dual_message, iMsg_dual_base, iProto_dual_involutive] at h
    exact h
  | vl' :: vsl => by
    simp only [List.cons_append, iProto_app_recvs_cons]
    exact ((iProto_interp_send_aux vl pl' p vsl).trans later_intro).trans (iProto_le_base _ _ _ _ _)

theorem iProto_interp_send (vl : V) (ml : iMsg GF V) (vsl vsr : List V) (pr pl' : iProto GF V) :
    iProto_interp vsl vsr (<!> ml) pr ⊢ ml.car vl (Later.next pl') -∗
      iProto_interp (vsl ++ [vl]) vsr pl' pr := by
  unfold iProto_interp
  iintro ⟨%p, Hp, Hdp⟩ Hml
  ihave Hp := (iProto_le_trans _ (<!> ml) (<!> iMsg_base vl iprop(True) pl')) $$ Hp [Hml]
  · iapply iProto_le_send
    iintro %v' %p' Hb
    isimp only [iMsg_base_car] at Hb
    icases Hb with ⟨%Hv, #Hp', _⟩
    subst Hv
    iexists p'
    isplitl []
    · iapply later_intro
      iapply iProto_le_refl
    · irewrite [← Hp']
      iexact Hml
  cases vsr with
  | nil =>
    isimp only [iProto_app_recvs_nil] at Hp
    iexists pl'
    rw [iProto_app_recvs_nil]
    isplitl []
    · iapply iProto_le_refl
    · iapply (iProto_le_trans _ _ pr) $$ [Hp] Hdp
      iapply (iProto_interp_send_aux vl pl' p vsl) $$ Hp
  | cons vr vsr =>
    isimp only [iProto_app_recvs_cons] at Hp
    iexfalso
    iapply (iProto_le_recv_send_inv _ _) $$ Hp

theorem iProto_interp_recv (vl : V) (vsl vsr : List V) (pl : iProto GF V) (mr : iMsg GF V) :
    iProto_interp (vl :: vsl) vsr pl (<?> mr) ⊢
      ∃ pr, mr.car vl (Later.next pr) ∗ ▷ iProto_interp vsl vsr pl pr := by
  unfold iProto_interp
  iintro ⟨%p, Hp, Hdp⟩
  isimp only [iProto_app_recvs_cons] at Hdp
  icases (iProto_le_recv_recv_inv _ mr vl (iProto_app_recvs vsl (iProto_dual p))) $$ Hdp [] with
    ⟨%pr, Hle, Hm⟩
  · isimp only [iMsg_base_car]
    isplitl []
    · ipureintro; trivial
    · isplitl []
      · istop; exact internalEq.refl
      · ipureintro; trivial
  iexists pr
  isplitl [Hm]
  · iexact Hm
  · inext
    iexists p
    isplitl [Hp]
    · iexact Hp
    · iexact Hle

/-! ### Telescopes -/

theorem iProto_le_trans_emp {a b c : iProto GF V} (h1 : ⊢ iProto_le a b) (h2 : ⊢ iProto_le b c) :
    ⊢ iProto_le a c :=
  h2.trans (wand_entails (h1.trans (iProto_le_trans a b c)))

theorem iMsg_texist_exist {TT : Iris.Std.Tele} (w : V) (lp : Later (iProto GF V))
    (m : TT.Arg → iMsg GF V) :
    (iMsg_texist m).car w lp ⊣⊢ texist fun x => (m x).car w lp := by
  induction TT with
  | nil => exact .rfl
  | cons b ih =>
    rw [texist_cons]
    show (iMsg_exist fun x => iMsg_texist fun xs => m (.cons x xs)).car w lp ⊣⊢ _
    rw [iMsg_exist_car]
    exact exists_congr fun x => ih x _

universe u in
/-- `ULift.up v` as a telescopic function on the empty telescope. Its type is syntactically
`Tele.nil -t> T`, so that type class resolution (at `instances` transparency, which does not
unfold `Tele.Fun`) can assign it to an `outParam` of `MsgTele`. -/
abbrev tele_fun_nil {T : Type _} (v : T) : Iris.Std.Tele.nil.{u} -t> T := ULift.up v

/-- A function into telescopic functions as a telescopic function on `Tele.cons TT` (see
`tele_fun_nil`). -/
abbrev tele_fun_cons {A : Type _} {TT : A → Iris.Std.Tele} {T : Type _}
    (f : (x : A) → (TT x -t> T)) : Iris.Std.Tele.cons TT -t> T := f

universe u in
instance msg_tele_base (v : V) (P : IProp GF) (p : iProto GF V) :
    MsgTele (TT := Iris.Std.Tele.nil.{u}) (iMsg_base v P p) (tele_fun_nil v) (tele_fun_nil P)
      (tele_fun_nil p) := ⟨rfl⟩

instance msg_tele_exist {A : Type _} {TT : A → Iris.Std.Tele} (m : A → iMsg GF V)
    (tv : (x : A) → (TT x -t> V)) (tP : (x : A) → (TT x -t> IProp GF))
    (tp : (x : A) → (TT x -t> iProto GF V))
    [H : ∀ x, MsgTele (TT := TT x) (m x) (tv x) (tP x) (tp x)] :
    MsgTele (TT := .cons TT) (iMsg_exist m) (tele_fun_cons tv) (tele_fun_cons tP)
      (tele_fun_cons tp) where
  msg_tele := by
    show iMsg_exist m = iMsg_exist fun x => iMsg_texist _
    congr 1; funext x; exact (H x).msg_tele

theorem iProto_le_texist_elim_l {TT : Iris.Std.Tele} (m1 : TT.Arg → iMsg GF V) (m2 : iMsg GF V) :
    iprop(∀ x, iProto_le (<?> m1 x) (<?> m2)) ⊢ iProto_le (<?> iMsg_texist m1) (<?> m2) := by
  induction TT with
  | nil => exact forall_elim Iris.Std.Tele.Arg.nil
  | cons b ih =>
    show _ ⊢ iProto_le (<?> iMsg_exist fun x => iMsg_texist fun xs => m1 (.cons x xs)) (<?> m2)
    refine .trans ?_ (iProto_le_exist_elim_l _ m2)
    exact forall_intro fun x => (forall_intro fun xs => forall_elim (.cons x xs)).trans (ih x _)

theorem iProto_le_texist_elim_r {TT : Iris.Std.Tele} (m1 : iMsg GF V) (m2 : TT.Arg → iMsg GF V) :
    iprop(∀ x, iProto_le (<!> m1) (<!> m2 x)) ⊢ iProto_le (<!> m1) (<!> iMsg_texist m2) := by
  induction TT with
  | nil => exact forall_elim Iris.Std.Tele.Arg.nil
  | cons b ih =>
    show _ ⊢ iProto_le (<!> m1) (<!> iMsg_exist fun x => iMsg_texist fun xs => m2 (.cons x xs))
    refine .trans ?_ (iProto_le_exist_elim_r m1 _)
    exact forall_intro fun x => (forall_intro fun xs => forall_elim (.cons x xs)).trans (ih x _)

theorem iProto_le_texist_intro_l {TT : Iris.Std.Tele} (m : TT.Arg → iMsg GF V) (x : TT.Arg) :
    ⊢ iProto_le (<!> iMsg_texist m) (<!> m x) := by
  induction TT with
  | nil => exact iProto_le_refl _
  | cons b ih =>
    obtain ⟨x, xs⟩ := x
    show ⊢ iProto_le (<!> iMsg_exist fun x => iMsg_texist fun xs => m (.cons x xs)) _
    exact iProto_le_trans_emp (iProto_le_exist_intro_l (fun x => iMsg_texist fun xs => m (.cons x xs)) x) (ih x (fun xs => m (.cons x xs)) xs)

theorem iProto_le_texist_intro_r {TT : Iris.Std.Tele} (m : TT.Arg → iMsg GF V) (x : TT.Arg) :
    ⊢ iProto_le (<?> m x) (<?> iMsg_texist m) := by
  induction TT with
  | nil => exact iProto_le_refl _
  | cons b ih =>
    obtain ⟨x, xs⟩ := x
    show ⊢ iProto_le _ (<?> iMsg_exist fun x => iMsg_texist fun xs => m (.cons x xs))
    exact iProto_le_trans_emp (ih x (fun xs => m (.cons x xs)) xs) (iProto_le_exist_intro_r (fun x => iMsg_texist fun xs => m (.cons x xs)) x)

/-! ### Proof mode instances for `⊑` goals -/

instance iProto_le_from_forall_l {A : Type _} (m1 : A → iMsg GF V) (m2 : iMsg GF V) :
    FromForall (iProto_le (<?> iMsg_exist m1) (<?> m2)) (fun x => iProto_le (<?> m1 x) (<?> m2)) :=
  ⟨iProto_le_exist_elim_l m1 m2⟩

instance iProto_le_from_forall_r {A : Type _} (m1 : iMsg GF V) (m2 : A → iMsg GF V) :
    FromForall (iProto_le (<!> m1) (<!> iMsg_exist m2)) (fun x => iProto_le (<!> m1) (<!> m2 x)) :=
  ⟨iProto_le_exist_elim_r m1 m2⟩

instance iProto_le_from_wand_l (io) (m : iMsg GF V) (v : V) (P : IProp GF) (p : iProto GF V) :
    FromWand (iProto_le (<?> iMsg_base v P p) (<?> m)) io P
      (iProto_le (<?> iMsg_base v iprop(True) p) (<?> m)) :=
  ⟨iProto_le_payload_elim_l m v P p⟩

instance iProto_le_from_wand_r (io) (m : iMsg GF V) (v : V) (P : IProp GF) (p : iProto GF V) :
    FromWand (iProto_le (<!> m) (<!> iMsg_base v P p)) io P
      (iProto_le (<!> m) (<!> iMsg_base v iprop(True) p)) :=
  ⟨iProto_le_payload_elim_r m v P p⟩

instance iProto_le_from_exist_l {A : Type _} (m : A → iMsg GF V) (p : iProto GF V) :
    FromExists (iProto_le (<!> iMsg_exist m) p) (fun a => iProto_le (<!> m a) p) where
  from_exists := exists_elim fun x => by
    iintro H
    iapply (iProto_le_trans _ _ _) $$ [] H
    iapply iProto_le_exist_intro_l

instance iProto_le_from_exist_r {A : Type _} (m : A → iMsg GF V) (p : iProto GF V) :
    FromExists (iProto_le p (<?> iMsg_exist m)) (fun a => iProto_le p (<?> m a)) where
  from_exists := exists_elim fun x => by
    iintro H
    iapply (iProto_le_trans _ _ _) $$ H []
    iapply iProto_le_exist_intro_r

instance iProto_le_from_sep_l (m : iMsg GF V) (v : V) (P : IProp GF) (p : iProto GF V) :
    FromSep (iProto_le (<!> iMsg_base v P p) (<!> m)) P
      (iProto_le (<!> iMsg_base v iprop(True) p) (<!> m)) where
  from_sep := by
    iintro ⟨HP, H⟩
    iapply (iProto_le_trans _ _ _) $$ [HP] H
    iapply (iProto_le_payload_intro_l v P p) $$ HP

instance iProto_le_from_sep_r (m : iMsg GF V) (v : V) (P : IProp GF) (p : iProto GF V) :
    FromSep (iProto_le (<?> m) (<?> iMsg_base v P p)) P
      (iProto_le (<?> m) (<?> iMsg_base v iprop(True) p)) where
  from_sep := by
    iintro ⟨HP, H⟩
    iapply (iProto_le_trans _ _ _) $$ H [HP]
    iapply (iProto_le_payload_intro_r v P p) $$ HP

theorem iMsg_tele_car {TT : Iris.Std.Tele} (tv : TT -t> V) (tP : TT -t> IProp GF)
    (tp : TT -t> iProto GF V) (v : V) (p' : Later (iProto GF V)) :
    (iMsg_texist fun x => iMsg_base (Iris.Std.Tele.app tv x) (Iris.Std.Tele.app tP x)
      (Iris.Std.Tele.app tp x)).car v p' ⊣⊢
    ∃ x, ⌜Iris.Std.Tele.app tv x = v⌝ ∗ Later.next (Iris.Std.Tele.app tp x) ≡ p' ∗
      Iris.Std.Tele.app tP x := by
  refine (iMsg_texist_exist v p' _).trans ((texist_exist _).trans ?_)
  simp only [iMsg_base_car]; exact .rfl

theorem iProto_message_equiv {TT1 TT2 : Iris.Std.Tele} (a1 a2 : action) (m1 m2 : iMsg GF V)
    (v1 : TT1 -t> V) (v2 : TT2 -t> V) (P1 : TT1 -t> IProp GF) (P2 : TT2 -t> IProp GF)
    (prot1 : TT1 -t> iProto GF V) (prot2 : TT2 -t> iProto GF V)
    [Hm1 : MsgTele m1 v1 P1 prot1] [Hm2 : MsgTele m2 v2 P2 prot2] :
    ⌜a1 = a2⌝ ⊢
      iprop(■ (∀ xs1, Iris.Std.Tele.app P1 xs1 -∗
        ∃ xs2, ⌜Iris.Std.Tele.app v1 xs1 = Iris.Std.Tele.app v2 xs2⌝ ∗
          ▷ (Iris.Std.Tele.app prot1 xs1 ≡ Iris.Std.Tele.app prot2 xs2) ∗ Iris.Std.Tele.app P2 xs2)) -∗
      iprop(■ (∀ xs2, Iris.Std.Tele.app P2 xs2 -∗
        ∃ xs1, ⌜Iris.Std.Tele.app v1 xs1 = Iris.Std.Tele.app v2 xs2⌝ ∗
          ▷ (Iris.Std.Tele.app prot1 xs1 ≡ Iris.Std.Tele.app prot2 xs2) ∗ Iris.Std.Tele.app P1 xs1)) -∗
      iProto_message a1 m1 ≡ iProto_message a2 m2 := by
  rw [Hm1.msg_tele, Hm2.msg_tele]
  iintro %Ha #H1 #H2
  iapply (iProto_message_equivI a1 a2 _ _).2
  isplit
  · ipureintro; exact Ha
  iintro %v %p'
  iapply (prop_ext _ _).2
  imodintro
  isplit
  · iintro H
    icases (iMsg_tele_car v1 P1 prot1 v p').1 $$ H with ⟨%xs1, %Hv1, #Hp1, HP1⟩
    icases H1 $$ %xs1 HP1 with ⟨%xs2, %Hv2, #Hp2, HP2⟩
    iapply (iMsg_tele_car v2 P2 prot2 v p').2
    iexists xs2
    isplitl []
    · ipureintro; rw [← Hv2, Hv1]
    isplitl []
    · irewrite [← Hp1]
      ihave Hp2 := (later_equivI_mpr _ _) $$ Hp2
      iapply internalEq.symm $$ Hp2
    · iexact HP2
  · iintro H
    icases (iMsg_tele_car v2 P2 prot2 v p').1 $$ H with ⟨%xs2, %Hv2, #Hp2, HP2⟩
    icases H2 $$ %xs2 HP2 with ⟨%xs1, %Hv1, #Hp1, HP1⟩
    iapply (iMsg_tele_car v1 P1 prot1 v p').2
    iexists xs1
    isplitl []
    · ipureintro; rw [Hv1, Hv2]
    isplitl []
    · irewrite [← Hp2]
      iapply (later_equivI_mpr _ _) $$ Hp1
    · iexact HP1

instance iProto_le_frame_l (q : Bool) (m : iMsg GF V) (v : V) (R P Q : IProp GF) (p : iProto GF V)
    [HP : Frame q R P Q] :
    Frame q R (iProto_le (<!> iMsg_base v P p) (<!> m)) (iProto_le (<!> iMsg_base v Q p) (<!> m)) where
  frame := by
    iintro ⟨HR, H⟩
    iapply (iProto_le_trans _ _ _) $$ [HR] H
    iapply iProto_le_payload_elim_r
    iintro HQ
    iapply iProto_le_payload_intro_l
    iapply HP.frame
    isplitl [HR]
    · iexact HR
    · iexact HQ

instance iProto_le_frame_r (q : Bool) (m : iMsg GF V) (v : V) (R P Q : IProp GF) (p : iProto GF V)
    [HP : Frame q R P Q] :
    Frame q R (iProto_le (<?> m) (<?> iMsg_base v P p)) (iProto_le (<?> m) (<?> iMsg_base v Q p)) where
  frame := by
    iintro ⟨HR, H⟩
    iapply (iProto_le_trans _ _ _) $$ H [HR]
    iapply iProto_le_payload_elim_l
    iintro HQ
    iapply iProto_le_payload_intro_r
    iapply HP.frame
    isplitl [HR]
    · iexact HR
    · iexact HQ

instance iProto_le_from_modal (io) (a : action) (v : V) (p1 p2 : iProto GF V) :
    FromModal io (modality_laterN 1) True iprop(▷^[1] iProto_le p1 p2)
      (iProto_le (iProto_message a (iMsg_base v iprop(True) p1))
        (iProto_message a (iMsg_base v iprop(True) p2)))
      (iProto_le p1 p2) where
  from_modal _ := iProto_le_base a v iprop(True) p1 p2

end proofs

/-! ## Encoding protocols over `Pos` (for ghost state) -/

section enc
variable {GF : BundledGFunctors} {V : Type} [Pos.Countable V]

/-- Re-index a message along `decode` (with `False` outside the image of `encode`). -/
def iProto_enc_msg (d : iProto GF Pos -n> iProto GF V)
    (m : V → (Later (iProto GF V) -n> IProp GF)) (v' : Pos) : Later (iProto GF Pos) -n> IProp GF :=
  match (Pos.Countable.decode v' : Option V) with
  | some v => (m v).comp (laterMap d)
  | none => Hom.const iprop(False)

theorem iProto_enc_msg_ne {n} (d1 d2 : iProto GF Pos -n> iProto GF V)
    (m1 m2 : V → (Later (iProto GF V) -n> IProp GF))
    (hd : DistLater n d1 d2) (hm : ∀ v, m1 v ≡{n}≡ m2 v) (v' : Pos) :
    iProto_enc_msg d1 m1 v' ≡{n}≡ iProto_enc_msg d2 m2 v' := by
  unfold iProto_enc_msg
  split
  · exact fun x => (hm _ _).trans ((m2 _).ne.ne (laterMap_contractive.distLater_dist hd x))
  · exact .rfl

/-- The pair (encode, decode) of protocol re-indexing maps. -/
abbrev EncDec (GF : BundledGFunctors) (V : Type) : Type :=
  (iProto GF V -n> iProto GF Pos) × (iProto GF Pos -n> iProto GF V)

def iProto_encdec_aux (r : EncDec GF V) : EncDec GF V :=
  (⟨fun p => proto_elim proto_end (fun a m => proto_message a (iProto_enc_msg r.2 m)) p,
    ⟨fun {_ p1 p2} h => proto_elim_ne _ _ _ p1 p2
      (fun a m1 m2 hm => proto_message_ne a (iProto_enc_msg_ne _ _ m1 m2 .rfl hm)) h⟩⟩,
   ⟨fun p => proto_elim proto_end
      (fun a m => proto_message a (fun v => (m (Pos.Countable.encode v)).comp (laterMap r.1))) p,
    ⟨fun {_ p1 p2} h => proto_elim_ne _ _ _ p1 p2
      (fun a m1 m2 hm => proto_message_ne a fun v x => hm _ _) h⟩⟩)

instance iProto_encdec_aux_contractive : Contractive (iProto_encdec_aux (GF := GF) (V := V)) where
  distLater_dist {_ r1 r2} h :=
    ⟨fun p => proto_elim_ne proto_end
      (fun a m => proto_message a (iProto_enc_msg r1.2 m))
      (fun a m => proto_message a (iProto_enc_msg r2.2 m)) p p
      (fun a m1 m2 hm => proto_message_ne a
        (iProto_enc_msg_ne _ _ m1 m2 (fun k hk => (h k hk).2) hm)) .rfl,
     fun p => proto_elim_ne proto_end
      (fun a m => proto_message a (fun v => (m (Pos.Countable.encode v)).comp (laterMap r1.1)))
      (fun a m => proto_message a (fun v => (m (Pos.Countable.encode v)).comp (laterMap r2.1))) p p
      (fun a m1 m2 hm => proto_message_ne a fun v x =>
        (hm _ _).trans ((m2 _).ne.ne
          (laterMap_contractive.distLater_dist (fun k hk => (h k hk).1) x))) .rfl⟩

def iProto_encdec : EncDec GF V := fixpoint iProto_encdec_aux

/-- `iProto_enc : iProto GF V -n> iProto GF Pos`. -/
def iProto_enc : iProto GF V -n> iProto GF Pos := (iProto_encdec (GF := GF) (V := V)).1
/-- `iProto_dec : iProto GF Pos -n> iProto GF V`, a retraction of `iProto_enc`. -/
def iProto_dec : iProto GF Pos -n> iProto GF V := (iProto_encdec (GF := GF) (V := V)).2

theorem iProto_encdec_unfold :
    iProto_encdec (GF := GF) (V := V) = iProto_encdec_aux iProto_encdec :=
  fixpoint_unfold iProto_encdec_aux.toContractiveHom

theorem iProto_enc_message (a : action) (m : V → (Later (iProto GF V) -n> IProp GF)) :
    iProto_enc (proto_message a m) = proto_message a (iProto_enc_msg iProto_dec m) := by
  unfold iProto_enc iProto_dec
  exact (congrArg (fun r : EncDec GF V => r.1 (proto_message a m)) iProto_encdec_unfold).trans
    (proto_elim_message proto_end
      (fun a m => proto_message a (iProto_enc_msg (iProto_encdec (GF := GF) (V := V)).2 m)) a m)

theorem iProto_dec_message (a : action) (m : Pos → (Later (iProto GF Pos) -n> IProp GF)) :
    iProto_dec (V := V) (proto_message a m) =
      proto_message a (fun v => (m (Pos.Countable.encode v)).comp (laterMap iProto_enc)) := by
  unfold iProto_enc iProto_dec
  exact (congrArg (fun r : EncDec GF V => r.2 (proto_message a m)) iProto_encdec_unfold).trans
    (proto_elim_message proto_end (fun a m => proto_message a
      (fun v => (m (Pos.Countable.encode v)).comp (laterMap (iProto_encdec (GF := GF) (V := V)).1))) a m)

theorem iProto_enc_end : iProto_enc (GF := GF) (V := V) proto_end = proto_end := by
  unfold iProto_enc; rw [iProto_encdec_unfold]; rfl

theorem iProto_dec_end : iProto_dec (GF := GF) (V := V) proto_end = proto_end := by
  unfold iProto_dec; rw [iProto_encdec_unfold]; rfl

private theorem iProto_dec_enc_dist (n : Nat) :
    ∀ p : iProto GF V, iProto_dec (iProto_enc p) ≡{n}≡ p := by
  induction n using Nat.strongRecOn with
  | _ n IH =>
  intro p
  rcases proto_case p with rfl | ⟨a, m, rfl⟩
  · rw [iProto_enc_end, iProto_dec_end]
  · rw [iProto_enc_message, iProto_dec_message]
    refine proto_message_ne a fun v x => ?_
    simp only [iProto_enc_msg, Pos.Countable.decode_encode, Hom.comp_apply]
    exact (m v).ne.ne fun k hk => IH k hk x.car

theorem iProto_dec_enc (p : iProto GF V) : iProto_dec (iProto_enc p) = p :=
  OFE.eq_dist_2 fun n => iProto_dec_enc_dist n p

end enc

/-! ## Ghost state -/

section ghost
open ProofMode ExclAuth
variable {GF : BundledGFunctors} [allG GF] {V : Type} [Pos.Countable V]

/-- Rocq `protoG Σ V`: with the universal `allG` camera no further assumption is needed. -/
abbrev protoG (GF : BundledGFunctors) := allG GF

def iProto_own_frag (γ : GName) (p : iProto GF V) : IProp GF :=
  own γ (◯E (Later.next (iProto_enc p)) : ExclAuthR (A := Later (iProto GF Pos)))

def iProto_own_auth (γ : GName) (p : iProto GF V) : IProp GF :=
  own γ (●E (Later.next (iProto_enc p)) : ExclAuthR (A := Later (iProto GF Pos)))

/-- Rocq `iProto_ctx`: the two endpoints' authoritative protocols, with the in-flight
messages `vsl` (left to right) and `vsr` (right to left). -/
def iProto_ctx (γl γr : GName) (vsl vsr : List V) : IProp GF :=
  iprop(∃ pl pr, iProto_own_auth γl pl ∗ iProto_own_auth γr pr ∗ ▷ iProto_interp vsl vsr pl pr)

/-- The connective for ownership of channel ends. -/
def iProto_own (γ : GName) (p : iProto GF V) : IProp GF :=
  iprop(∃ p', ▷ iProto_le p' p ∗ iProto_own_frag γ p')

instance iProto_own_contractive (γ : GName) : Contractive (iProto_own (GF := GF) (V := V) γ) where
  distLater_dist h := exists_ne fun _ =>
    sep_ne.ne (Contractive.distLater_dist (f := BIBase.later)
      (fun k hk => iProto_le_ne.ne .rfl (h k hk))) .rfl

instance iProto_own_ne (γ : GName) : NonExpansive (iProto_own (GF := GF) (V := V) γ) :=
  inferInstance

instance iProto_own_frag_ne (γ : GName) : NonExpansive (iProto_own_frag (GF := GF) (V := V) γ) where
  ne {_ _ _} h := (own_ne γ).ne (Auth.frag_ne.ne (fun _ hk => iProto_enc.ne.ne (h.lt hk)))

private theorem excl_auth_agreeI {A : Type _} [OFE A] (a b : A) :
    (✓ ((●E a : ExclAuthR (A := A)) • ◯E b) : IProp GF) ⊢ a ≡ b := by
  sbi_unfold; intro n; exact ExclAuth.agreeN

private theorem excl_auth_frag_op_validI {A : Type _} [OFE A] (a b : A) :
    (✓ ((◯E a : ExclAuthR (A := A)) • ◯E b) : IProp GF) ⊢ False := by
  sbi_unfold; intro n h; exact (ExclAuth.frag_op_validN.mp h).elim

theorem own_prot_excl (γ : GName) (p1 p2 : iProto GF V) :
    iProto_own_frag γ p1 ⊢ iProto_own_frag γ p2 -∗ False := by
  unfold iProto_own_frag
  iintro H1 H2
  iapply (excl_auth_frag_op_validI (GF := GF) _ _)
  iapply (own_valid_2 γ _ _) $$ H1 H2

theorem iProto_own_excl (γ : GName) (p1 p2 : iProto GF V) :
    iProto_own γ p1 ⊢ iProto_own γ p2 -∗ False := by
  unfold iProto_own
  iintro ⟨%p1', _, H1⟩ ⟨%p2', _, H2⟩
  iapply (own_prot_excl γ p1' p2') $$ H1 H2

theorem iProto_own_auth_agree (γ : GName) (p p' : iProto GF V) :
    iProto_own_auth γ p ⊢ iProto_own_frag γ p' -∗ ▷ (p ≡ p') := by
  unfold iProto_own_auth iProto_own_frag
  iintro Ha Hf
  ihave H := (own_valid_2 γ _ _) $$ Ha Hf
  ihave H := (excl_auth_agreeI (GF := GF) _ _) $$ H
  ihave H := (later_equivI_mp _ _) $$ H
  inext
  ihave H := (internalEq.of_internalEquiv_ne iProto_dec) $$ H
  rw [iProto_dec_enc, iProto_dec_enc]
  iexact H

theorem iProto_own_auth_update (γ : GName) (p p' p'' : iProto GF V) :
    iProto_own_auth γ p ⊢ iProto_own_frag γ p' ==∗
      iProto_own_auth γ p'' ∗ iProto_own_frag γ p'' := by
  unfold iProto_own_auth iProto_own_frag
  iintro Ha Hf
  imod (own_update_2 γ _ _ _ ExclAuth.update) $$ Ha Hf with H
  imodintro
  iapply (own_op γ _ _).1 $$ H

theorem iProto_send_end_inv_r (γl γr : GName) (vsl vsr : List V) (vr : V) (pr : iProto GF V) :
    iProto_ctx γl γr vsl vsr ⊢ iProto_own γl (END : iProto GF V) -∗
      iProto_own γr (<!> iMsg_base vr iprop(True) pr) -∗ ▷ False := by
  unfold iProto_ctx iProto_own
  iintro ⟨%pl', %pr', Hal, Har, Hinterp⟩ ⟨%pl'', Hlel, Hfl⟩ ⟨%pr'', Hler, Hfr⟩
  ihave #Hpl := (iProto_own_auth_agree γl pl' pl'') $$ Hal Hfl
  ihave #Hpr := (iProto_own_auth_agree γr pr' pr'') $$ Har Hfr
  inext
  irewrite [← Hpl] at Hlel
  irewrite [← Hpr] at Hler
  ihave Hinterp := (iProto_interp_le_l _ _ _ _ _) $$ Hinterp Hlel
  ihave Hinterp := (iProto_interp_le_r _ _ _ _ _) $$ Hinterp Hler
  ihave Hinterp := (iProto_interp_sym _ _ _ _) $$ Hinterp
  iapply (iProto_interp_send_end_inv _ _ _ _) $$ Hinterp

theorem iProto_recv_end_inv_l (γl γr : GName) (vsl : List V) (m : iMsg GF V) :
    iProto_ctx γl γr vsl [] ⊢ iProto_own γl (<?> m) -∗ iProto_own γr (END : iProto GF V) -∗ ▷ False := by
  unfold iProto_ctx iProto_own
  iintro ⟨%pl', %pr', Hal, Har, Hinterp⟩ ⟨%pl'', Hlel, Hfl⟩ ⟨%pr'', Hler, Hfr⟩
  ihave #Hpl := (iProto_own_auth_agree γl pl' pl'') $$ Hal Hfl
  ihave #Hpr := (iProto_own_auth_agree γr pr' pr'') $$ Har Hfr
  inext
  irewrite [← Hpl] at Hlel
  irewrite [← Hpr] at Hler
  ihave Hinterp := (iProto_interp_le_l _ _ _ _ _) $$ Hinterp Hlel
  ihave Hinterp := (iProto_interp_le_r _ _ _ _ _) $$ Hinterp Hler
  iapply (iProto_interp_recv_end_inv _ _) $$ Hinterp

theorem iProto_end_inv_l (γl γr : GName) (vsl vsr : List V) :
    iProto_ctx γl γr vsl vsr ⊢ iProto_own γl (END : iProto GF V) -∗ ▷ ⌜vsr = []⌝ := by
  unfold iProto_ctx iProto_own
  iintro ⟨%pl', %pr', Hal, _, Hinterp⟩ ⟨%pl'', Hle, Hf⟩
  ihave #Hpl := (iProto_own_auth_agree γl pl' pl'') $$ Hal Hf
  inext
  irewrite [← Hpl] at Hle
  ihave Hinterp := (iProto_interp_le_l _ _ _ _ _) $$ Hinterp Hle
  iapply (iProto_interp_end_inv _ _ _) $$ Hinterp

theorem iProto_end_inv_r (γl γr : GName) (vsl vsr : List V) :
    iProto_ctx γl γr vsl vsr ⊢ iProto_own γr (END : iProto GF V) -∗ ▷ ⌜vsl = []⌝ := by
  unfold iProto_ctx iProto_own
  iintro ⟨%pl', %pr', _, Har, Hinterp⟩ ⟨%pr'', Hle, Hf⟩
  ihave #Hpr := (iProto_own_auth_agree γr pr' pr'') $$ Har Hf
  inext
  irewrite [← Hpr] at Hle
  ihave Hinterp := (iProto_interp_le_r _ _ _ _ _) $$ Hinterp Hle
  ihave Hinterp := (iProto_interp_sym _ _ _ _) $$ Hinterp
  iapply (iProto_interp_end_inv _ _ _) $$ Hinterp

theorem iProto_ctx_sym (γl γr : GName) (vsl vsr : List V) :
    iProto_ctx (GF := GF) γl γr vsl vsr ⊢ iProto_ctx γr γl vsr vsl := by
  unfold iProto_ctx
  iintro ⟨%pl, %pr, Hal, Har, Hinterp⟩
  iexists pr, pl
  isplitl [Har]
  · iexact Har
  isplitl [Hal]
  · iexact Hal
  inext
  iapply (iProto_interp_sym _ _ _ _) $$ Hinterp

theorem iProto_own_le (γ : GName) (p1 p2 : iProto GF V) :
    iProto_own γ p1 ⊢ ▷ iProto_le p1 p2 -∗ iProto_own γ p2 := by
  unfold iProto_own
  iintro ⟨%p1', Hle, H⟩ Hle'
  iexists p1'
  isplitl [Hle Hle']
  · inext
    iapply (iProto_le_trans _ _ _) $$ Hle Hle'
  · iexact H

theorem iProto_init (p : iProto GF V) :
    ⊢ |==> ∃ γl γr, iProto_ctx (GF := GF) (V := V) γl γr [] [] ∗ iProto_own γl p ∗
      iProto_own γr (iProto_dual p) := by
  unfold iProto_ctx iProto_own iProto_own_auth iProto_own_frag
  imod (own_alloc ((●E (Later.next (iProto_enc p)) : ExclAuthR (A := Later (iProto GF Pos))) •
    ◯E (Later.next (iProto_enc p))) ExclAuth.valid) with Hl
  imod (own_alloc ((●E (Later.next (iProto_enc (iProto_dual p))) : ExclAuthR (A := Later (iProto GF Pos))) •
    ◯E (Later.next (iProto_enc (iProto_dual p)))) ExclAuth.valid) with Hr
  icases Hl with ⟨%γl, Hl⟩
  icases Hr with ⟨%γr, Hr⟩
  icases (own_op γl _ _).1 $$ Hl with ⟨Hal, Hfl⟩
  icases (own_op γr _ _).1 $$ Hr with ⟨Har, Hfr⟩
  imodintro
  iexists γl, γr
  isplitl [Hal Har]
  · iexists p, (iProto_dual p)
    isplitl [Hal]
    · iexact Hal
    isplitl [Har]
    · iexact Har
    · iapply later_intro
      iapply iProto_interp_nil
  isplitl [Hfl]
  · iexists p
    isplitl []
    · iapply later_intro
      iapply iProto_le_refl
    · iexact Hfl
  · iexists (iProto_dual p)
    isplitl []
    · iapply later_intro
      iapply iProto_le_refl
    · iexact Hfr

theorem iProto_own_auth_agree' (γ : GName) (p p' : iProto GF V) :
    iProto_own_auth γ p ∗ iProto_own_frag γ p' ⊢
      (iProto_own_auth γ p ∗ iProto_own_frag γ p') ∗ ▷ (p ≡ p') :=
  persistent_entails_left ((sep_mono_left (iProto_own_auth_agree γ p p')).trans wand_elim_left)

theorem iProto_send (γl γr : GName) (m : iMsg GF V) (vsr vsl : List V) (vl : V) (p : iProto GF V) :
    iProto_ctx γl γr vsl vsr ⊢ iProto_own γl (<!> m) -∗ m.car vl (Later.next p) ==∗
      iProto_ctx γl γr (vsl ++ [vl]) vsr ∗ iProto_own γl p := by
  unfold iProto_ctx iProto_own
  iintro ⟨%pl, %pr, Hal, Har, Hinterp⟩ ⟨%pl', Hle, Hf⟩ Hm
  icases (iProto_own_auth_agree' γl pl pl') $$ [Hal Hf] with ⟨⟨Hal, Hf⟩, #Hp⟩
  · isplitl [Hal]
    · iexact Hal
    · iexact Hf
  ihave Hinterp : iprop(▷ iProto_interp (vsl ++ [vl]) vsr p pr) $$ [Hinterp Hle Hm]
  · inext
    irewrite [← Hp] at Hle
    ihave H := (iProto_interp_le_l _ _ _ _ _) $$ Hinterp Hle
    iapply (iProto_interp_send _ _ _ _ _ _) $$ H Hm
  imod (iProto_own_auth_update γl pl pl' p) $$ Hal Hf with ⟨Hal, Hf⟩
  imodintro
  isplitl [Hal Har Hinterp]
  · iexists p, pr
    isplitl [Hal]
    · iexact Hal
    isplitl [Har]
    · iexact Har
    · iexact Hinterp
  · iexists p
    isplitl []
    · iapply later_intro
      iapply iProto_le_refl
    · iexact Hf

theorem iProto_recv (γl γr : GName) (m : iMsg GF V) (vr : V) (vsr vsl : List V) :
    iProto_ctx γl γr vsl (vr :: vsr) ⊢ iProto_own γl (<?> m) ==∗
      ▷ ∃ p, iProto_ctx γl γr vsl vsr ∗ iProto_own γl p ∗ m.car vr (Later.next p) := by
  unfold iProto_ctx iProto_own
  iintro ⟨%pl, %pr, Hal, Har, Hinterp⟩ ⟨%p, Hle, Hf⟩
  icases (iProto_own_auth_agree' γl pl p) $$ [Hal Hf] with ⟨⟨Hal, Hf⟩, #Hp⟩
  · isplitl [Hal]
    · iexact Hal
    · iexact Hf
  ihave Hinterp : iprop(▷ ∃ q, m.car vr (Later.next q) ∗ ▷ iProto_interp vsr vsl pr q)
    $$ [Hinterp Hle]
  · inext
    irewrite [← Hp] at Hle
    ihave H := (iProto_interp_le_l _ _ _ _ _) $$ Hinterp Hle
    ihave H := (iProto_interp_sym _ _ _ _) $$ H
    iapply (iProto_interp_recv _ _ _ _ _) $$ H
  icases (later_exists).2 $$ Hinterp with ⟨%q, Hinterp⟩
  imod (iProto_own_auth_update γl pl p q) $$ Hal Hf with ⟨Hal, Hf⟩
  imodintro
  inext
  icases Hinterp with ⟨Hm, Hinterp⟩
  iexists q
  isplitl [Hal Har Hinterp]
  · iexists q, pr
    isplitl [Hal]
    · iexact Hal
    isplitl [Har]
    · iexact Har
    · inext
      iapply (iProto_interp_sym _ _ _ _) $$ Hinterp
  isplitl [Hf]
  · iexists q
    isplitl []
    · iapply later_intro
      iapply iProto_le_refl
    · iexact Hf
  · iexact Hm

end ghost

end Perennial
