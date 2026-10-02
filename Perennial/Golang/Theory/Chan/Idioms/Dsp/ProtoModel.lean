import Perennial.Golang.Theory.Chan.Idioms.Dsp.CofeSolver2

/-!
Port of `new/golang/theory/chan/idioms/dsp/proto_model.v` (from Actris).

The model of dependent separation protocols as the solution of the recursive domain
equation
  `proto = 1 + (action * (V → ▶ proto → PROP))`
with constructors `proto_end`, `proto_message`, the eliminator `proto_elim`, and the
functorial action `proto_map` (giving the functor `protoOF`).

Important: this file should not be used directly; use the wrappers in `DspGhostTheory`.

Lean notes: iris-lean's OFE equivalence is Leibniz equality, so `≡` lemmas of the Rocq
development are stated with `=`; in particular `proto_case` and `proto_elim_message` hold
up to `=` (the latter needs no properness assumption any more).
-/

set_option autoImplicit false

namespace Perennial
open Iris OFE COFE

/-! ## Actions -/

inductive action where
  | Send | Recv
  deriving DecidableEq, Inhabited

export action (Send Recv)

instance action_inhabited : Inhabited action := ⟨Send⟩

def action_dual (a : action) : action :=
  match a with | Send => Recv | Recv => Send

@[simp] theorem action_dual_involutive (a : action) : action_dual (action_dual a) = a := by
  cases a <;> rfl

/-- Rocq `actionO := leibnizO action`. -/
instance actionO : COFE action := COFE.ofDiscrete action
instance : OFE.Discrete action := ⟨id⟩
instance (a : action) : OFE.DiscreteE a := ⟨id⟩

/-! ## The recursive domain equation -/

/-- Rocq `proto_auxOF V PROP = optionOF (actionO * (V -d> ▶ ∙ -n> PROP))`. -/
abbrev proto_auxOF (V : Type) (PROP : Type) [COFE PROP] : OFunctorPre :=
  fun A _ _ _ => Option (action × (V → (Later A -n> PROP)))

def proto_auxOF_map {V : Type} {PROP : Type} [COFE PROP] {A1 A2 : Type} [OFE A1] [OFE A2]
    (f : A2 -n> A1) : Option (action × (V → (Later A1 -n> PROP))) -n>
      Option (action × (V → (Later A2 -n> PROP))) where
  f x := x.map fun am => (am.1, fun v => (am.2 v).comp (laterMap f))
  ne.ne {n} x y h := by
    rcases x with _ | ⟨a1, m1⟩ <;> rcases y with _ | ⟨a2, m2⟩
    · exact .rfl
    · exact h.elim
    · exact h.elim
    · exact ⟨h.1, fun v z => h.2 v _⟩

instance proto_auxOF_ofunctor (V : Type) (PROP : Type) [COFE PROP] :
    OFunctorContractive (proto_auxOF V PROP) where
  ofe := inferInstance
  map f _ := proto_auxOF_map f
  map_ne.ne {n} f1 f2 hf _ _ _ x := by
    rcases x with _ | ⟨a, m⟩
    · exact .rfl
    · exact ⟨rfl, fun v z => (m v).ne.ne (fun k hk => (hf _).lt hk)⟩
  map_id x := by
    rcases x with _ | ⟨a, m⟩
    · rfl
    · rfl
  map_comp f g _ _ x := by
    rcases x with _ | ⟨a, m⟩
    · rfl
    · rfl
  map_contractive := ⟨fun {n} {fg1 fg2} h x => by
    rcases x with _ | ⟨a, m⟩
    · exact .rfl
    · exact ⟨rfl, fun v z => (m v).ne.ne (fun k hk => (h k hk).1 _)⟩⟩

/-- Rocq `pre_proto`. -/
abbrev pre_proto (V : Type) (PROPn : Type) [COFE PROPn] (PROP : Type) [COFE PROP] : Type :=
  cofe_solver_2.T (proto_auxOF V) PROPn PROP

/-- Rocq `proto V PROPn PROP`. -/
abbrev proto (V : Type) (PROPn : Type) [COFE PROPn] (PROP : Type) [COFE PROP] : Type :=
  Option (action × (V → (Later (pre_proto V PROP PROPn) -n> PROP)))

section
variable {V : Type} {PROPn : Type} [COFE PROPn] {PROP : Type} [COFE PROP]

instance proto_cofe : COFE (proto V PROPn PROP) := inferInstance

def proto_iso : OFE.Iso (proto V PROPn PROP) (pre_proto V PROPn PROP) :=
  cofe_solver_2.result_2 (proto_auxOF V) PROPn PROP

def proto_fold : pre_proto V PROPn PROP -n> proto V PROPn PROP := proto_iso.inv
def proto_unfold : proto V PROPn PROP -n> pre_proto V PROPn PROP := proto_iso.hom

@[simp] theorem proto_fold_unfold (p : proto V PROPn PROP) : proto_fold (proto_unfold p) = p :=
  proto_iso.inv_hom
@[simp] theorem proto_unfold_fold (p : pre_proto V PROPn PROP) : proto_unfold (proto_fold p) = p :=
  proto_iso.hom_inv

def proto_end : proto V PROPn PROP := none

def proto_message (a : action) (m : V → (Later (proto V PROP PROPn) -n> PROP)) :
    proto V PROPn PROP :=
  some (a, fun v => (m v).comp (laterMap proto_fold))

theorem proto_message_ne (a : action) {n} {m1 m2 : V → (Later (proto V PROP PROPn) -n> PROP)}
    (Hm : ∀ v, m1 v ≡{n}≡ m2 v) :
    proto_message (PROPn := PROPn) a m1 ≡{n}≡ proto_message a m2 :=
  ⟨rfl, fun v x => Hm v _⟩

instance proto_message_ne' (a : action) :
    NonExpansive (proto_message (V := V) (PROPn := PROPn) (PROP := PROP) a) :=
  ⟨fun _ _ _ h => proto_message_ne a h⟩

theorem proto_laterMap_fold_unfold (p : Later (proto V PROPn PROP)) :
    laterMap proto_fold (laterMap proto_unfold p) = p := by
  obtain ⟨p⟩ := p; simp [laterMap]

theorem proto_laterMap_unfold_fold (p : Later (pre_proto V PROPn PROP)) :
    laterMap proto_unfold (laterMap proto_fold p) = p := by
  obtain ⟨p⟩ := p; simp [laterMap]

theorem proto_case (p : proto V PROPn PROP) :
    p = proto_end ∨ ∃ a m, p = proto_message a m := by
  rcases p with _ | ⟨a, m⟩
  · exact .inl rfl
  · refine .inr ⟨a, fun v => (m v).comp (laterMap proto_unfold), ?_⟩
    simp only [proto_message]
    congr; funext v; ext x
    simp [proto_laterMap_unfold_fold]

instance proto_inhabited : Inhabited (proto V PROPn PROP) := ⟨proto_end⟩

def proto_elim {A : Type _} (x : A)
    (f : action → (V → (Later (proto V PROP PROPn) -n> PROP)) → A)
    (p : proto V PROPn PROP) : A :=
  match p with
  | none => x
  | some (a, m) => f a (fun v => (m v).comp (laterMap proto_unfold))

theorem proto_elim_ne {A : Type _} [OFE A] (x : A)
    (f1 f2 : action → (V → (Later (proto V PROP PROPn) -n> PROP)) → A)
    (p1 p2 : proto V PROPn PROP) {n}
    (Hf : ∀ a m1 m2, (∀ v, m1 v ≡{n}≡ m2 v) → f1 a m1 ≡{n}≡ f2 a m2)
    (Hp : p1 ≡{n}≡ p2) :
    proto_elim x f1 p1 ≡{n}≡ proto_elim x f2 p2 := by
  rcases p1 with _ | ⟨a1, m1⟩ <;> rcases p2 with _ | ⟨a2, m2⟩
  · exact .rfl
  · exact Hp.elim
  · exact Hp.elim
  · obtain ⟨ha, hm⟩ := Hp
    cases (ha : a1 = a2)
    exact Hf a1 _ _ fun v x => hm v _

@[simp] theorem proto_elim_end {A : Type _} (x : A)
    (f : action → (V → (Later (proto V PROP PROPn) -n> PROP)) → A) :
    proto_elim x f (proto_end : proto V PROPn PROP) = x := rfl

@[simp] theorem proto_elim_message {A : Type _} (x : A)
    (f : action → (V → (Later (proto V PROP PROPn) -n> PROP)) → A) a m :
    proto_elim x f (proto_message (PROPn := PROPn) a m) = f a m := by
  simp only [proto_elim, proto_message]
  congr; funext v; ext p
  simp [proto_laterMap_fold_unfold]

end

section equivI
open BI

variable {SPROP : Type _} [Sbi SPROP]
variable {V : Type} {PROPn : Type} [COFE PROPn] {PROP : Type} [COFE PROP]

private def proto_action (p : proto V PROPn PROP) : action :=
  match p with | none => Send | some (a, _) => a

private instance proto_action_ne : NonExpansive (proto_action (V := V) (PROPn := PROPn) (PROP := PROP)) where
  ne {n} p1 p2 h := by
    rcases p1 with _ | ⟨a1, m1⟩ <;> rcases p2 with _ | ⟨a2, m2⟩
    · rfl
    · exact h.elim
    · exact h.elim
    · exact h.1

private def proto_payload (d : PROP) (v : V) (p' : Later (proto V PROP PROPn))
    (p : proto V PROPn PROP) : PROP :=
  match p with | none => d | some (_, m) => m v (laterMap proto_unfold p')

private instance proto_payload_ne (d : PROP) (v : V) (p' : Later (proto V PROP PROPn)) :
    NonExpansive (proto_payload (PROPn := PROPn) d v p') where
  ne {n} p1 p2 h := by
    rcases p1 with _ | ⟨a1, m1⟩ <;> rcases p2 with _ | ⟨a2, m2⟩
    · exact .rfl
    · exact h.elim
    · exact h.elim
    · exact h.2 v _

theorem proto_message_equivI (a1 a2 : action) (m1 m2 : V → (Later (proto V PROP PROPn) -n> PROP)) :
    (iprop(proto_message (PROPn := PROPn) a1 m1 ≡ proto_message a2 m2) : SPROP) ⊣⊢
      iprop(⌜a1 = a2⌝ ∧ ∀ v p', m1 v p' ≡ m2 v p') := by
  constructor
  · refine and_intro ?_ (forall_intro fun v => forall_intro fun p' => ?_)
    · exact (internalEq.of_internalEquiv_ne proto_action).trans discrete_eq_mp
    · have := internalEq.of_internalEquiv_ne (PROP := SPROP)
        (proto_payload (PROPn := PROPn) (m1 v p') v p')
        (x := proto_message a1 m1) (y := proto_message a2 m2)
      simpa [proto_payload, proto_message, proto_laterMap_fold_unfold] using this
  · refine pure_elim_left fun h => ?_
    subst h
    refine (forall_mono fun v => (ofeMorO_equivI (m1 v) (m2 v)).2).trans ?_
    refine fun_extI.trans ?_
    exact internalEq.of_internalEquiv_ne (proto_message a1)

theorem proto_message_end_equivI (a : action) (m : V → (Later (proto V PROP PROPn) -n> PROP)) :
    (iprop(proto_message (PROPn := PROPn) a m ≡ proto_end) : SPROP) ⊢ False := by
  let Ψ : proto V PROPn PROP → SPROP := fun p => iprop(⌜p.isSome⌝)
  haveI : NonExpansive Ψ := ⟨fun {n} p1 p2 h => by
    rcases p1 with _ | _ <;> rcases p2 with _ | _
    · exact .rfl
    · exact h.elim
    · exact h.elim
    · exact .rfl⟩
  refine (and_intro .rfl (pure_intro (P := iprop(proto_message (PROPn := PROPn) a m ≡ proto_end))
    (show (proto_message (PROPn := PROPn) a m).isSome from rfl))).trans ?_
  refine (imp_elim (internalEq.rewrite Ψ)).trans ?_
  exact pure_elim' fun h => nomatch h

theorem proto_end_message_equivI (a : action) (m : V → (Later (proto V PROP PROPn) -n> PROP)) :
    (iprop(proto_end ≡ proto_message (PROPn := PROPn) a m) : SPROP) ⊢ False :=
  internalEq.symm.trans (proto_message_end_equivI a m)

end equivI

/-! ## Functor -/

section map
variable {V : Type}

def proto_map_aux {PROPn PROPn' PROP PROP' : Type} [COFE PROPn] [COFE PROPn'] [COFE PROP] [COFE PROP']
    (g : PROP -n> PROP') (r : proto V PROP' PROPn' -n> proto V PROP PROPn) :
    proto V PROPn PROP -n> proto V PROPn' PROP' where
  f p := proto_elim proto_end (fun a m => proto_message a (fun v => g.comp ((m v).comp (laterMap r)))) p
  ne := ⟨fun {_ p1 p2} h => proto_elim_ne _ _ _ p1 p2
    (fun a _ _ hm => proto_message_ne a (fun v _ => g.ne.ne (hm v _))) h⟩

instance proto_map_aux_contractive {PROPn PROPn' PROP PROP' : Type} [COFE PROPn] [COFE PROPn']
    [COFE PROP] [COFE PROP'] (g : PROP -n> PROP') :
    Contractive (proto_map_aux (V := V) (PROPn := PROPn) (PROPn' := PROPn') g) where
  distLater_dist {_ r1 r2} h p := proto_elim_ne proto_end
    (fun a m => proto_message a (fun v => g.comp ((m v).comp (laterMap r1))))
    (fun a m => proto_message a (fun v => g.comp ((m v).comp (laterMap r2)))) p p
    (fun a m1 m2 hm => proto_message_ne a fun v x =>
      g.ne.ne ((hm v _).trans ((m2 v).ne.ne (laterMap_contractive.distLater_dist h x)))) .rfl

def proto_map_aux_2 {PROPn PROPn' PROP PROP' : Type} [COFE PROPn] [COFE PROPn'] [COFE PROP] [COFE PROP']
    (gn : PROPn' -n> PROPn) (g : PROP -n> PROP')
    (r : proto V PROPn PROP -n> proto V PROPn' PROP') :
    proto V PROPn PROP -n> proto V PROPn' PROP' :=
  proto_map_aux g (proto_map_aux gn r)

instance proto_map_aux_2_contractive {PROPn PROPn' PROP PROP' : Type} [COFE PROPn] [COFE PROPn']
    [COFE PROP] [COFE PROP'] (gn : PROPn' -n> PROPn) (g : PROP -n> PROP') :
    Contractive (proto_map_aux_2 (V := V) gn g) where
  distLater_dist h :=
    (ne_of_contractive (proto_map_aux g)).ne ((proto_map_aux_contractive gn).distLater_dist h)

def proto_map {PROPn PROPn' PROP PROP' : Type} [COFE PROPn] [COFE PROPn'] [COFE PROP] [COFE PROP']
    (gn : PROPn' -n> PROPn) (g : PROP -n> PROP') :
    proto V PROPn PROP -n> proto V PROPn' PROP' :=
  fixpoint (proto_map_aux_2 gn g)

private theorem proto_map_unfold_dist (n : Nat) : ∀ {PROPn PROPn' PROP PROP' : Type} [COFE PROPn]
    [COFE PROPn'] [COFE PROP] [COFE PROP'] (gn : PROPn' -n> PROPn) (g : PROP -n> PROP')
    (p : proto V PROPn PROP), proto_map gn g p ≡{n}≡ proto_map_aux g (proto_map g gn) p := by
  induction n using Nat.strongRecOn with
  | _ n IH =>
  intro PROPn PROPn' PROP PROP' _ _ _ _ gn g p
  have := fixpoint_unfold (proto_map_aux_2 (V := V) gn g).toContractiveHom
  refine (congrArg (fun f => Hom.f f p) this).dist.trans ?_
  exact (proto_map_aux_contractive g).distLater_dist (fun m hm q => (IH m hm g gn q).symm) p

theorem proto_map_unfold {PROPn PROPn' PROP PROP' : Type} [COFE PROPn] [COFE PROPn'] [COFE PROP]
    [COFE PROP'] (gn : PROPn' -n> PROPn) (g : PROP -n> PROP') (p : proto V PROPn PROP) :
    proto_map gn g p = proto_map_aux g (proto_map g gn) p :=
  OFE.eq_dist_2 fun n => proto_map_unfold_dist n gn g p

@[simp] theorem proto_map_end {PROPn PROPn' PROP PROP' : Type} [COFE PROPn] [COFE PROPn'] [COFE PROP]
    [COFE PROP'] (gn : PROPn' -n> PROPn) (g : PROP -n> PROP') :
    proto_map gn g (proto_end : proto V PROPn PROP) = proto_end := by
  rw [proto_map_unfold]; rfl

theorem proto_map_message {PROPn PROPn' PROP PROP' : Type} [COFE PROPn] [COFE PROPn'] [COFE PROP]
    [COFE PROP'] (gn : PROPn' -n> PROPn) (g : PROP -n> PROP') (a : action)
    (m : V → (Later (proto V PROP PROPn) -n> PROP)) :
    proto_map gn g (proto_message a m) =
      proto_message a (fun v => g.comp ((m v).comp (laterMap (proto_map g gn)))) := by
  rw [proto_map_unfold]
  simp only [proto_map_aux]
  exact proto_elim_message _ _ a m

theorem proto_map_ne (n : Nat) : ∀ {PROPn PROPn' PROP PROP' : Type} [COFE PROPn] [COFE PROPn']
    [COFE PROP] [COFE PROP'] (gn1 gn2 : PROPn' -n> PROPn) (g1 g2 : PROP -n> PROP')
    (p : proto V PROPn PROP), gn1 ≡{n}≡ gn2 → g1 ≡{n}≡ g2 →
    proto_map gn1 g1 p ≡{n}≡ proto_map gn2 g2 p := by
  induction n using Nat.strongRecOn with
  | _ n IH =>
  intro PROPn PROPn' PROP PROP' _ _ _ _ gn1 gn2 g1 g2 p Hgn Hg
  rcases proto_case p with rfl | ⟨a, m, rfl⟩
  · rw [proto_map_end, proto_map_end]
  · rw [proto_map_message, proto_map_message]
    refine proto_message_ne a fun v x => (Hg _).trans (g2.ne.ne ((m v).ne.ne ?_))
    exact fun k hk => IH k hk g1 g2 gn1 gn2 _ (Hg.lt hk) (Hgn.lt hk)

theorem proto_map_ext {PROPn PROPn' PROP PROP' : Type} [COFE PROPn] [COFE PROPn'] [COFE PROP]
    [COFE PROP'] (gn1 gn2 : PROPn' -n> PROPn) (g1 g2 : PROP -n> PROP') (p : proto V PROPn PROP)
    (Hgn : gn1 = gn2) (Hg : g1 = g2) :
    proto_map gn1 g1 p = proto_map gn2 g2 p := by
  subst Hgn Hg; rfl

private theorem proto_map_id_dist (n : Nat) : ∀ {PROPn PROP : Type} [COFE PROPn] [COFE PROP]
    (p : proto V PROPn PROP), proto_map Hom.id Hom.id p ≡{n}≡ p := by
  induction n using Nat.strongRecOn with
  | _ n IH =>
  intro PROPn PROP _ _ p
  rcases proto_case p with rfl | ⟨a, m, rfl⟩
  · rw [proto_map_end]
  · rw [proto_map_message]
    exact proto_message_ne a fun v x => (m v).ne.ne (fun k hk => IH k hk _)

theorem proto_map_id {PROPn PROP : Type} [COFE PROPn] [COFE PROP] (p : proto V PROPn PROP) :
    proto_map Hom.id Hom.id p = p :=
  OFE.eq_dist_2 fun n => proto_map_id_dist n p

private theorem proto_map_compose_dist (n : Nat) : ∀ {PROPn PROPn' PROPn'' PROP PROP' PROP'' : Type}
    [COFE PROPn] [COFE PROPn'] [COFE PROPn''] [COFE PROP] [COFE PROP'] [COFE PROP'']
    (gn1 : PROPn'' -n> PROPn') (gn2 : PROPn' -n> PROPn)
    (g1 : PROP -n> PROP') (g2 : PROP' -n> PROP'') (p : proto V PROPn PROP),
    proto_map (gn2.comp gn1) (g2.comp g1) p ≡{n}≡ proto_map gn1 g2 (proto_map gn2 g1 p) := by
  induction n using Nat.strongRecOn with
  | _ n IH =>
  intro PROPn PROPn' PROPn'' PROP PROP' PROP'' _ _ _ _ _ _ gn1 gn2 g1 g2 p
  rcases proto_case p with rfl | ⟨a, m, rfl⟩
  · simp only [proto_map_end]; exact .rfl
  · rw [proto_map_message, proto_map_message, proto_map_message]
    exact proto_message_ne a fun v x =>
      g2.ne.ne (g1.ne.ne ((m v).ne.ne (fun k hk => IH k hk g1 g2 gn1 gn2 _)))

theorem proto_map_compose {PROPn PROPn' PROPn'' PROP PROP' PROP'' : Type}
    [COFE PROPn] [COFE PROPn'] [COFE PROPn''] [COFE PROP] [COFE PROP'] [COFE PROP'']
    (gn1 : PROPn'' -n> PROPn') (gn2 : PROPn' -n> PROPn)
    (g1 : PROP -n> PROP') (g2 : PROP' -n> PROP'') (p : proto V PROPn PROP) :
    proto_map (gn2.comp gn1) (g2.comp g1) p = proto_map gn1 g2 (proto_map gn2 g1 p) :=
  OFE.eq_dist_2 fun n => proto_map_compose_dist n gn1 gn2 g1 g2 p

end map

/-- Rocq `protoOF V Fn F`: the functor `(A, B) ↦ proto V (Fn B A) (F A B)`. -/
abbrev protoOF (V : Type) (Fn F : OFunctorPre.{0,0,0}) [OFunctor Fn] [OFunctor F]
    [∀ (α β : Type) [COFE α] [COFE β], IsCOFE (Fn α β)]
    [∀ (α β : Type) [COFE α] [COFE β], IsCOFE (F α β)] : OFunctorPre :=
  fun A B _ _ => proto V (Fn B A) (F A B)

instance protoOF_ofunctor (V : Type) (Fn F : OFunctorPre.{0,0,0}) [OFunctor Fn] [OFunctor F]
    [∀ (α β : Type) [COFE α] [COFE β], IsCOFE (Fn α β)]
    [∀ (α β : Type) [COFE α] [COFE β], IsCOFE (F α β)] :
    OFunctor (protoOF V Fn F) where
  ofe := inferInstance
  map f g := proto_map (OFunctor.map (F := Fn) g f) (OFunctor.map (F := F) f g)
  map_ne.ne {n} _ _ hf _ _ hg x :=
    proto_map_ne n _ _ _ _ x (OFunctor.map_ne.ne hg hf) (OFunctor.map_ne.ne hf hg)
  map_id x := by
    simp only [COFE.OFunctor.map_id_eq]; exact proto_map_id x
  map_comp f g f' g' x := by
    simp only [COFE.OFunctor.map_comp_eq]; exact proto_map_compose _ _ _ _ x

instance protoOF_contractive (V : Type) (Fn F : OFunctorPre.{0,0,0})
    [OFunctorContractive Fn] [OFunctorContractive F]
    [∀ (α β : Type) [COFE α] [COFE β], IsCOFE (Fn α β)]
    [∀ (α β : Type) [COFE α] [COFE β], IsCOFE (F α β)] :
    OFunctorContractive (protoOF V Fn F) where
  map_contractive := ⟨fun {n} {fg1 fg2} h x =>
    proto_map_ne n _ _ _ _ x
      (fun y => OFunctorContractive.map_distLater (fun m hm => (h m hm).2) (fun m hm => (h m hm).1) y)
      (fun y => OFunctorContractive.map_distLater (fun m hm => (h m hm).1) (fun m hm => (h m hm).2) y)⟩

end Perennial
