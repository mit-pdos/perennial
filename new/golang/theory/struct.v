From Perennial.goose_lang Require Import lifting.
From New.golang Require defn.
From New.golang.defn Require Export struct.
From New.golang.theory Require Import typed_pointsto exception list typing dynamic_typing.
From Perennial.Helpers Require Import NamedProps.
From RecordUpdate Require Export RecordUpdate.
From Perennial Require Import base.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

Set Default Proof Using "Type".

Module struct.
Section goose_lang.
Context `{ffi_syntax}.

Implicit Types (d : struct.descriptor).
Infix "=?" := (ByteString.eqb).

Definition field_offset_f (t : go_type) f : (w64 * go_type) :=
  let missing := W64 (2^64-1) in
  match t with
  | structT d =>
      (fix field_offset_struct (d : struct.descriptor) : (w64 * go_type) :=
         match d with
         | [] => (missing, badT)
         | (f',t)::fs => if f' =? f then (W64 0, t)
                         else match field_offset_struct fs with
                              | (off, t') => (word.add (go_type_size t) off, t')
                              end
         end) d
  | _ => (missing, badT)
  end .

Definition field_ty_f t f : go_type := (field_offset_f t f).2.

Definition field_get_f t f0: val -> val :=
  match t with
  | structT d =>
      (fix go d v :=
         match d with
         | [] => #()
         | (f,_)::fs =>
             match v with
             | PairV v1 v2 => if f =? f0 then v1 else go fs v2
             | _ => #()
             end
         end) d
  | _ => λ v, LitV LitPoison
  end.

Definition field_set_f t f0 fv: val -> val :=
  match t with
  | structT d =>
      (fix go d v :=
         match d with
         | [] => v
         | (f,_)::fs =>
             match v with
             | PairV v1 v2 =>
                 if f =? f0
                 then PairV fv v2
                 else PairV v1 (go d v2)
             | _ => v
             end
         end) d
  | _ => λ v, LitV LitPoison
  end
  .

Definition field_ref_f_def t f0 l: loc := l +ₗ uint.Z (field_offset_f t f0).1.
Program Definition field_ref_f := sealed @field_ref_f_def.
Definition field_ref_f_unseal : field_ref_f = _ := seal_eq _.

Class Wf (t : go_type) : Set :=
  {
    descriptor_NoDup: match t with
    | structT d => NoDup d.*1
    | _ => False
    end
  }.

End goose_lang.
End struct.

Notation "l ↦s[ t :: f ] dq v" := (struct.field_ref_f t f l ↦{dq} v)%I
  (at level 50, dq custom dfrac at level 70, t at level 59, f at level 59,
     format "l  ↦s[ t  ::  f ] dq  v").

Definition option_descriptor_wf (d : struct.descriptor) : option (struct.Wf (structT d)).
  destruct (decide (NoDup d.*1)); [ apply Some | apply None ].
  constructor; auto.
Defined.

Definition proj_descriptor_wf (d : struct.descriptor) :=
  match option_descriptor_wf d as mwf return match mwf with
                                             | Some _ => struct.Wf (structT d)
                                             | None => True
                                             end  with
  | Some pf => pf
  | None => I
  end.

(* This hint converts [someStructType] into [structT blah] *)
Global Hint Extern 10 (struct.Wf ?t) => unfold t : typeclass_instances.
Global Hint Extern 3 (struct.Wf (structT ?d)) => exact (proj_descriptor_wf d) : typeclass_instances.

Section lemmas.
Context `{heapGS Σ}.

Record StructField V :=
struct_field {
  Vf : Type;
  proj : V → Vf;
  iv :: IntoVal Vf;
  tf : go_type;
  ivt :: IntoValTyped Vf tf;
  setter_wf :: SetterWf proj;
}.
Arguments struct_field {_ _} (_) {_ _ _ _}.
Arguments tf {_} (_).
Arguments proj {_} (_ _).

Lemma struct_val_aux_eq decls fvs fvs' :
  (∀ f t, (f, t) ∈ decls →
  default (zero_val t) (alist_lookup_f f fvs) = default (zero_val t) (alist_lookup_f f fvs')) ↔
  struct.val_aux (structT decls) fvs = struct.val_aux (structT decls) fvs'.
Proof.
  split.
  - intros Heq. induction decls as [|[]].
    + rewrite !struct.val_aux_nil //.
    + rewrite !struct.val_aux_cons. simpl in *. rewrite -IHdecls; first f_equal.
      2:{ intros. apply Heq. right. done. }
      apply Heq. left.
  - intros Heq. intros ?? Hin. induction decls as [|[]]; first by inversion Hin.
    rewrite !struct.val_aux_cons in Heq. simplify_eq.
    apply elem_of_cons in Hin. destruct Hin as [Hin|Hcontinue].
    + simplify_eq. done.
    + by apply IHdecls.
Qed.

Definition x V (projections : list (go_string * StructField V)) :=
  foldl (λ mkType '(_, p), p.(Vf V) → mkType) V projections.
Record t := mk {
  wall' : w64;
  ext' : w64;
  loc' : loc;
}.
Global Instance settable_Time `{ffi_syntax} : Settable _ :=
  settable! mk < wall'; ext'; loc' >.
Definition y := [
    ("wall"%go, struct_field wall');
    ("ext"%go, struct_field ext');
    ("loc"%go, struct_field loc')
  ]%struct.

Eval simpl in foldr (λ '(_, p) mkType, p.(Vf t) → mkType) t y.
Check (mk : foldr (λ '(_, p) mkType, p.(Vf t) → mkType) t y).

Program Definition x'
  {V : Type} (projections : list (go_string * StructField V))
  (mk_record : foldr (λ '(_, p) mkType, p.(Vf V) → mkType) V projections)
  : Prop :=
  (fix go (projections : list (go_string * StructField V)) mk1 mk2 :=
     match projections as ps return (projections = ps → Prop) with
     | [] => λ _, mk1 = mk2
     | (name, p) :: tl =>
         λ Heq,
         (∀ (x x' : p.(Vf V)),
            _
         )
     end eq_refl
  ) projections mk_record mk_record.
Final Obligation.
intros. subst. clear -go mk1 mk2 x0 x'.
set (y:=mk1 x0). set (y':=mk2 x').
eapply go.
{ exact y. }
{ exact y'. }
Defined.

Eval simpl in x' y mk.
Lemma test : x' y mk.
Proof.
  cbn. intros ??????. cbn. unfold x'.
  cbn.
  rewrite /eq_trans /f_equal. simpl.
  unfold foldr_cons.
  simpl. intros ??. clear.
  simpl in *.
Eval cbn in x' y mk.
unfodl eq_$ect

specialize ()
Show Proof.
subst.
Show Proof.

mk_record mk_record.


Class IntoValStruct (t : go_type) (V : Type) :=
  {
    projections : list (go_string * StructField V);
    mk_record : foldr (λ '(_, p) mkType, p.(Vf V) → mkType) V projections;
    mk_record_inv :
    (fix go projections (mk1 mk2 : foldr (λ '(_, p) mkType, p.(Vf V) → mkType) V projections) :=
       match projections with
       | [] => mk1 = mk2
       | (name, p) :: tl =>
           mk1 = match projections as ps return (foldr _ _ ps) with
                 | [] => mk1
                 | (name, p) :: tl => mk1
                 end
       end
    ) projections mk_record mk_record;
  }.
    (* )| _ => None *)
    end
    foldl (λ P '(_, p),
                             True
                        (* ∀ (a a' : p.(Vf V)), mk_record a = mk_record a' → a = a' *)
                      ) True projections;
    (* default_struct_val : V; *)
    size_bounded : go_type_size t < 2^64;
    struct_wf :: struct.Wf t;
    projections_match : t = structT ((λ '(x, p), (x, p.(tf))) <$> projections);
    projections_complete : (∀ v1 v2, Forall (λ '(_, p), p.(proj) v1 = p.(proj) v2) projections → v1 = v2);
    (* default_projections : Forall (λ '(_, p), p.(proj) default_struct_val = default_val _) projections; *)
    #[global] struct_eq_dec :: EqDecision V;
  }.

Global Instance into_val_struct_into_val `{!IntoValStruct t V} : IntoVal V :=
  {|
    to_val_def := λ v, struct.val_aux t ((λ '(n, p), (n, #(p.(proj) v))) <$> projections)
  |}.

Program Global Instance into_val_struct_into_val_typed `{!IntoValStruct t V} : IntoValTyped V t :=
  {|
    default_val := default_struct_val;
  |}.
Next Obligation.
  intros.
  destruct IntoValStruct0; subst.
  rewrite to_val_unseal. simpl. constructor. intros ?? Hin.
  clear -Hin struct_wf0. induction projections0 as [|[]]; first done.
  pose proof struct.descriptor_NoDup as Hdup. rewrite fmap_cons in Hdup.
  inversion Hdup. subst. rename H1 into Hnotin.
  destruct Hin as [Hin|Hcontinue].
  - simplify_eq. simpl. rewrite ByteString.eqb_refl /=. apply to_val_has_go_type.
  - simpl. rewrite ByteString.eqb_ne /=.
    { by apply IHprojections0. }
    intros Heq. subst. rewrite -elem_of_list_In in Hcontinue.
    apply Hnotin. by eapply elem_of_list_fmap_1_alt.
Qed.
Next Obligation.
  intros. destruct IntoValStruct0; subst.
  rewrite zero_val_eq to_val_unseal /=. pose proof struct.descriptor_NoDup as Hdup. simpl in Hdup.
  clear -default_projections0 Hdup.
  induction projections0 as [|[]]; first done.
  rewrite !struct.val_aux_cons /=. inversion Hdup; subst.
  inversion default_projections0; subst. simpl.
  rewrite ByteString.eqb_refl /= H3 default_val_eq_zero_val. f_equal.
  rewrite -IHprojections0 //=. apply struct_val_aux_eq. intros ?? Hin.
  apply elem_of_list_fmap_2 in Hin as [[f' ?] [[=->->] ?]].
  f_equal. simpl. rewrite ByteString.eqb_ne //. intros Heq. subst. apply H1.
  eapply elem_of_list_fmap_1_alt; try done.
  { eapply elem_of_list_fmap_1_alt; done. }
  done.
Qed.
Final Obligation.
  intros. rewrite to_val_unseal /=. intros x y Heq. apply projections_complete.
  destruct IntoValStruct0. pose proof struct.descriptor_NoDup as Hdup. subst.
  rewrite Forall_forall.
  intros [] Hin. simpl in *. clear -Hin Heq Hdup.
  induction projections0 as [|[]]; first done.
  rewrite -struct_val_aux_eq in Heq.
  destruct Hin as [Hin|Hcontinue].
  - simplify_eq. opose proof (Heq g s.(tf) _) as Heq.
    { left. }
    simpl in Heq. rewrite /= ByteString.eqb_refl /= in Heq.
    apply to_val_inj. done.
  - inversion Hdup; subst. apply IHprojections0; try done.
    rewrite struct_val_aux_eq in Heq.
    rewrite !fmap_cons !struct.val_aux_cons in Heq.
    simplify_eq. rename H into H'.
    rewrite -!struct_val_aux_eq in H' |- *.
    intros. ospecialize (H' f t ltac:(done)).
    simpl in H'. rewrite ByteString.eqb_ne // in H'.
    intros ->. apply H1. apply elem_of_list_fmap_2 in H as [[f' ?] [[=->->] ?]].
    eapply elem_of_list_fmap_1_alt; try done.
    { eapply elem_of_list_fmap_1_alt; done. }
    done.
Qed.

Lemma struct_val_inj d fvs1 fvs2 :
  struct.val_aux (structT d) fvs1 = struct.val_aux (structT d) fvs2 →
  ∀ f, In f d.*1 →
       match (alist_lookup_f f fvs1), (alist_lookup_f f fvs2) with
       | Some v1, Some v2 => v1 = v2
       | _, _ => True
       end.
Proof.
  rewrite struct.val_aux_unseal.
  induction d as [|[]].
  { done. }
  intros Heq ? [].
  - subst. simpl in Heq.
    injection Heq as ??.
    repeat destruct alist_lookup_f; naive_solver.
  - simpl in *. injection Heq as ??. by apply IHd.
Qed.

Class StructFieldsSplit `{!IntoValStruct t V} {dwf : struct.Wf t}
                        (dq : dfrac) (l : loc) (v : V) (Psplit : iProp Σ)
  :=
  {
    struct_fields_splittable : (Psplit ⊣⊢ [∗ list] '(name, p) ∈ projections, struct.field_ref_f t name l ↦{dq} (p.(proj) v))
  }.

(* A specialized version of [big_sepL_app] that simplifies some loc_add-related
expressions. Not strictly about heap_pointsto, but specialized with a dfrac so
higher-order unification works properly. *)
Lemma heap_pointsto_app (vs1 vs2: list val) (l: loc) dq (f: loc → dfrac → val → iProp Σ) :
  ([∗ list] j↦vj ∈ (vs1 ++ vs2), f (l +ₗ j) dq vj) ⊣⊢
  ([∗ list] j↦vj ∈ vs1, f (l +ₗ j) dq vj) ∗
  ([∗ list] j↦vj ∈ vs2, f (l +ₗ (Z.of_nat (length vs1)) +ₗ Z.of_nat j) dq vj).
Proof.
  rewrite big_sepL_app.
  f_equiv.
  setoid_rewrite Nat2Z.inj_add.
  setoid_rewrite loc_add_assoc.
  reflexivity.
Qed.

Lemma struct_field_offset_le decls f:
  f ∈ decls.*1 →
  uint.Z (struct.field_offset_f (structT decls) f).1 ≤ go_type_size (structT decls).
Proof.
  intros Hin. induction decls as [|[]]; first set_solver.
  simpl.
  destruct (decide (g = f)).
  - subst. rewrite ByteString.eqb_refl. simpl. word.
  - simpl in *. rewrite ByteString.eqb_ne //.
    rewrite !go_type_size_unseal in IHdecls |- *. simpl in *.
    ospecialize (IHdecls _); first set_solver.
    set (x:=_ decls) in IHdecls |- *.
    destruct x eqn:H'. simpl in *. word.
Qed.

Lemma struct_field_offset_cons f t decls f' :
  go_type_size (structT ((f,t)::decls)) < 2^64 →
  f' ≠ f →
  f' ∈ decls.*1 →
  uint.Z (struct.field_offset_f (structT ((f,t)::decls)) f').1 =
  go_type_size t + uint.Z (struct.field_offset_f (structT decls) f').1.
Proof.
  intros Hsize Hne Hin.
  opose proof (struct_field_offset_le decls f' _) as Hw.
  { simpl. done. }
  subst. simpl in *. rewrite ByteString.eqb_ne //.
  set (x:=_ decls) in Hw |- *.
  destruct x. simpl in *.
  simpl. rewrite !go_type_size_unseal in Hsize Hw |- *.
  simpl in *. word.
Qed.

Lemma flatten_struct_tt : flatten_struct #() = [].
Proof. rewrite to_val_unseal //. Qed.

Lemma flatten_struct_val_aux `{!IntoValStruct t V} v :
  flatten_struct (struct.val_aux t ((λ '(n, p), (n ::= # (proj p v))%struct) <$> projections)) =
  concat (flatten_struct <$> ((λ '(_, p), #(proj p v)) <$> projections)).
Proof.
  pose proof projections_match. rewrite {1}H0.
  destruct IntoValStruct0. pose proof struct.descriptor_NoDup as Hdup. subst.
  simpl in *. clear -Hdup. induction projections0 as [|[]].
  { rewrite /= struct.val_aux_nil flatten_struct_tt //. }
  rewrite struct.val_aux_cons /=. inversion Hdup; subst.
  rewrite /= -IHprojections0 //. rewrite ByteString.eqb_refl. f_equal.
  f_equal. apply struct_val_aux_eq. intros ?? Hin. f_equal.
  simpl. rewrite ByteString.eqb_ne //.
  intros Heq. subst. apply H1.
  by eapply elem_of_list_fmap_1_alt.
Qed.

Lemma sep_equiv {PROP : bi} (P P' Q Q' : PROP) :
  P ⊣⊢ P' →
  Q ⊣⊢ Q' →
  P ∗ Q ⊣⊢ P' ∗ Q'.
Proof. by intros -> ->. Qed.

Lemma big_sepL_equiv {PROP:bi} {A} (l : list A) (Φ Ψ : _ → _ → PROP) :
  (∀ i x, l !! i = Some x → Φ i x ⊣⊢ Ψ i x) →
  ([∗ list] i ↦ x ∈ l, Φ i x)%I ⊣⊢ ([∗ list] i ↦ x ∈ l, Ψ i x)%I.
Proof.
  induction l using rev_ind; first done.
  rewrite !big_sepL_snoc => Heq.
  rewrite IHl.
  - simpl. iSplit.
    + iIntros "[$ H]". rewrite Heq; first iFrame.
      rewrite lookup_app_r // Nat.sub_diag //.
    + iIntros "[$ H]". rewrite Heq; first iFrame.
      rewrite lookup_app_r // Nat.sub_diag //.
  - intros ?? Hlook. apply Heq. rewrite lookup_app Hlook //.
Qed.

Lemma big_sepL_concat {PROP:bi} {A} (l : list (list A)) (Φ : _ → _ → PROP) :
  ([∗ list] i ↦ x ∈ concat l, Φ i x) ⊣⊢
  ([∗ list] j ↦ xs ∈ l, ([∗ list] i ↦ x ∈ xs, Φ (length (concat (take j l)) + i)%nat x)).
Proof.
  clear. induction l using rev_ind; first done. simpl. rewrite !concat_app !big_sepL_app.
  apply sep_equiv. 2: rewrite /= take_app Nat.add_0_r Nat.sub_diag take_0 app_nil_r take_ge //.
  rewrite IHl. apply big_sepL_equiv. intros.
  apply lookup_lt_Some in H. rewrite take_app_le //. lia.
Qed.

Lemma eq_equiv `{Equiv A, !Reflexive (≡@{A})} {a a' : A}:
  a = a' → a ≡ a'.
Proof. intros ->. reflexivity. Qed.

Lemma struct_field_offset_lookup i f t decls `{!NoDup decls.*1}:
  go_type_size (structT decls) < 2^64 →
  decls !! i = Some (f, t) →
  uint.Z (struct.field_offset_f (structT decls) f).1 =
  list_sum (go_type_size <$> take i (decls.*2)).
Proof.
  intros Hty. generalize dependent i. induction decls as [|[]]; first done; intros i Hlookup.
  destruct i.
  - subst. simpl in *. simplify_eq. rewrite ByteString.eqb_refl //.
  - inversion NoDup0; subst.
    rewrite struct_field_offset_cons; [ |list_simplifier..]; first last.
    { apply elem_of_list_lookup_2 in Hlookup. eapply elem_of_list_fmap_1_alt; done. }
    { intros ->. subst. apply elem_of_list_lookup_2 in Hlookup.
      exfalso. apply H2. eapply elem_of_list_fmap_1_alt; done. }
    { done. }
    ospecialize (IHdecls _ _ i _).
    { done. }
    { clear -Hty. rewrite go_type_size_unseal in Hty |- *. simpl in *. word. }
    { list_simplifier. done. }
    rewrite IHdecls fmap_cons firstn_cons fmap_cons /=. word.
Qed.

Lemma struct_fields_split' `{IntoValStruct t V} l dq (v : V) :
  l ↦{dq} v ⊣⊢ [∗ list] '(name, p) ∈ projections, struct.field_ref_f t name l ↦{dq} (p.(proj) v).
Proof.
  rewrite typed_pointsto_unseal /typed_pointsto_def.
  rewrite [in #v]to_val_unseal /= flatten_struct_val_aux big_sepL_concat
    big_sepL_fmap big_sepL_fmap.
  apply big_sepL_equiv.
  intros i [name p] Hlookup.
  rewrite struct.field_ref_f_unseal /struct.field_ref_f_def.
  rewrite typed_pointsto_unseal /typed_pointsto_def.
  apply big_sepL_equiv. intros j x Hlook_x. apply eq_equiv.
  f_equal. rewrite loc_add_assoc. f_equal.
  rewrite length_concat. rewrite -> fmap_take.
  pose proof projections_match. rewrite [in struct.field_offset_f _ _]H1.
  erewrite (struct_field_offset_lookup i).
  2:{ pose proof struct.descriptor_NoDup as Hdup. rewrite H1 // in Hdup. }
  2:{ pose proof size_bounded. rewrite H1 in H2. done. }
  2:{ rewrite list_lookup_fmap. rewrite Hlookup //. }
  zify. f_equal. rewrite fmap_take.
  rewrite -!list_fmap_compose. unfold compose.
  setoid_rewrite has_go_type_len; first done.
  destruct x0. apply to_val_has_go_type.
Qed.

Lemma struct_fields_split `{StructFieldsSplit t V dq l} :
  l ↦{dq} v ⊢ Psplit.
Proof. rewrite struct_fields_split' /=. rewrite -> struct_fields_splittable. done. Qed.

Lemma struct_fields_combine `{StructFieldsSplit t V dq l} :
  Psplit ⊢ l ↦{dq} v.
Proof. rewrite struct_fields_split' /=. rewrite -> struct_fields_splittable. done. Qed.

Class IntoValStructField (f : go_string) (t : go_type) {V Vf' : Type} {tf'}
  (field_proj : V → Vf')
  `{!IntoValStruct t V}
  `{!IntoVal Vf'}
  `{!IntoValTyped Vf' tf'} :=
  {
    lookup_projection : (alist_lookup_f f projections) = Some (struct_field field_proj)
  }.

Theorem struct_fields_acc_update f t V Vf'
  l dq {dwf : struct.Wf t} (v : V) (field_proj : _ → Vf')
  `{IntoValStructField f t V Vf' tf' field_proj} `{!SetterWf field_proj} :
  l ↦{dq} v -∗
  l ↦s[t :: f]{dq} (field_proj v) ∗
  (∀ fv', l ↦s[t :: f]{dq} fv' -∗
          typed_pointsto l dq (set field_proj (λ _, fv') v)).
Proof.
  iIntros "Hl".
  iDestruct (struct_fields_split' with "Hl") as "H".
  inversion H0.
  eassert (Hp : ∃ i, projections !! i = Some (f, _)).
  { induction projections as [|[]]; first done.
    destruct (decide (g = f)).
    - eexists O. simpl in *. subst. rewrite ByteString.eqb_refl in lookup_projection0.
      simplify_eq. done.
    - ospecialize (IHl0 _).
      { simpl in *. rewrite ByteString.eqb_ne // in lookup_projection0. }
      destruct IHl0 as [i IHl].
      eexists (S i). done. }
  destruct Hp as [i Hp].
  iDestruct (big_sepL_lookup_acc_impl with "H") as "[H' H]"; first eassumption.
  simpl. iFrame.
  iIntros (?) "H'".
  iApply struct_fields_split'.
  iApply ("H" with "[] [H']").
  2:{ rewrite set_get. iFrame. }
  iIntros "!# * %Hlook %Hne H". destruct y.
  iExactEq "H". f_equal.
  Print Settable.
  Print SetterWf.
  rewrite [in (l ↦{_} v)%I]typed_pointsto_unseal /typed_pointsto_def.
  rewrite to_val_unseal. simpl. destruct IntoValStruct0.
  subst. simpl in *. destruct H0.
  iInduction projections0 as [|[]] "IH".
  { simpl in *. done. }
  simpl in *.
Qed.

Theorem struct_fields_acc f t V Vf
  l dq {dwf : struct.Wf t} (v : V)
  `{IntoValStructField f t V Vf tf' field_proj} `{!SetterWf field_proj} :
  typed_pointsto l dq v -∗
  l ↦s[t :: f]{dq} (field_proj v) ∗
  (l ↦s[t :: f]{dq} (field_proj v) -∗ typed_pointsto l dq v).
Proof.
  iIntros "Hl".
  iDestruct (struct_fields_acc_update with "[$]") as "[$ H]".
  iIntros "* Hl".
  iSpecialize ("H" with "[$]").
  erewrite set_eq.
  2:{ done. } iFrame.
Qed.

End lemmas.

Section wps.
Context `{sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.

#[global] Instance field_offset_into_val : IntoVal (w64 * go_type) :=
  { to_val_def := fun '(off, t) => (#off, #t)%V; }.

Lemma field_off_to_val_unfold (p: w64 * go_type) :
  #p = (#p.1, #p.2)%V.
Proof.
  destruct p.
  rewrite {1}to_val_unseal //=.
Qed.

Global Instance pure_struct_field_offset_wp (t: go_type) f :
  PureWp True (struct.field_offset #t #f) (#(struct.field_offset_f t f)).
Proof.
  apply pure_wp_val. iIntros (??).
  induction t using go_type_ind;
    try solve [
        iIntros (Φ) "_ HΦ"; wp_call_lc "?";
        rewrite [in #(_, _)]to_val_unseal /=;
          iApply "HΦ"; done
      ].
  iIntros (Φ) "_ HΦ"; wp_call_lc "?".
  iSpecialize ("HΦ" with "[$]").
  iInduction decls as [|[f' ft] decls] forall (Φ).
  - wp_pures.
    rewrite field_off_to_val_unfold /=.
    iApply "HΦ".
  - match goal with
    | |- context[environments.Esnoc _ (INamed "IHdecls") ?P] =>
        set (IHdeclsP := P)
    end.
    wp_pures.
    rewrite !field_off_to_val_unfold !desc_to_val_unfold /=.
    wp_pures.
    destruct (bool_decide_reflect (f' = f)); subst.
    + rewrite -> bool_decide_eq_true_2 by auto; wp_pures.
      rewrite -> ByteString.eqb_eq by auto.
      iApply "HΦ".
    + rewrite -> bool_decide_eq_false_2 by auto; wp_pures.
      rewrite -> ByteString.eqb_ne by auto.
      wp_bind (match decls with | nil => _ | cons _ _ => _ end).
      iApply "IHdecls".
      { naive_solver. }
      wp_pures.
      rewrite field_off_to_val_unfold.
      destruct ((fix field_offset_struct (d : struct.descriptor) :=
                  match d with
                  | nil => _
                  | cons _ _ => _
                  end)
        decls) eqn:Hoff.
      wp_pures.
      wp_apply wp_type_size.
      iIntros "_".
      wp_pures.
      iApply "HΦ".
Qed.

Global Instance pure_struct_field_ref_wp (t: go_type) f (l : loc) :
  PureWp True (struct.field_ref #t #f #l) #(struct.field_ref_f t f l).
Proof.
  pure_wp_start.
  destruct (struct.field_offset_f t f) eqn:Hoff.
  rewrite field_off_to_val_unfold /=; wp_pures.
  iExactEq "HΦ".
  repeat f_equal.
  rewrite struct.field_ref_f_unseal /struct.field_ref_f_def.
  rewrite Hoff /=.
  repeat (f_equal; try word).
Qed.

Definition is_structT (t : go_type) : Prop :=
  match t with
  | structT d => True
  | _ => False
  end.

Definition wp_struct_make (t : go_type) (l : list (go_string*val)) :
  is_structT t →
  PureWp True
  (struct.make #t (alist_val l))
  (struct.val_aux t l).
Proof.
  intros ?.
  pure_wp_start.
  rewrite struct.make_unseal /struct.make_def struct.val_aux_unseal.
  destruct t; try by exfalso.
  wp_pures.
  iInduction decls as [|[f ft] decls] "IH" forall (Φ).
  - wp_pure_lc "?". wp_pures. by iApply "HΦ".
  - wp_pure_lc "?"; wp_pures.
    rewrite !desc_to_val_unfold /=; wp_pures.
    destruct (alist_lookup_f _ _).
    + wp_pures.
      wp_bind (match decls with | nil => _ | cons _ _ => _ end).
      unshelve iApply "IH"; first done.
      iIntros "_".
      simpl fill. wp_pures. by iApply "HΦ".
    + wp_pures.
      wp_bind (match decls with | nil => _ | cons _ _ => _ end).
      unshelve iApply "IH"; first done.
      iIntros "_".
      simpl fill. wp_pures. by iApply "HΦ".
Qed.

Lemma struct_val_aux_nil fvs :
  (struct.val_aux (structT $ []) fvs) = #().
Proof. rewrite struct.val_aux_unseal //=. Qed.

Lemma struct_val_aux_cons decls f t fvs :
  (struct.val_aux (structT $ (f,t) :: decls) fvs) =
  (default (zero_val t) (alist_lookup_f f fvs), (struct.val_aux (structT decls) fvs))%V.
Proof. rewrite struct.val_aux_unseal //=. Qed.

(* Global Instance *) Definition points_to_access_struct_field_ref
  {V Vf} (l : loc) f (v : V) (proj : V → Vf) dq {t tf : go_type}
  `{!IntoValStruct t V} `{!IntoVal Vf} `{!IntoValTyped Vf tf}
  `{!IntoValStructField f t proj} `{!SetterWf proj} `{!struct.Wf t}
  : PointsToAccess (struct.field_ref_f t f l) (proj v)
                   dq
                   (l ↦{dq} v)%I
                   (λ vf', l ↦{dq} (set proj (λ _, vf') v))%I.
Proof.
  constructor.
  - intros. by iApply struct_fields_acc_update.
  - by rewrite RecordSet.set_eq.
Qed.
End wps.

Ltac solve_into_val_struct_field :=
  done.

Ltac solve_struct_make_pure_wp :=
  intros;
  (* BUG: ssreflect has rewrite [in v in PureWp _ _ v]to_val_unseal that would
  do this directly, but Coq incorrectly flags v as an unbound variable when
  trying to use it in an Ltac. *)
  lazymatch goal with
  | |- PureWp _ _ ?v =>
      rewrite [in v]to_val_unseal;
      apply wp_struct_make; cbn; auto
  end.

(* use the above automation the way proofgen does (approximately, not kept in sync) *)
Module __struct_automation_test.

Import New.golang.defn.

Module time.

Definition Time : go_type := structT [
  "wall" :: uint64T;
  "ext" :: int64T;
  "loc" :: ptrT
].

Module Time.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  wall' : w64;
  ext' : w64;
  loc' : loc;
}.
End def.
End Time.

Section instances.

Global Instance settable_Time `{ffi_syntax} : Settable _ :=
  settable! Time.mk < Time.wall'; Time.ext'; Time.loc' >.
Arguments struct_field {_ _ _} (_) {_ _ _}.
Global Program Instance into_val_struct_Time `{ffi_syntax} : IntoValStruct time.Time Time.t :=
  {|
    projections := [
      ("wall"%go, struct_field Time.wall');
      ("ext"%go, struct_field Time.ext');
      ("loc"%go, struct_field Time.loc')
    ]%struct;
    default_struct_val := Time.mk (default_val _) (default_val _) (default_val _);
  |}.
Next Obligation. intros. rewrite go_type_size_unseal. reflexivity. Qed.
Next Obligation. intros. reflexivity. Qed.
Next Obligation. intros ? [][] H. rewrite !Forall_cons /= in H. naive_solver. Qed.
Next Obligation. intros. repeat (constructor; first reflexivity); constructor. Qed.
Final Obligation. intros ?. solve_decision. Qed.

Global Instance into_val_struct_field_Time_wall `{ffi_syntax} : IntoValStructField "wall" time.Time Time.wall'.
Proof. solve_into_val_struct_field. Qed.

Global Instance into_val_struct_field_Time_ext `{ffi_syntax} : IntoValStructField "ext" time.Time Time.ext'.
Proof. solve_into_val_struct_field. Qed.

Global Instance into_val_struct_field_Time_loc `{ffi_syntax} : IntoValStructField "loc" time.Time Time.loc'.
Proof. solve_into_val_struct_field. Qed.

Context `{!ffi_syntax} `{!ffi_model, !ffi_semantics _ _, !ffi_interp _, !heapGS Σ}.
Global Instance wp_struct_make_Time wall' ext' loc':
  PureWp True
    (struct.make #time.Time (alist_val [
      "wall" ::= #wall';
      "ext" ::= #ext';
      "loc" ::= #loc'
    ]))%struct
    #(Time.mk wall' ext' loc').
Proof. solve_struct_make_pure_wp. Qed.


Global Instance Time_struct_fields_split dq l (v : Time.t) :
  StructFieldsSplit dq l v (
    "Hwall" ∷ l ↦s[time.Time :: "wall"]{dq} v.(Time.wall') ∗
    "Hext" ∷ l ↦s[time.Time :: "ext"]{dq} v.(Time.ext') ∗
    "Hloc" ∷ l ↦s[time.Time :: "loc"]{dq} v.(Time.loc') ∗
    "_" ∷ emp
  ).
Proof. done. Qed.

End instances.
End time.

Module empty_struct.


Definition empty_struct : go_type := structT [].

Module unit.
Section def.
Context `{ffi_syntax}.
Record t := mk {
}.
End def.
End unit.

Section instances.
Context `{ffi_syntax}.
Global Instance into_val_unit : IntoVal unit.t :=
  {| to_val_def v :=
    struct.val_aux empty_struct [
    ]%struct
  |}.

Global Program Instance into_val_typed_unit : IntoValTyped unit.t empty_struct :=
{|
  default_val := unit.mk;
|}.
Next Obligation. solve_to_val_type. Qed.
Next Obligation. solve_zero_val. Qed.
Next Obligation. solve_to_val_inj. Qed.
Final Obligation. solve_decision. Qed.


Context `{!ffi_model, !ffi_semantics _ _, !ffi_interp _, !heapGS Σ}.
Global Instance wp_struct_make_unit:
  PureWp True
    (struct.make #empty_struct (alist_val [
    ]))%struct
    #(unit.mk).
Proof. solve_struct_make_pure_wp. Qed.

End instances.

End empty_struct.

End __struct_automation_test.
