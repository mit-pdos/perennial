From New.golang.defn Require Export loop assume predeclared.
From New.code.github_com.mit_pdos.perennial.goose.model Require Import strings.
From Coq Require Import PropExtensionality.

Module go.
Section defs.
Context {ext : ffi_syntax}.
Context {go_lctx : GoLocalContext} {go_gctx : GoGlobalContext}.

(* Lexicographic ordering on go_string (byte lists). *)
Fixpoint go_string_ltb (x y : go_string) : bool :=
  match x, y with
  | [], [] => false
  | [], _ => true
  | _, [] => false
  | (a :: x), (b :: y) => if (word.ltu a b) then
                         true
                       else if (word.eqb a b) then
                              go_string_ltb x y
                            else false
  end.

Example go_string_ltb_examples :
  go_string_ltb "" "" = false ∧
  go_string_ltb "" "a" = true ∧
  go_string_ltb "a" "" = false ∧
  go_string_ltb "ab" "a" = false ∧
  go_string_ltb "ab" "b" = true
  := ltac:(auto).

Fixpoint go_string_lt (x y : go_string) : Prop :=
  match x, y with
  | [], [] => False
  | [], _ => True
  | _, [] => False
  | (a :: x), (b :: y) => if decide (uint.Z a < uint.Z b) then
                         True
                       else if decide (uint.Z a = uint.Z b) then
                              go_string_lt x y
                            else false
  end.

Definition go_string_le (x y : go_string) : Prop :=
  x = y ∨ go_string_lt x y.

Definition go_string_leb (x y : go_string) : bool :=
 bool_decide(x = y) || go_string_ltb x y.

(* Ordering lemmas: totality and reflexivity for w8 and go_string,
   used to show go_string_leb is a total preorder. *)
Lemma w8_trichotomy (a b : w8) :
  word.ltu a b = true \/ word.eqb a b = true \/ word.ltu b a = true.
Proof.
  destruct (decide (uint.Z a < uint.Z b)%Z) as [Hab|Hnab].
  - left.
    rewrite word.unsigned_ltu.
    apply Z.ltb_lt.
    exact Hab.
  - destruct (decide (uint.Z a = uint.Z b)%Z) as [Heq|Hneq].
    + right. left.
      apply word.eqb_eq. 
      word.
    + right. right.
      assert ((uint.Z b < uint.Z a)%Z) by lia.
      rewrite word.unsigned_ltu.
      apply Z.ltb_lt.
      assumption.
Qed.

Lemma w8_ltu_irrefl (a : w8) :
  word.ltu a a = false.
Proof.
  rewrite word.unsigned_ltu. 
  apply Z.ltb_irrefl.
Qed.

Lemma w8_eqb_refl (a : w8) :
  word.eqb a a = true.
Proof.
  apply word.eqb_eq. done.
Qed.

Lemma go_string_ltb_total x y :
  x = y \/ go_string_ltb x y = true \/ go_string_ltb y x = true.
Proof.
  revert y.
  induction x as [|a x IH]; intros [|b y].
  - left; reflexivity.
  - right; left; reflexivity.
  - right; right; reflexivity.
  - destruct (w8_trichotomy a b) as [Hlt | [Heq | Hgt]].
    + right; left; simpl; rewrite Hlt; reflexivity.
    + destruct (word.eqb_spec a b) as [Hab | Hab].
      * subst.
        destruct (IH y) as [Hxy | [Hxy | Hxy]].
        -- left; congruence.
        -- right; left; simpl; rewrite w8_ltu_irrefl. rewrite w8_eqb_refl; assumption.
        -- right; right; simpl; rewrite w8_ltu_irrefl. rewrite w8_eqb_refl; assumption.
      * exfalso. apply Hab. done.
    + right; right; simpl; rewrite Hgt; reflexivity.
Qed.

Lemma go_string_leb_total x y :
  go_string_leb x y = true \/ go_string_leb y x = true.
Proof.
  destruct (go_string_ltb_total x y) as [-> | [Hxy | Hyx]].
  - left.
    unfold go_string_leb.
    assert (y = y) by done. 
    assert (bool_decide (y = y)) by set_solver.  
    replace (bool_decide (y = y)) with true.
    { done. } rewrite bool_decide_true. { done. } done.
  - left.
    unfold go_string_leb.
    replace (go_string_ltb x y ) with true. 
    replace (true = true) with True;first lia. 
    apply Coq.Logic.PropExtensionality.propositional_extensionality; naive_solver.
  
  - right.
    unfold go_string_leb.

    rewrite Hyx. 
    replace (true = true) with True;first lia. 
    apply Coq.Logic.PropExtensionality.propositional_extensionality; naive_solver.
Qed.

Class StringSemantics `{!GoSemanticsFunctions} :=
{
  #[global] package_sem :: strings.Assumptions;

  #[global] internal_string_len_step (s : go_string) ::
    ⟦InternalStringLen, #s⟧ ⤳ (if decide (length s < 2^63) then
                                  (Val #(W64 (length s)))
                                else AngelicExit #());

  #[global] string_len_unfold `{!t ↓u go.string} :: FuncUnfold go.len [t]
    (λ: "s", InternalStringLen "s")%V;

  #[global] string_index (s : go_string) (i : w64) ::
    ⟦Index go.string, (#s, #i)⟧ ⤳[under]
    (match (s !! (sint.nat i)) with Some b => #b | _ => Panic "index out of bounds" end);

  #[global] convert_byte_to_string (c : w8) ::
    ⟦Convert go.byte go.string, #c⟧ ⤳[under] #([c]);

  #[global] convert_bytes_to_string
    `[!from ↓u go.SliceType elem_type] `[!elem_type ↓u go.byte] `[!to ↓u go.string] (v : val) ::
    ⟦Convert from to, v⟧ ⤳[internal] (@! strings.ByteSliceToString v);

  #[global] convert_string_to_bytes
    `[!from ↓u go.string] `[!to ↓u go.SliceType elem_type] `[!elem_type ↓u go.byte] (v : val) ::
    ⟦Convert from to, v⟧ ⤳[internal] (@! strings.StringToByteSlice v);

  #[global] lt_string (x y : go_string) ::
    ⟦GoOp GoLt go.string, (#x, #y)⟧ ⤳[under] #(go_string_ltb x y);

  #[global] le_string (x y : go_string) ::
    ⟦GoOp GoLe go.string, (#x, #y)⟧ ⤳[under] #(go_string_leb x y);

  #[global] gt_string (x y : go_string) ::
    ⟦GoOp GoGt go.string, (#x, #y)⟧ ⤳[under] #(go_string_ltb y x);

  #[global] ge_string (x y : go_string) ::
    ⟦GoOp GoGe go.string, (#x, #y)⟧ ⤳[under] #(go_string_leb y x);
}.
End defs.
End go.
