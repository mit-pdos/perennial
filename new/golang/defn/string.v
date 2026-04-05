From New.golang.defn Require Export loop assume predeclared.
From New.code.github_com.mit_pdos.perennial.goose.model Require Import strings.

Module go.
Section defs.
Context {ext : ffi_syntax}.
Context {go_lctx : GoLocalContext} {go_gctx : GoGlobalContext}.

Global Instance w8_lexico : Lexico w8 := (λ x y, uint.Z x < uint.Z y).

Global Instance : TrichotomyT (lexico (A:=w8)).
Proof.
  intros x y. destruct (uint.Z x ?= uint.Z y) eqn:Heq.
  - apply Z.compare_eq in Heq. left. right. word.
  - left. left. rewrite (Z.compare_lt_iff (uint.Z x) (uint.Z y)) in Heq.
    rewrite /lexico /= /w8_lexico //.
  - right. rewrite (Z.compare_gt_iff (uint.Z x) (uint.Z y)) in Heq.
    rewrite /lexico /= /w8_lexico //.
Defined. (* for computing bool_decide *)

Global Instance : StrictOrder (lexico (A:=w8)).
Proof.
  constructor.
  - intros x. rewrite /lexico /w8_lexico /complement. intros H. lia.
  - intros x y z. rewrite /lexico /w8_lexico. lia.
Qed.

Definition go_string_lt : go_string → go_string → Prop := lexico.

Instance : StrictOrder go_string_lt.
Proof. apply _. Qed.

Example go_string_ltb_examples :
  ¬ go_string_lt "" "" ∧
  go_string_lt "" "a" ∧
  ¬ go_string_lt "a" "" ∧
  ¬ go_string_lt "ab" "a" ∧
  go_string_lt "ab" "b".
Proof.
  split_and!; eapply bool_decide_unpack; done.
Qed.

Definition go_string_le (x y : go_string) : Prop :=
  x = y ∨ go_string_lt x y.

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
    ⟦GoOp GoLt go.string, (#x, #y)⟧ ⤳[under] #(bool_decide (go_string_lt x y));

  #[global] le_string (x y : go_string) ::
    ⟦GoOp GoLe go.string, (#x, #y)⟧ ⤳[under] #(bool_decide (go_string_le x y));

  #[global] gt_string (x y : go_string) ::
    ⟦GoOp GoGt go.string, (#x, #y)⟧ ⤳[under] #(bool_decide (go_string_lt y x));

  #[global] ge_string (x y : go_string) ::
    ⟦GoOp GoGe go.string, (#x, #y)⟧ ⤳[under] #(bool_decide (go_string_le y x));
}.
End defs.
End go.
