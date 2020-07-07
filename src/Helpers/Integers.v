From stdpp Require Import decidable countable.
From coqutil Require Import Datatypes.HList.
From coqutil.Z Require Import BitOps.
From coqutil.Word Require Naive.
From coqutil.Word Require Export Interface Properties.
From Perennial Require Import Helpers.LittleEndian.

Open Scope Z_scope.

Instance word_inhabited width (word: Interface.word width) : Inhabited word.
Proof.
  constructor.
  exact (word.of_Z 0).
Qed.

Record u64_rep := Word64 { u64_car : Naive.word64 }.
Record u32_rep := Word32 { u32_car : Naive.word32 }.
Record u8_rep := Word8 { u8_car : Naive.word8 }.

Definition width64_ok : 0 < 64 := eq_refl.
Definition width32_ok : 0 < 32 := eq_refl.
Definition width8_ok : 0 < 8 := eq_refl.

Hint Resolve width64_ok width32_ok width8_ok : typeclass_instances.

Opaque Naive.word.


Module u64_instance.
  Import Interface.word.
  Notation "'lift1' f" := (fun w => Word64 (f w.(u64_car))) (at level 10, only parsing).
  Notation "'lift2' f" := (fun w1 w2 => Word64 (f w1.(u64_car) w2.(u64_car))) (at level 10, only parsing).
  Instance u64 : word 64 :=
    {|
      rep := u64_rep;
      unsigned w := unsigned w.(u64_car);
      signed w := signed (w.(u64_car));
      of_Z z := Word64 (of_Z z);
      add := lift2 add;
      sub := lift2 sub;
      opp := lift1 opp;
      or := lift2 or;
      and := lift2 and;
      xor := lift2 xor;
      not := lift1 not;
      ndn := lift2 ndn;
      mul := lift2 mul;
      mulhss := lift2 mulhss;
      mulhsu := lift2 mulhsu;
      mulhuu := lift2 mulhuu;
      divu := lift2 divu;
      divs := lift2 divs;
      modu := lift2 modu;
      mods := lift2 mods;
      slu := lift2 slu;
      sru := lift2 sru;
      srs := lift2 srs;
      eqb w1 w2 := eqb w1.(u64_car) w2.(u64_car);
      ltu w1 w2 := ltu w1.(u64_car) w2.(u64_car);
      lts w1 w2 := lts w1.(u64_car) w2.(u64_car);
      sextend width' := lift1 (sextend width');
    |}.

  Global Instance u64_word_ok : word.ok u64.
  Proof.
    destruct (_ : word.ok (Naive.word 64)).
    constructor; simpl; eauto.
    - intros []; simpl.
      rewrite of_Z_unsigned; auto.
  Qed.

End u64_instance.

Module u32_instance.
  Import Interface.word.
  Notation "'lift1' f" := (fun w => Word32 (f w.(u32_car))) (at level 10, only parsing).
  Notation "'lift2' f" := (fun w1 w2 => Word32 (f w1.(u32_car) w2.(u32_car))) (at level 10, only parsing).
  Instance u32 : word 32 :=
    {|
      rep := u32_rep;
      unsigned w := unsigned w.(u32_car);
      signed w := signed (w.(u32_car));
      of_Z z := Word32 (of_Z z);
      add := lift2 add;
      sub := lift2 sub;
      opp := lift1 opp;
      or := lift2 or;
      and := lift2 and;
      xor := lift2 xor;
      not := lift1 not;
      ndn := lift2 ndn;
      mul := lift2 mul;
      mulhss := lift2 mulhss;
      mulhsu := lift2 mulhsu;
      mulhuu := lift2 mulhuu;
      divu := lift2 divu;
      divs := lift2 divs;
      modu := lift2 modu;
      mods := lift2 mods;
      slu := lift2 slu;
      sru := lift2 sru;
      srs := lift2 srs;
      eqb w1 w2 := eqb w1.(u32_car) w2.(u32_car);
      ltu w1 w2 := ltu w1.(u32_car) w2.(u32_car);
      lts w1 w2 := lts w1.(u32_car) w2.(u32_car);
      sextend width' := lift1 (sextend width');
    |}.

  Global Instance u32_word_ok : word.ok u32.
  Proof.
    destruct (_ : word.ok (Naive.word 32)).
    constructor; simpl; eauto.
    - intros []; simpl.
      rewrite of_Z_unsigned; auto.
  Qed.

End u32_instance.

Module u8_instance.
  Import Interface.word.
  Notation "'lift1' f" := (fun w => Word8 (f w.(u8_car))) (at level 10, only parsing).
  Notation "'lift2' f" := (fun w1 w2 => Word8 (f w1.(u8_car) w2.(u8_car))) (at level 10, only parsing).
  Instance u8 : word 8 :=
    {|
      rep := u8_rep;
      unsigned w := unsigned w.(u8_car);
      signed w := signed (w.(u8_car));
      of_Z z := Word8 (of_Z z);
      add := lift2 add;
      sub := lift2 sub;
      opp := lift1 opp;
      or := lift2 or;
      and := lift2 and;
      xor := lift2 xor;
      not := lift1 not;
      ndn := lift2 ndn;
      mul := lift2 mul;
      mulhss := lift2 mulhss;
      mulhsu := lift2 mulhsu;
      mulhuu := lift2 mulhuu;
      divu := lift2 divu;
      divs := lift2 divs;
      modu := lift2 modu;
      mods := lift2 mods;
      slu := lift2 slu;
      sru := lift2 sru;
      srs := lift2 srs;
      eqb w1 w2 := eqb w1.(u8_car) w2.(u8_car);
      ltu w1 w2 := ltu w1.(u8_car) w2.(u8_car);
      lts w1 w2 := lts w1.(u8_car) w2.(u8_car);
      sextend width' := lift1 (sextend width');
    |}.

  Global Instance u8_word_ok : word.ok u8.
  Proof.
    destruct (_ : word.ok (Naive.word 8)).
    constructor; simpl; eauto.
    - intros []; simpl.
      rewrite of_Z_unsigned; auto.
  Qed.

End u8_instance.

Global Opaque u64_instance.u64 u32_instance.u32 u8_instance.u8.

(* these are identity coercions to make notation.v work out (this is still black
magic to me) *)

Global SubClass u64 := @word.rep _ u64_instance.u64.
Global SubClass u32 := @word.rep _ u32_instance.u32.
Global SubClass u8 := @word.rep _ u8_instance.u8.

(* TODO: ideally this is rarely or never used, but it's useful for backwards
compatibility while we're still experimenting *)
Notation byte := u8 (only parsing).

Definition U64 (x:Z) : u64 := word.of_Z x.
Definition U32 (x:Z) : u32 := word.of_Z x.
Definition U8 (x:Z)  : u8  := word.of_Z x.

Instance word_eq_dec {width} (word: word width) {word_ok: word.ok word} : EqDecision word.
Proof.
  hnf; intros; hnf.
  pose proof (word.eqb_spec x y).
  destruct (word.eqb x y);
    [ left | right]; inversion H; auto.
Defined.

Instance u64_eq_dec : EqDecision u64 := _.
Instance u32_eq_dec : EqDecision u32 := _.
Instance u8_eq_dec : EqDecision u8 := _.

Instance int_val_inj `(word: Interface.word width) {word_ok: word.ok word} : Inj eq eq word.unsigned.
Proof.
  intros x1 x2.
  intros.
  apply word.unsigned_inj in H; auto.
Qed.

Instance byte_eq_dec : EqDecision byte.
Proof. solve_decision. Defined.

Instance word_countable `(word: Interface.word width) {word_ok: word.ok word} : Countable word.
Proof.
  apply (inj_countable'
           word.unsigned
           (fun z => word.of_Z z)); intros.
  by rewrite word.of_Z_unsigned.
Qed.

Instance u64_countable : Countable u64 := _.
Instance u32_countable : Countable u32 := _.
Instance u8_countable : Countable byte := _.

(* int and the u64_through* theorems are for backwards compatibility *)

Module int.
  Notation val := word.unsigned.

  Notation nat x := (Z.to_nat (word.unsigned x)).
End int.

Theorem u64_Z_through_nat (x:u64) : Z.of_nat (int.nat x) = int.val x.
Proof.
  rewrite Z2Nat.id; auto.
  pose proof (word.unsigned_range x); lia.
Qed.

Theorem u64_nat_through_Z (x:u64) : Z.to_nat (int.val x) = int.nat x.
Proof.
  reflexivity.
Qed.

Theorem u8_nat_through_Z (x:u8) : Z.to_nat (int.val x) = int.nat x.
Proof.
  reflexivity.
Qed.

(* should maybe convert this into an explicit match on ints at some point *)
Definition u8_to_ascii (x:byte) : Ascii.ascii := Ascii.ascii_of_nat (int.nat x).

(* conversion to string *)
Definition u8_to_string (x:byte) : String.string := String.String (u8_to_ascii x) String.EmptyString.

(* conversions up *)
Definition u8_to_u32 (x:byte) : u32 := U32 (int.val x).
Definition u8_to_u64 (x:byte) : u64 := U64 (int.val x).
Definition u32_to_u64 (x:u32) : u64 := U64 (int.val x).

(* conversions down *)
Definition u32_from_u64 (x:u64) : u32 := U32 (int.val x).
Definition u8_from_u64 (x:u64) : byte := U8 (int.val x).
Definition u8_from_u32 (x:u32) : byte := U8 (int.val x).

Theorem wrap_small `{word: Interface.word width} {ok: word.ok word} (x:Z) :
  0 <= x < 2^width ->
  word.wrap x = x.
Proof.
  unfold word.wrap; intros.
  rewrite Zmod_small; auto.
Qed.

Theorem u32_to_u64_val x : int.val (u32_to_u64 x) = int.val x.
Proof.
  unfold u32_to_u64, U64.
  rewrite word.unsigned_of_Z.
  rewrite wrap_small; auto.
  pose proof (word.unsigned_range x); lia.
Qed.

Theorem u32_from_u64_val (x: u64) : int.val x < 2^32 ->
                                    int.val (u32_from_u64 x) = int.val x.
Proof.
  unfold u32_from_u64, U32; intros.
  rewrite word.unsigned_of_Z.
  rewrite wrap_small; auto.
  pose proof (word.unsigned_range x); lia.
Qed.

Theorem tuple_to_list_length A n (t: tuple A n) :
  length (tuple.to_list t) = n.
Proof.
  induction n; simpl; auto.
Qed.

(* these make sure that s/64/32/ changes 64-bit code to 32-bit code *)
Notation u64_bytes := 8%nat (only parsing).
Notation u32_bytes := 4%nat (only parsing).

(** 64-bit encoding *)
Definition u64_le (x: u64) : list byte :=
  let n := word.unsigned x in
  let t := split (byte:=u8_instance.u8) u64_bytes n in
  tuple.to_list t.

Definition le_to_u64 (l: list byte) : u64.
Proof.
  refine (word.of_Z _).
  set (t := tuple.of_list l).
  exact (combine (byte:=u8_instance.u8) _ t).
Defined.

Theorem u64_le_length x : length (u64_le x) = u64_bytes.
Proof.
  reflexivity.
Qed.

Theorem tuple_of_to_list_u64 A (t: tuple A u64_bytes) :
  tuple.of_list (tuple.to_list t) = t.
Proof.
  unfold tuple in t.
  repeat match goal with
         | [ t: hlist _ |- _ ] => destruct t
         end.
  f_equal.
Qed.

Theorem u64_le_to_word : forall x,
    le_to_u64 (u64_le x) = x.
Proof.
  intros x; simpl.
  unfold le_to_u64, u64_le.
  f_equal.
  rewrite tuple_of_to_list_u64.
  rewrite combine_split.
  change (u64_bytes%nat * 8) with 64.
  rewrite word.wrap_unsigned by lia.
  by rewrite word.of_Z_unsigned.
Qed.
(* end 64-bit code *)

(* this block is a copy-paste of the above with s/64/32/ *)
(** 32-bit encoding *)
Definition u32_le (x: u32) : list byte :=
  let n := word.unsigned x in
  let t := split (byte:=u8_instance.u8) u32_bytes n in
  tuple.to_list t.

Definition le_to_u32 (l: list byte) : u32.
Proof.
  refine (word.of_Z _).
  set (t := tuple.of_list l).
  exact (combine (byte:=u8_instance.u8) _ t).
Defined.

Theorem u32_le_length x : length (u32_le x) = u32_bytes.
Proof.
  reflexivity.
Qed.

Theorem tuple_of_to_list_u32 A (t: tuple A u32_bytes) :
  tuple.of_list (tuple.to_list t) = t.
Proof.
  unfold tuple in t.
  repeat match goal with
         | [ t: hlist _ |- _ ] => destruct t
         end.
  f_equal.
Qed.

Theorem u32_le_to_word : forall x,
    le_to_u32 (u32_le x) = x.
Proof.
  intros x; simpl.
  unfold le_to_u32, u32_le.
  f_equal.
  rewrite tuple_of_to_list_u32.
  rewrite combine_split.
  change (u32_bytes%nat * 8) with 32.
  rewrite word.wrap_unsigned by lia.
  by rewrite word.of_Z_unsigned.
Qed.
(* end 32-bit code *)

Lemma combine_unfold n b (t: HList.tuple byte n) :
  combine (S n) {| PrimitivePair.pair._1 := b; PrimitivePair.pair._2 := t |} =
  Z.lor (int.val b) (combine n t ≪ 8).
Proof.
  reflexivity.
Qed.

Theorem Zmod_small_bits_high p z n :
  0 <= z < 2 ^ p ->
  0 <= p <= n ->
  Z.testbit z n = false.
Proof.
  intros.
  rewrite <- (Z.mod_small z (2^p)) by lia.
  rewrite Z.mod_pow2_bits_high; auto; lia.
Qed.

Theorem combine_bound n t :
  0 <= combine n t < 2 ^ (8 * n).
Proof.
  induction n; simpl.
  - cbv; split; congruence.
  - destruct t as [b t].
    let T := type of t in change T with (HList.tuple byte n) in *.
    rewrite combine_unfold.
    rewrite BitOps.or_to_plus.
    { pose proof (IHn t).
      pose proof (word.unsigned_range b).
      split.
      { unfold Z.shiftl; simpl. lia. }
      { unfold Z.shiftl; simpl.
        replace (2 ^ (8 * S n)) with (2^8 * 2 ^ (8 * n)); try lia.
        replace (8 * S n) with (8 + 8*n) by lia.
        rewrite <- Z.pow_add_r; lia. } }
    pose proof (word.unsigned_range b).
    apply Z.bits_inj.
    unfold Z.eqf; intros.
    rewrite Z.land_spec.
    rewrite Z.bits_0.
    destruct (decide (n0 < 0)).
    { rewrite Z.testbit_neg_r; [ | lia ].
      rewrite andb_false_l; auto.
    }
    destruct (decide (n0 < 8)).
    + rewrite Z.shiftl_spec_low; [ | lia ].
      rewrite andb_false_r; auto.
    + rewrite (Zmod_small_bits_high 8); [ | lia | lia ].
      rewrite andb_false_l; auto.
Qed.

Lemma le_to_u64_le bs :
  length bs = 8%nat ->
  u64_le (le_to_u64 bs) = bs.
Proof.
  intros.
  do 8 (destruct bs; [ simpl in H; lia | ]).
  destruct bs; [ clear H | simpl in H; lia ].
  unfold u64_le, le_to_u64.
  rewrite word.unsigned_of_Z.
  rewrite wrap_small.
  { rewrite LittleEndian.split_combine.
    simpl; auto. }
  cbv [length].
  match goal with
  | |- context[LittleEndian.combine ?n ?t] =>
    pose proof (combine_bound n t)
  end.
  exact H.
Qed.

Lemma unsigned_U64 z : int.val (U64 z) = word.wrap (word:=u64_instance.u64) z.
Proof.
  unfold U64; rewrite word.unsigned_of_Z; auto.
Qed.

Lemma unsigned_U32 z : int.val (U32 z) = word.wrap (word:=u32_instance.u32) z.
Proof.
  unfold U32; rewrite word.unsigned_of_Z; auto.
Qed.

Lemma unsigned_U64_0 : int.val (U64 0) = 0.
Proof.
  reflexivity.
Qed.

Lemma unsigned_U32_0 : int.val (U32 0) = 0.
Proof.
  reflexivity.
Qed.

Create HintDb word.

Ltac word_cleanup :=
  repeat autounfold with word in *;
  try match goal with
      | |- @eq u64 _ _ => apply word.unsigned_inj
      | |- @eq u32 _ _ => apply word.unsigned_inj
      | |- @eq u8 _ _ => apply word.unsigned_inj
      end;
  (* can't replace this with [autorewrite], probably because typeclass inference
  isn't the same *)
  rewrite ?word.unsigned_add, ?word.unsigned_sub,
  ?word.unsigned_divu_nowrap, ?word.unsigned_modu_nowrap,
  ?unsigned_U64_0, ?unsigned_U32_0,
  ?word.unsigned_of_Z, ?word.of_Z_unsigned, ?unsigned_U64, ?unsigned_U32;
  try autorewrite with word;
  repeat match goal with
         | [ H: context[word.unsigned (U64 (Zpos ?x))] |- _ ] => change (int.val (Zpos x)) with (Zpos x) in *
         | [ |- context[word.unsigned (U64 (Zpos ?x))] ] => change (int.val (Zpos x)) with (Zpos x)
         | [ H: context[word.unsigned (U32 (Zpos ?x))] |- _ ] => change (int.val (U32 (Zpos x))) with (Zpos x) in *
         | [ |- context[word.unsigned (U32 (Zpos ?x))] ] => change (int.val (U32 (Zpos x))) with (Zpos x)
         end;
  repeat match goal with
         | [ |- context[int.val ?x] ] =>
           lazymatch goal with
           | [ H': 0 <= int.val x < 2^64 |- _ ] => fail
           | [ H': 0 <= int.val x <= 2^64 |- _ ] => fail (* TODO: should be unnecessary *)
           | _ => pose proof (word.unsigned_range x)
           end
         | [ H: context[int.val ?x] |- _ ] =>
           lazymatch goal with
           | [ H': 0 <= int.val x < 2^64 |- _ ] => fail
           | [ H': 0 <= int.val x <= 2^64 |- _ ] => fail (* TODO: should be unnecessary *)
           | _ => pose proof (word.unsigned_range x)
           end
         end;
  repeat match goal with
         | |- context[@word.wrap _ ?word ?ok ?z] =>
           rewrite (@wrap_small _ word ok z) by lia
         | |- context[Z.of_nat (Z.to_nat ?z)] =>
           rewrite (Z2Nat.id z) by lia
         end;
  try lia.

Ltac word := solve [ word_cleanup ].

(* FIXME: move upstream to std++ *)
Lemma elem_of_seq start sz :
  ∀ i, i ∈ seq start sz ↔ (start ≤ i < start + sz)%nat.
Proof.
  intros i.
  rewrite elem_of_list_In, in_seq.
  auto.
Qed.

(* FIXME: move upstream to std++ *)
Lemma elem_of_seqZ start sz :
  ∀ i, i ∈ seqZ start sz ↔ start ≤ i < start + sz.
Proof.
  intros i.
  unfold seqZ.
  rewrite elem_of_list_fmap.
  setoid_rewrite elem_of_seq.
  split; intros.
  - destruct H as [y [-> Hin]]; lia.
  - exists (Z.to_nat (i - start)); lia.
Qed.

(* FIXME: move upstream to std++ *)
Lemma NoDup_fmap_2_strong {A B} (f : A → B) (l : list A) :
  (∀ x y, x ∈ l → y ∈ l → f x = f y → x = y) →
  NoDup l →
  NoDup (f <$> l).
Proof.
  intros Hinj.
  induction 1; simpl; constructor; cycle 1.
  { apply IHNoDup. intros ????. apply Hinj; apply elem_of_list_further; done. }
  rewrite elem_of_list_fmap. intros [y [Hxy ?]].
  apply Hinj in Hxy; [by subst|..].
  - apply elem_of_list_here.
  - apply elem_of_list_further. done.
Qed.

Theorem val_u32 z :
  0 <= z < 2 ^ 32 ->
  int.val (U32 z) = z.
Proof.
  intros.
  unfold U32.
  rewrite word.unsigned_of_Z.
  rewrite wrap_small; auto.
Qed.

Theorem val_u64 z :
  0 <= z < 2 ^ 64 ->
  int.val (U64 z) = z.
Proof.
  intros.
  unfold U64.
  rewrite word.unsigned_of_Z.
  rewrite wrap_small; auto.
Qed.

Lemma seq_U64_NoDup (m len : Z) :
  (0 ≤ m)%Z →
  (m+len < 2^64)%Z →
  NoDup (U64 <$> seqZ m len).
Proof.
  intros Hlb Hub. apply NoDup_fmap_2_strong; cycle 1.
  { apply NoDup_seqZ. }
  Set Printing Coercions. (* This is impossible to work on otherwise... *)
  clear- Hlb Hub. intros x y Hx%elem_of_seqZ Hy%elem_of_seqZ Heq.
  rewrite <-(val_u64 x), <-(val_u64 y).
  - by rewrite Heq.
  - word.
  - word.
Qed.
