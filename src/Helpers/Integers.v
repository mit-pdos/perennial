From stdpp Require Import decidable countable.
From coqutil Require Import Datatypes.HList.
From coqutil.Word Require Naive.
From coqutil.Word Require Export Interface.
From coqutil.Word Require Import Properties LittleEndian.

Open Scope Z_scope.

Record u64 := Word64 { u64_car :> Naive.word64 }.
Record u32 := Word32 { u32_car :> Naive.word32 }.
Record byte := Word8 { u8_car :> Naive.word8 }.

Definition width64_ok : 0 < 64 := eq_refl.
Definition width32_ok : 0 < 32 := eq_refl.
Definition width8_ok : 0 < 8 := eq_refl.

Hint Resolve width64_ok width32_ok width8_ok : typeclass_instances.

Opaque Naive.word.

Module u64_instance.
  Import Interface.word.
  Notation "'lift1' f" := (fun w => Word64 (f w)) (at level 10, only parsing).
  Notation "'lift2' f" := (fun w1 w2 => Word64 (f w1 w2)) (at level 10, only parsing).
  Instance u64_word : word 64 :=
    {|
      rep := u64;
      unsigned := unsigned;
      signed := signed;
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

      eqb w1 w2 := eqb w1 w2;
      ltu w1 w2 := ltu w1 w2;
      lts w1 w2 := lts w1 w2;

      sextend width' := lift1 (sextend width');
    |}.

  Global Instance u64_word_ok : word.ok u64_word.
  Proof.
    destruct (_ : word.ok (Naive.word 64)).
    constructor; simpl; eauto.
    - intros []; simpl.
      rewrite of_Z_unsigned; auto.
  Qed.

End u64_instance.
Import u64_instance.

Module u32_instance.
  Import Interface.word.
  Notation "'lift1' f" := (fun w => Word32 (f w)) (at level 10, only parsing).
  Notation "'lift2' f" := (fun w1 w2 => Word32 (f w1 w2)) (at level 10, only parsing).
  Instance u32_word : word 32 :=
    {|
      rep := u32;
      unsigned := unsigned;
      signed := signed;
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

      eqb w1 w2 := eqb w1 w2;
      ltu w1 w2 := ltu w1 w2;
      lts w1 w2 := lts w1 w2;

      sextend width' := lift1 (sextend width');
    |}.

  Global Instance u32_word_ok : word.ok u32_word.
  Proof.
    destruct (_ : word.ok (Naive.word 32)).
    constructor; simpl; eauto.
    - intros []; simpl.
      rewrite of_Z_unsigned; auto.
  Qed.
End u32_instance.
Import u32_instance.

Module u8_instance.
  Import Interface.word.
  Notation "'lift1' f" := (fun w => Word8 (f w)) (at level 10, only parsing).
  Notation "'lift2' f" := (fun w1 w2 => Word8 (f w1 w2)) (at level 10, only parsing).
  Instance u8_word : word 8 :=
    {|
      rep := byte;
      unsigned := unsigned;
      signed := signed;
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

      eqb w1 w2 := eqb w1 w2;
      ltu w1 w2 := ltu w1 w2;
      lts w1 w2 := lts w1 w2;

      sextend width' := lift1 (sextend width');
    |}.

  Global Instance u8_word_ok : word.ok u8_word.
  Proof.
    destruct (_ : word.ok (Naive.word 8)).
    constructor; simpl; eauto.
    - intros []; simpl.
      rewrite of_Z_unsigned; auto.
  Qed.

End u8_instance.
Import u8_instance.

(* does this make sense? *)
(*
Canonical Structure u64_word.
Canonical Structure u32_word.
*)

Definition U64 (x:Z) : u64 := word.of_Z (word:=u64_word) x.
Definition U32 (x:Z) : u32 := word.of_Z (word:=u32_word) x.
Definition U8 (x:Z) : byte := word.of_Z (word:=u8_word) x.

Instance word_eq_dec {width} (word: word width) {word_ok: word.ok word} : EqDecision word.
Proof.
  hnf; intros; hnf.
  pose proof (word.eqb_spec x y).
  destruct (word.eqb x y);
    [ left | right]; inversion H; auto.
Defined.

Instance u64_eq_dec : EqDecision u64 := word_eq_dec u64_word.
Instance u32_eq_dec : EqDecision u32 := word_eq_dec u32_word.
Instance u8_eq_dec : EqDecision byte := word_eq_dec u8_word.

Instance byte_eq_dec : EqDecision byte.
Proof. solve_decision. Defined.

Instance word_countable {width} (word: word.word width) {word_ok: word.ok word} : Countable word.
Proof.
  apply (inj_countable'
           word.unsigned
           (fun z => word.of_Z z)); intros.
  by rewrite word.of_Z_unsigned.
Qed.

Instance u64_countable : Countable u64.
Proof. apply (word_countable u64_word). Qed.

Instance u32_countable : Countable u32.
Proof. apply (word_countable u32_word). Qed.

Instance u8_countable : Countable byte.
Proof. apply (word_countable u8_word). Qed.

(* int and the u64_through* theorems are for backwards compatibility *)

Module int.
  Notation val := word.unsigned.

  Definition nat {width} {word: word.word width} (x: word) :=
    Z.to_nat (word.unsigned x).
End int.

Theorem u64_Z_through_nat (x:u64) : Z.of_nat (int.nat x) = int.val x.
Proof.
  unfold int.nat; intros.
  rewrite Z2Nat.id; auto.
  pose proof (word.unsigned_range x); lia.
Qed.

Theorem u64_nat_through_Z (x:u64) : Z.to_nat (int.val x) = int.nat x.
Proof.
  unfold int.nat; intros.
  reflexivity.
Qed.

(* conversions up *)
Definition u8_to_u32 (x:byte) : u32 := U32 (int.val x).
Definition u8_to_u64 (x:byte) : u64 := U64 (int.val x).
Definition u32_to_u64 (x:u32) : u64 := U64 (int.val x).

(* conversions down *)
Definition u32_from_u64 (x:u64) : u32 := U32 (int.val x).
Definition u8_from_u64 (x:u64) : byte := U8 (int.val x).
Definition u8_from_u32 (x:u32) : byte := U8 (int.val x).

Theorem u32_to_u64_val x : int.val (u32_to_u64 x) = int.val x.
Proof.
  simpl.
  rewrite word.unsigned_of_Z.
  unfold word.wrap.
  pose proof (word.unsigned_range x).
  rewrite Z.mod_small by lia; auto.
Qed.

Theorem u32_from_u64_val (x: u64) : int.val x < 2^32 ->
                                    int.val (u32_from_u64 x) = int.val x.
Proof.
  simpl; intros.
  rewrite word.unsigned_of_Z.
  unfold word.wrap.
  pose proof (word.unsigned_range x).
  rewrite Z.mod_small by lia; auto.
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
  let n := word.unsigned x.(u64_car) in
  let t := split (byte:=Naive.word8) u64_bytes n in
  let words := tuple.to_list t in
  map Word8 words.

Definition le_to_u64 (l: list byte) : u64.
Proof.
  refine (Word64 (word.of_Z _)).
  set (t := tuple.of_list (map u8_car l)).
  exact (combine (byte:=Naive.word8) _ t).
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
  intros [x]; simpl.
  unfold le_to_u64, u64_le.
  f_equal.
  cbv [u64_car].
  rewrite map_map, map_id.
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
  let n := word.unsigned x.(u32_car) in
  let t := split (byte:=Naive.word8) u32_bytes n in
  let words := tuple.to_list t in
  map Word8 words.

Definition le_to_u32 (l: list byte) : u32.
Proof.
  refine (Word32 (word.of_Z _)).
  set (t := tuple.of_list (map u8_car l)).
  exact (combine (byte:=Naive.word8) _ t).
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
  intros [x]; simpl.
  unfold le_to_u32, u32_le.
  f_equal.
  cbv [u32_car].
  rewrite map_map, map_id.
  rewrite tuple_of_to_list_u32.
  rewrite combine_split.
  change (u32_bytes%nat * 8) with 32.
  rewrite word.wrap_unsigned by lia.
  by rewrite word.of_Z_unsigned.
Qed.
(* end 32-bit code *)

Eval cbv [u32_le map split tuple.to_list] in u32_le.
Eval cbv [le_to_u32 map combine length tuple.of_list PrimitivePair.pair._1 PrimitivePair.pair._2]
  in (fun v1 v2 v3 v4 => le_to_u32 [v1;v2;v3;v4]).
