From Coq Require Import FunctionalExtensionality.
From Coq Require Import micromega.Lia.
From RecoveryRefinement Require Import Helpers.MachinePrimitives.
From RecoveryRefinement Require Import Database.Common.

From Tactical Require Import ProofAutomation.

From Classes Require Import EqualDec.
Import EqualDecNotation.

Import BSNotations UIntNotations.

Definition Decoder T := ByteString -> option (T * uint64).

Definition decodeBind T1 T2 (dec1: Decoder T1) (dec2: T1 -> Decoder T2) : Decoder T2 :=
  fun bs => match dec1 bs with
         | Some (v1, n) => match dec2 v1 (BS.drop n bs) with
                          | Some (v2, n2) => Some (v2, (n + n2)%u64)
                          | None => None
                          end
         | None => None
         end.

Theorem decodeBind_assoc T1 T2 T3
        (dec1: Decoder T1)
        (dec2: T1 -> Decoder T2)
        (dec3: T2 -> Decoder T3) :
  decodeBind (decodeBind dec1 dec2) dec3 =
  decodeBind dec1 (fun x => decodeBind (dec2 x) dec3).
Proof.
  extensionality x.
  unfold decodeBind; simpl.
  destruct matches; subst; auto;
    rewrite ?drop_drop, ?add_assoc in *;
    try congruence.
Qed.

Definition decodeRet T (v:T) : Decoder T :=
  fun _ => Some (v, fromNum 0).

Definition decodeFail {T} : Decoder T :=
  fun _ => None.

Definition decodeFinished : Decoder unit :=
  fun bs => match compare (BS.length bs) 0 with
         | Gt => None
         | _ => Some (tt, 0%u64)
         end.

Definition decodeFixed (n:uint64) : Decoder ByteString :=
  fun bs => if compare n (BS.length bs) == Gt
         then None
         else Some (BS.take n bs, n).

Definition decodeMap A B (f: A -> B) (dec: Decoder A) : Decoder B :=
  fun bs => match dec bs with
         | Some (v, n) => Some (f v, n)
         | None => None
         end.

Theorem decodeMap_bind T1 T2 T3 f dec rx bs :
  @decodeBind T1 T3 (decodeMap f dec) rx bs =
  @decodeBind T2 T3 dec (fun x => rx (f x)) bs.
Proof.
  unfold decodeBind, decodeMap; simpl.
  destruct matches.
Qed.

Module DecodeNotations.
  (* Declare Scope decode_bind_scope. *)
  Delimit Scope decode_bind_scope with dec.
  Notation "x <- a ;; b" := (decodeBind a (fun x => b))
                             (at level 20, a at level 100, b at level 200, right associativity)
                           : decode_bind_scope.
  Notation "'ret' x" := (decodeRet x) (at level 0) : decode_bind_scope.
  Notation "'done'" := (decodeFinished) (at level 0) : decode_bind_scope.
  Infix "<$>" := decodeMap (at level 61, left associativity) : decode_bind_scope.
End DecodeNotations.

Class Encodable (T: Type) :=
  { encode : T -> ByteString;
    decode : Decoder T;
  }.

Class EncodableCorrect T (enc:Encodable T) :=
  { decode_encode : forall x bs',
      decode (encode x ++ bs')%bs = Some (x, BS.length (encode x));
    decode_prefix : forall x n,
        n.(toNum) < (BS.length (encode x)).(toNum) ->
        decode (BS.take n (encode x)) = None;
  }.

(* only for this file's proofs make formats explicit *)
Arguments encode {T} fmt : rename.
Arguments decode {T} fmt : rename.
Arguments decode_encode {T} fmt {fmt_ok} : rename.
Arguments decode_prefix {T} fmt {fmt_ok} : rename.

Import DecodeNotations.
Local Open Scope bs.
Local Open Scope dec.

Theorem decodeBind_encode_first T1 T2 fmt1 {fmt1_ok:EncodableCorrect fmt1} (rx: T1 -> Decoder T2) :
  forall x bs',
    decodeBind fmt1.(decode) rx (fmt1.(encode) x ++ bs') =
    match rx x bs' with
    | Some (v, n) => Some (v, BS.length (fmt1.(encode) x) + n)%u64
    | None => None
    end.
Proof.
  unfold decodeBind; simpl; intros.
  rewrite fmt1.(decode_encode).
  rewrite drop_app_exact; auto.
Qed.

Instance product_fmt
         T1 T2 (fmt1: Encodable T1) (fmt2: Encodable T2)
  : Encodable (T1*T2).
Proof.
  refine {| encode '(x1, x2) := fmt1.(encode) x1 ++ fmt2.(encode) x2;
            decode :=
              v1 <- fmt1.(decode);;
                 v2 <- fmt2.(decode);;
                 ret (v1, v2); |}.
Defined.

Hint Rewrite decodeBind_assoc decodeMap_bind : dec.
Hint Rewrite append_assoc app_length decodeBind_encode_first : dec.

Ltac solve_num_eq :=
  match goal with
  | |- @eq uint64 ?x ?y =>
    apply toNum_inj; simpl; lia
  | |- _ => simpl; lia
  end.

Ltac simplify :=
  autorewrite with dec in *;
  repeat match goal with
         | |- EncodableCorrect _ => typeclasses eauto with core typeclass_instances
         | |- Some (_, ?x) = Some (_, ?x) => f_equal
         | |- Some (_, ?x) = Some (_, ?y) => replace x with y by solve_num_eq
         | |- ?x = ?x => reflexivity
         | _ => progress cbn [decodeRet decodeBind]
         end.

Opaque BS.length.

Definition take_app_split n bs1 bs2 :
  {n.(toNum) < (BS.length bs1).(toNum) /\
   BS.take n (bs1 ++ bs2) = BS.take n bs1}
  + {n.(toNum) >= (BS.length bs1).(toNum) /\
     BS.take n (bs1 ++ bs2) = bs1 ++ BS.take (n - BS.length bs1)%u64 bs2}.
Proof.
  destruct (numbers.nat_lt_dec n.(toNum) (BS.length bs1).(toNum));
    [ left | right ].
  intuition eauto.
  rewrite take_app_first by lia; eauto.
  (intuition eauto); try solve_num_eq.
  rewrite take_app_second by solve_num_eq; auto.
Qed.

Theorem decodeBind_prefix n `(enc:@EncodableCorrect T fmt) (x:T) T' rx bs' :
  (n.(toNum) >= (BS.length (fmt.(encode) x)).(toNum) ->
   rx x (BS.take (n - BS.length (fmt.(encode) x))%u64 bs') = None) ->
  @decodeBind T T' fmt.(decode) rx (BS.take n (fmt.(encode) x ++ bs')) = None.
Proof.
  intros Hngt.
  destruct (take_app_split n (fmt.(encode) x) bs');
    propositional; simpl.
  - rewrite H0.
    unfold decodeBind; simpl.
    rewrite fmt.(decode_prefix); auto.
  - rewrite take_app_second by solve_num_eq.
    rewrite decodeBind_encode_first; eauto.
    rewrite Hngt; auto.
Qed.

Theorem decodeBind_prefix_first `(enc:@EncodableCorrect T fmt)
        T' rx bs :
  fmt.(decode) bs = None ->
  @decodeBind T T' fmt.(decode) rx bs = None.
Proof.
  intros.
  unfold decodeBind; simpl.
  rewrite H; auto.
Qed.

Instance product_fmt_ok
         `(fmt1_ok: @EncodableCorrect T1 fmt1) `(fmt2_ok: @EncodableCorrect T2 fmt2) : EncodableCorrect (product_fmt fmt1 fmt2).
Proof.
  constructor; intros; destruct x as [x1 x2].
  - simpl; simplify.
  - simpl in *; simplify.
    apply decodeBind_prefix; eauto; intros.
    apply decodeBind_prefix_first; eauto.
    rewrite fmt2.(decode_prefix); eauto.
    simpl in *; lia.
Qed.

Global Opaque product_fmt.

Instance uint64_fmt : Encodable uint64.
Proof.
  refine {| encode := uint64_to_le;
            decode := fun bs =>
                        let num := BS.take 8 bs in
                        if compare (BS.length num) 8 == Lt
                        then None
                        else match uint64_from_le num with
                             | Some x => Some (x, fromNum 8)
                             | None => None
                             end; |}.
Defined.

Instance uint64_fmt_ok : EncodableCorrect uint64_fmt.
Proof.
  constructor; intros; simpl in *.
  - rewrite take_app_exact
      by (rewrite uint64_le_enc.(encode_length_ok); auto).
    rewrite uint64_le_enc.(encode_length_ok).
    rewrite compare_eq.
    destruct (Eq == Lt); try congruence.
    rewrite uint64_le_enc.(encode_decode_ok); auto.
  - rewrite uint64_le_enc.(encode_length_ok) in *.
    rewrite take_take2 by lia.
    rewrite take_length_le.
    destruct (compare_lt_dec n 8); simpl in *;
      try lia;
      repeat simpl_match; auto.
    rewrite uint64_le_enc.(encode_length_ok); lia.
Qed.

Theorem uint64_fmt_length x :
  BS.length (uint64_fmt.(encode) x) = 8.
Proof.
  simpl.
  apply uint64_le_enc.(encode_length_ok).
Qed.

Global Opaque uint64_fmt.

Record Array64 := array64 { getBytes :> ByteString }.

Instance array64_fmt : Encodable Array64.
Proof.
  refine {| encode := fun (bs:Array64) =>
              array64 (uint64_fmt.(encode) (BS.length bs) ++ bs);
            decode :=
              l <- uint64_fmt.(decode);;
                                     array64 <$> decodeFixed l; |}.
Defined.

Theorem decodeFixed_first bs bs' :
  decodeFixed (BS.length bs) (bs ++ bs') = Some (bs, BS.length bs).
Proof.
  unfold decodeFixed.
  rewrite app_length.
  match goal with
  | |- context[compare ?x ?y == Gt] =>
    destruct (compare_gt_dec x y); simpl in *; try lia
  end.
  rewrite Hc.
  rewrite take_app_exact; auto.
Qed.

Theorem decodeFixed_prefix n bs :
  (BS.length bs).(toNum) < n.(toNum) ->
  decodeFixed n bs = None.
Proof.
  unfold decodeFixed; simpl; intros.
  destruct (u64_compare_dec n (BS.length bs)); try lia.
  rewrite e.
  destruct (Gt == Gt); congruence.
Qed.

Instance array64_fmt_ok : EncodableCorrect array64_fmt.
Proof.
  constructor; intros; simpl.
  - simplify.
    unfold decodeMap.
    rewrite decodeFixed_first; simpl; simplify.
    destruct x as [bs]; auto.
  - apply decodeBind_prefix; intros; try typeclasses eauto.
    unfold decodeMap; simpl.
    rewrite decodeFixed_prefix; simpl; auto.
    destruct x as [bs]; simpl in *.
    rewrite app_length in *.
    rewrite uint64_fmt_length in *.
    simpl in *.
    rewrite take_length_le; simpl; lia.
Qed.

Global Opaque array64_fmt.

Instance entry_fmt : Encodable Entry.t.
Proof.
  refine {| encode :=
              fun e => uint64_fmt.(encode) e.(Entry.key) ++ array64_fmt.(encode) (array64 e.(Entry.value));
            decode :=
              key <- uint64_fmt.(decode);;
            value <- getBytes <$> array64_fmt.(decode);;
            ret (Entry.mk key value); |}.
Defined.

Instance entry_fmt_ok : EncodableCorrect entry_fmt.
Proof.
  constructor; intros; simpl.
  - destruct x as [k v].
    simplify.
  - destruct x as [k v]; simpl in *.
    rewrite app_length in *.
    apply decodeBind_prefix; intros; eauto.
    typeclasses eauto.
    rewrite decodeMap_bind; simpl.
    apply decodeBind_prefix_first.
    typeclasses eauto.
    rewrite array64_fmt.(decode_prefix); auto.
    simpl in *; lia.
Qed.

Global Opaque entry_fmt.

Instance SliceHandle_fmt : Encodable SliceHandle.t.
Proof.
  refine {| encode :=
              fun h => uint64_fmt.(encode) h.(SliceHandle.offset)
                    ++ uint64_fmt.(encode) h.(SliceHandle.length);
            decode :=
              offset <- uint64_fmt.(decode);;
            length <- uint64_fmt.(decode);;
            ret (SliceHandle.mk offset length);
         |}.
Defined.

Instance SliceHandle_fmt_ok : EncodableCorrect SliceHandle_fmt.
Proof.
  constructor; intros; simpl.
  - destruct x as [o l].
    simplify.
  - destruct x as [o l]; simpl in *.
    rewrite app_length in *; simpl in *.
    apply decodeBind_prefix; intros.
    typeclasses eauto.
    apply decodeBind_prefix_first; intros.
    typeclasses eauto.
    rewrite uint64_fmt.(decode_prefix); auto.
    simpl in *; lia.
Qed.

Global Opaque SliceHandle_fmt.

Arguments encode {T fmt} v : rename.
Arguments decode T {fmt} bs : rename.
