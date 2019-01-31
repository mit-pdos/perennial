From Coq Require Import FunctionalExtensionality.
From Coq Require Import Program.Wf.
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

Lemma compare_not_gt x y : compare x y <> Gt -> x.(toNum) <= y.(toNum).
Proof.
  intros.
  destruct (compare_gt_dec x y); eauto.
  congruence.
Qed.

Definition decodeFixedSig (n:uint64) : Decoder {bs:ByteString | BS.length bs = n}.
  intro bs.
  destruct (compare n (BS.length bs) == Gt).
  exact None.
  refine (Some (_, n)).
  exists (BS.take n bs).
  apply take_length_le; eauto using compare_not_gt.
Defined.

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
    (* TODO: also prove prefix of an encoding decodes to None *)
  }.

(* only for this file's proofs make formats explicit *)
Arguments encode {T} fmt : rename.
Arguments decode {T} fmt : rename.
Arguments decode_encode {T} fmt {fmt_ok} : rename.

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

Definition fixed_fmt n : Encodable {x:ByteString | BS.length x = n} :=
  {| encode x := proj1_sig x;
     decode := decodeFixedSig n; |}.

Theorem Some_proj_eq A T (P: A -> Prop) (x y:option (sig P * T)) :
  match x with
  | Some (x', n) => Some (proj1_sig x', n)
  | None => None
  end = match y with
        | Some (y', n) => Some (proj1_sig y', n)
        | None => None
        end ->
  x = y.
Proof.
  destruct x as [ [x n] | ], y as [ [y n'] | ];
    intros; eauto; try congruence.
  inversion H; subst.
  f_equal.
  f_equal.
  destruct x, y.
  apply ProofIrrelevance.ProofIrrelevanceTheory.subset_eq_compat; eauto.
Qed.

Theorem fixed_fmt_ok n : EncodableCorrect (fixed_fmt n).
Proof.
  constructor; intros.
  destruct x as [bs ?]; simpl.
  apply Some_proj_eq; simpl.
  unfold decodeFixedSig.

  destruct (compare n (BS.length (bs ++ bs')) == Gt); subst;
    simpl in *;
    rewrite ?app_length in *.
  - apply compare_to_pf in e0; simpl in *.
    lia.
  - f_equal.
    f_equal.
    rewrite take_app_exact; auto.
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
  end.

Ltac simplify :=
  autorewrite with dec;
  repeat match goal with
         | |- EncodableCorrect _ => typeclasses eauto with core typeclass_instances
         | |- Some (_, ?x) = Some (_, ?x) => f_equal
         | |- Some (_, ?x) = Some (_, ?y) => replace x with y by solve_num_eq
         | |- ?x = ?x => reflexivity
         | _ => progress cbn [decodeRet decodeBind]
         end.

Instance product_fmt_ok
         `(fmt1_ok: @EncodableCorrect T1 fmt1) `(fmt2_ok: @EncodableCorrect T2 fmt2) : EncodableCorrect (product_fmt fmt1 fmt2).
Proof.
  constructor; intros.
  destruct x as [x1 x2]; simpl; simplify.
Qed.

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
  constructor; intros.
  simpl.
  rewrite take_app_exact
    by (rewrite uint64_le_enc.(encode_length_ok); auto).
  rewrite uint64_le_enc.(encode_length_ok).
  rewrite compare_eq.
  destruct (Eq == Lt); try congruence.
  rewrite uint64_le_enc.(encode_decode_ok); auto.
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


Instance array64_fmt_ok : EncodableCorrect array64_fmt.
Proof.
  constructor; intros; simpl.
  simplify.
  unfold decodeMap.
  rewrite decodeFixed_first; simpl; simplify.
  destruct x as [bs]; auto.
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
  destruct x as [k v].
  simplify.
Qed.

Global Opaque entry_fmt.

Fixpoint encode_list T (enc: T -> ByteString) (l: list T) : ByteString :=
  match l with
  | nil => BS.empty
  | cons x xs => BS.append (enc x) (encode_list enc xs)
  end.

Program Fixpoint decode_list T (dec: Decoder T) (bs:ByteString)
        {measure (toNum (BS.length bs)) lt} : option (list T * uint64) :=
  if bs == BS.empty
  then Some (nil, 0)
  else match dec bs with
       | Some (x, n) => if n == 0 then None else
                         match decode_list dec (BS.drop n bs) with
                         | Some (x', n') => Some (cons x x', n')
                         | None => None
                         end
       | None => None
       end.
Next Obligation.
  intros.
  rewrite drop_length.
  simpl.
  destruct n as [n]; simpl in *.
  destruct bs as [bs]; simpl in *.
  u64_cleanup.
  assert (length bs > 0).
  destruct bs; simpl in *; try lia.
  exfalso; eauto.
  lia.
Qed.
Next Obligation.
  apply measure_wf.
  apply Wf_nat.lt_wf.
Qed.

(* decode a list of elements encoded with a particular format, expecting them to
fit exactly in the input buffer

intentionally not an instance since lists can be encoded in multiple ways (eg,
with a length prefix) and this isn't the most general such format *)
Definition exact_list_fmt T (fmt:Encodable T) : Encodable (list T).
  refine {| encode := encode_list (@encode T fmt);
            decode := decode_list (@decode T fmt); |}.
Defined.

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
  destruct x as [o l].
  simplify.
Qed.

Global Opaque SliceHandle_fmt.

Arguments encode {T fmt} v : rename.
Arguments decode T {fmt} bs : rename.
