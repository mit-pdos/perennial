From Coq Require Import FunctionalExtensionality.
From RecoveryRefinement Require Import Helpers.MachinePrimitives.
From RecoveryRefinement Require Import Database.Common.

From Tactical Require Import ProofAutomation.

Import BSNotations.

Definition Decoder T := ByteString -> option (T * uint64).

Definition decodeBind T1 T2 (dec1: Decoder T1) (dec2: T1 -> Decoder T2) : Decoder T2 :=
  fun bs => match dec1 bs with
         | Some (v1, n) => match dec2 v1 (BS.drop n bs) with
                          | Some (v2, n2) => Some (v2, intPlus uint64 n n2)
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
  destruct matches; subst; auto.
  (* required associativity of intPlus as well as a model of BS.drop *)
Abort.

Definition decodeRet T (v:T) : Decoder T :=
  fun _ => Some (v, int_val0).

Definition decodeFail {T} : Decoder T :=
  fun _ => None.

Definition decodeFinished : Decoder unit :=
  fun bs => match intCmp (BS.length bs) int_val0 with
         | Gt => None
         | _ => Some (tt, int_val0)
         end.

Definition decodeFixed (n:uint64) : Decoder ByteString :=
  fun bs => match intCmp (BS.length bs) n with
         | Gt => None
         | _ => Some (BS.take n bs, n)
         end.

Definition decodeMap A B (f: A -> B) (dec: Decoder A) : Decoder B :=
  fun bs => match dec bs with
         | Some (v, n) => Some (f v, n)
         | None => None
         end.

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
    decode : Decoder T; }.

Arguments encode {T fmt} v : rename.
Arguments decode T {fmt} bs : rename.

Import DecodeNotations.
Local Open Scope bs.
Local Open Scope dec.

Instance product_fmt
         T1 T2 (fmt1: Encodable T1) (fmt2: Encodable T2)
  : Encodable (T1*T2).
Proof.
  refine {| encode '(x1, x2) := encode x1 ++ encode x2;
            decode :=
              v1 <- decode T1;;
                 v2 <- decode T2;;
                 ret (v1, v2); |}.
Defined.

Axiom uint64_fmt : Encodable uint64.
Existing Instance uint64_fmt.

Axiom uint32_fmt : Encodable uint32.
Existing Instance uint32_fmt.

Axiom uint16_fmt : Encodable uint16.
Existing Instance uint16_fmt.

Axiom uint8_fmt : Encodable uint8.
Existing Instance uint8_fmt.

Record Array16 := array16 { getBytes :> ByteString }.

Instance array16_fmt : Encodable Array16.
Proof.
  refine {| encode := fun (bs:Array16) =>
              array16 (encode (uint64_to_uint16 (BS.length bs)) ++ bs);
            decode :=
              l <- decode uint16;;
                array16 <$> decodeFixed (uint16_to_uint64 l); |}.
Defined.

Instance entry_fmt : Encodable Entry.t.
Proof.
  refine {| encode :=
              fun e => encode e.(Entry.key) ++ encode (array16 e.(Entry.value));
            decode :=
              key <- decode uint64;;
            value <- getBytes <$> decode Array16;;
            ret (Entry.mk key value); |}.
Defined.
