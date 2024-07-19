(*
Here's an operational model for:
1) an EUF-CMA signature scheme
2) a collision-resistant random oracle hash function

Hopefully, we can prove the admitted iProps in cryptoffi.v from it.
*)

From Perennial.Helpers Require Import Integers.
From stdpp Require Import prelude gmap.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Notation skTy := (list w8) (only parsing).
Notation pkTy := (list w8) (only parsing).
Notation msgTy := (list w8) (only parsing).
Notation sigTy := (list w8) (only parsing).
Notation hashTy := (list w8) (only parsing).

Record stateTy :=
  mkState {
    signed: gmap skTy (list (msgTy * sigTy));
    pks: gmap pkTy skTy;
    hashes: list (msgTy * hashTy);
  }.
#[export] Instance etaState : Settable _ := settable! mkState <signed; pks; hashes>.

Inductive opTy : Type :=
  | GenKey : opTy
  | Sign : skTy → msgTy → opTy
  | Verify : pkTy → msgTy → sigTy → opTy
  | Hash : msgTy → opTy.

Inductive retTy : Type :=
  | ret : forall {T : Type}, T → retTy.

Definition ArbBool : bool.
Admitted.

Definition ArbBytes : list w8.
Admitted.

Definition step (op : opTy) (state : stateTy) : (retTy * stateTy) :=
  match op with
  | GenKey =>
    let sk := ArbBytes in
    let pk := ArbBytes in
    (ret (sk, pk), state <|signed ::= (λ x, (<[sk:=[]]>x))|> <|pks ::= (λ x, (<[pk:=sk]>)x)|>)
  | Sign sk msg =>
    match state.(signed) !! sk with
    | Some my_signed =>
      (* Sign is probabilistic. might return diff sigs for same data. *)
      let sig := ArbBytes in
      (ret sig, state <|signed ::= (λ x, (<[sk:=(msg,sig)::my_signed]>x))|>)
    (* this will never happen. assume sk from GenKey distr. *)
    | None => (ret 0, state)
    end
  | Verify pk msg sig =>
    match state.(pks) !! pk with
    | Some sk =>
      match state.(signed) !! sk with
      | Some my_signed =>
        match list_find (λ x, x.1 = msg) my_signed with
        | Some _ =>
          match list_find (λ x, x = (msg,sig)) my_signed with
          | Some _ =>
            (ret true, state)
          | None =>
            (* for already signed msgs, might be able to forge sig. *)
            let ok := ArbBool in
            match ok with
            | true => (ret true, state <|signed ::= (λ x, (<[sk:=(msg,sig)::my_signed]>x))|>)
            | false => (ret false, state)
            end
          end
        | None =>
          (* if never signed msg before, should be impossible to verify. *)
          (ret false, state)
        end
      | None =>
        (* this will never happen bc state.(pks) only has in-distr keys. *)
        (ret false, state)
      end
    | None =>
      (* Verify can return anything for OOD pk. *)
      (* TODO: it's deterministic, so memoize the output. *)
      let ok := ArbBool in
      (ret ok, state)
    end
  | Hash msg =>
    match list_find (λ x, x.1 = msg) state.(hashes) with
    | Some x =>
      (ret x.2, state)
    | None =>
      let hash := ArbBytes in
      match list_find (λ x, x.2 = hash) state.(hashes) with
      | Some _ =>
        (* hash collision. infinite loop the machine. *)
        (ret 0, state)
      | None =>
        (ret hash, state <|hashes ::= (λ x, (msg,hash)::x)|>)
      end
    end
  end.
