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
    (* TODO: change to gmap. *)
    hashes: list (msgTy * hashTy);
  }.
#[export] Instance etaState : Settable _ := settable! mkState <signed; pks; hashes>.

Inductive opTy : Type :=
  | KeyGen : opTy
  | Sign : skTy → msgTy → opTy
  | Verify : pkTy → msgTy → sigTy → opTy
  | Hash : msgTy → opTy.

Inductive retTy : Type :=
  | ret : forall {T : Type}, T → retTy.

Definition ArbBool : bool.
Admitted.

Definition ArbBytes : list w8.
Admitted.

(*
new state that tracks all bad keys.
if verify called on bad pk,
return arbitrary thing (as long as deterministic).

all keys are good.
all crypto ops go thru this step function.
the laws of math hold.
but there might be unverif prog that calls crypto ops.

known vs unknown code.

if you're in a world running some known code and some unknown code,
all of these programs run this step func to modify global state.
namely, the unkown program might do arbitrary crypto ops that we don't know about.
therefore, if a known program calls verify, it has no guarantees
about the set of signed msgs with that key,
so it can't deduce what the output of verify will be.

proof strategy for verify post-cond for both all known and some unknown worlds.
spell this out.

figure out exactly what unknown code is allowed to do.

two worlds differ: whether unknown code has sk's that known code has pk's for.

3 cases of using honesty flags in spec.

so don't need honesty flag anymore. just use is_pk absence.

downside: proof duplication for the wp part. but core of proofs will be diff.

evidence checking func new spec. one with is_pk pre and one without.

the core remaining issues:
- ideally want to know that sk wasn't given to unknown progs.
this will be necessary in proving the Verify iprop.
how to guarantee that?
care about guaranteeing for checked progs.
in RW, checked progs don't use golang unsafe, so if sk was hidden in nice struct private field,
can't access it at all.
how to model that?
at iprop level? by creating strong opaque own_sk that doesn't expose own_slice_small?
but this doesn't feel principled. shouldn't rely on unfolding guarantees logically.
at operational level? by somehow making sk's their own thing and tying together with leakage to unchecked code.
- leakage. unchecked code isolation. unchecked code how much it can change state.
it can do a lot. like calling crypto ops and modifying crypto state.
but it shouldn't be able to do certain things, like receiving sk's.
what exactly should it be able to do?
- key gen func is a bit tricky as well, but we can figure it out without a flag.
what do we do when calling keygen and giving the key to an unchecked program?
what prevents checked programs from getting the corresponding is_pk?
 *)

Definition step (op : opTy) (state : stateTy) : (retTy * stateTy) :=
  match op with
  | KeyGen =>
    let sk := ArbBytes in
    let pk := ArbBytes in
    (* TODO: just use the update func directly. *)
    (* TODO: require sk's don't collide. *)
    (ret (sk, pk), state <|signed ::= (λ x, (<[sk:=[]]>x))|> <|pks ::= (λ x, (<[pk:=sk]>)x)|>)
  | Sign sk msg =>
    match state.(signed) !! sk with
    | Some my_signed =>
      (* Sign is probabilistic. might return diff sigs for same data. *)
      let sig := ArbBytes in
      (ret sig, state <|signed ::= (λ x, (<[sk:=(msg,sig)::my_signed]>x))|>)
    (* this will never happen. assume sk from KeyGen distr. *)
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
