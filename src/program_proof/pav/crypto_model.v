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

Notation sk_ty := (list w8) (only parsing).
Notation pk_ty := (list w8) (only parsing).
Notation msg_ty := (list w8) (only parsing).
Notation sig_ty := (list w8) (only parsing).
Notation hash_ty := (list w8) (only parsing).

Record state_ty :=
  mk_state {
    signed: gmap sk_ty (list (msg_ty * sig_ty));
    pks: gmap pk_ty sk_ty;
    hashes: gmap msg_ty hash_ty;
  }.
#[export] Instance eta_state : Settable _ := settable! mk_state <signed; pks; hashes>.

Inductive op_ty : Type :=
  | key_gen : op_ty
  | sign : sk_ty → msg_ty → op_ty
  | verify : pk_ty → msg_ty → sig_ty → op_ty
  | hash : msg_ty → op_ty.

Inductive ret_ty : Type :=
  | ret : forall {T : Type}, T → ret_ty.

Definition arb_bool : bool.
Admitted.

Definition arb_bytes : list w8.
Admitted.

Definition arb_bytes_len (len : nat) : list w8.
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
this will be necessary in proving the verify iprop.
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

Definition step (op : op_ty) (state : state_ty) : (ret_ty * state_ty) :=
  match op with
  | key_gen =>
    let sk := arb_bytes in
    let pk := arb_bytes in
    match (state.(pks) !! pk, state.(signed) !! sk) with
    | (None, None) =>
      (ret (sk, pk), state <| signed ::= <[sk:=[]]> |> <| pks ::= <[pk:=sk]> |>)
    | _ =>
      (* collision. infinite loop the machine. *)
      (ret 0, state)
    end
  | sign sk msg =>
    match state.(signed) !! sk with
    | Some my_signed =>
      (* sign is probabilistic. might return diff sigs for same data. *)
      let sig := arb_bytes in
      (ret sig, state <| signed ::= <[sk:=(msg,sig)::my_signed]> |>)
    (* this will never happen. assume sk from key_gen distr. *)
    | None => (ret 0, state)
    end
  | verify pk msg sig =>
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
            let ok := arb_bool in
            match ok with
            | true => (ret true, state <| signed ::= <[sk:=(msg,sig)::my_signed]> |>)
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
      (* verify can return anything for OOD pk. *)
      (* TODO: it's deterministic, so memoize the output. *)
      let ok := arb_bool in
      (ret ok, state)
    end
  | hash msg =>
    match state.(hashes) !! msg with
    | Some h =>
      (ret h, state)
    | None =>
      let new_hash := arb_bytes in
      match bool_decide (map_Exists (λ _ h, h = new_hash) state.(hashes)) with
      | true =>
        (* hash collision. infinite loop the machine. *)
        (ret 0, state)
      | false =>
        (ret new_hash, state <| hashes ::= <[msg:=new_hash]> |>)
      end
    end
  end.
