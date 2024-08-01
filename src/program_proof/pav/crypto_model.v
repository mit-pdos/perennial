(** This file provides an operational model for:
1) an EUF-CMA signature scheme.
2) a collision-resistant random oracle hash function.

Hopefully, we can prove the admitted iProps in cryptoffi.v from it. *)

(* TODO: double check model with Derek. *)

From Perennial.Helpers Require Import Integers.
From stdpp Require Import prelude gmap.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Section shared.

(* arb_T returns a random concrete T. *)
Definition arb_bool : bool. Admitted.
Definition arb_bytes : list w8. Admitted.
Definition arb_bytes_len (len : nat) : list w8. Admitted.

End shared.

Section signatures.

Notation sk_ty := (list w8) (only parsing).
Notation pk_ty := (list w8) (only parsing).
Notation sig_ty := (list w8) (only parsing).
Notation msg_ty := (list w8) (only parsing).

Record sig_state_ty :=
  mk_sig_state {
    signed: gmap sk_ty (list msg_ty);
    pk_to_sk: gmap pk_ty sk_ty;
    (* this could be implemented with preimg pk_to_sk,
    but that gets very complicated. *)
    sk_to_pk: gmap sk_ty pk_ty;
    (* make verify deterministic by memoizing outputs. *)
    verify_memo: gmap (pk_ty * msg_ty * sig_ty) bool;
  }.
#[export] Instance eta_sig_state : Settable _ :=
  settable! mk_sig_state <signed; pk_to_sk; sk_to_pk; verify_memo>.

Inductive sig_op_ty : Type :=
  | key_gen : sig_op_ty
  | sign : sk_ty → msg_ty → sig_op_ty
  | verify : pk_ty → msg_ty → sig_ty → sig_op_ty.

Inductive sig_ret_ty : Type :=
  | ret_key_gen : sk_ty → pk_ty → sig_ret_ty
  | ret_sign : sig_ty → sig_ret_ty
  | ret_verify : bool → sig_ret_ty.

(** the main goal is to follow the guarantees of EUF-CMA as closely as possible.
e.g., EUF-CMA says sign / verify are undefined for OOD sk's / pk's,
so we return random values.
e.g., EUF-CMA has a stateful notion of the adversary not being able to forge
signatures if it never signed the msg before.
our model tracks signed state to guarantee this.

the main divergence is in the notion of distributions.
for us, "in-distribution" means a key already gen'd by key_gen.
"out-of-distribution" means a key not yet gen'd by key_gen.
in EUF-CMA, a distribution is fixed ahead of time.

the other divergence is how we capture the constraint of a poly time adversary.
the main capability of super-poly adversaries is their ability to run crypto ops
a huge number of times to exhibit collisions.
we block this, by having the underlying machine infinite loop exactly when
it detects a collision. *)
Definition sig_step (op : sig_op_ty) (state : sig_state_ty) : (sig_ret_ty * sig_state_ty) :=
  match op with
  | key_gen =>
    let sk := arb_bytes in
    let pk := arb_bytes in
    (* check for collisions, either with prior key_gen or with OOD key. *)
    match (state.(signed) !! sk, state.(pk_to_sk) !! pk,
      bool_decide (map_Exists (λ k _, k.1.1 = pk) state.(verify_memo))) with
    | (None, None, false) =>
      (* TODO: make key_gen not directly return the sk, so it's impossible
      for programs to leak it. *)
      (ret_key_gen sk pk,
        state <| signed ::= <[sk:=[]]> |>
              <| pk_to_sk ::= <[pk:=sk]> |>
              <| sk_to_pk ::= <[sk:=pk]> |>)
    | _ =>
      (* collision. infinite loop the machine. *)
      (ret_key_gen [] [], state)
    end

  | sign sk msg =>
    match (state.(signed) !! sk, state.(sk_to_pk) !! sk) with
    | (Some my_signed, Some pk) =>
      (* sign is probabilistic. might return diff sigs for same data.
      avoid sig dup in the following degenerate case:
      key_gen, verify msg sig = false, sign msg = sig, verify msg sig = ?. *)
      let sig := arb_bytes in
      match state.(verify_memo) !! (pk, msg, sig) with
      | None
      | Some true =>
        (ret_sign sig,
          state <| signed ::= <[sk:=msg::my_signed]> |>
                (* immediately memoize so verify returns the right thing. *)
                <| verify_memo ::= <[(pk,msg,sig):=true]> |>)
      | Some false =>
        (* bad sig collision (see above case). infinite loop the machine. *)
        (ret_sign [], state)
      end
    (* sign is only defined over in-distribution sk's. return random values. *)
    | _ =>
      let sig := arb_bytes in
      (ret_sign [], state)
    end

  | verify pk msg sig =>
    match state.(verify_memo) !! (pk, msg, sig) with
    | Some ok => (ret_verify ok, state)
    | None =>
      (* memoize new verify output. *)
      (λ '(new_ok, new_state),
        (ret_verify new_ok, new_state <| verify_memo ::= <[(pk,msg,sig):=new_ok]> |>))
      match state.(pk_to_sk) !! pk with
      | None =>
        (* verify is only defined over in-distribution pk's. return random values. *)
        let ok := arb_bool in
        (ok, state)
      | Some sk =>
        match state.(signed) !! sk with
        | None =>
          (* will never happen for in-distribution pk's. return random values. *)
          let ok := arb_bool in
          (ok, state)
        | Some my_signed =>
          match list_find (λ x, x = msg) my_signed with
          | None =>
            (* if never signed msg before, should be impossible to verify. *)
            (false, state)
          | Some _ =>
            (* for already signed msgs, either:
            1) we signed this exact sig.
            in this case, memoization would run, not this code.
            2) we signed this msg, but not this sig.
            could have forged a valid sig. *)
            let ok := arb_bool in
            (* even tho verify might ret true, only update signed state via
            the sign op, not here. *)
            (ok, state)
          end
        end
      end
    end
  end.

End signatures.

Section hashes.

Notation msg_ty := (list w8) (only parsing).
Notation hash_ty := (list w8) (only parsing).
Notation hash_len := (32) (only parsing).

Record hash_state_ty :=
  mk_hash_state {
    hashes: gmap msg_ty hash_ty;
  }.
#[export] Instance eta_hash_state : Settable _ :=
  settable! mk_hash_state <hashes>.

Inductive hash_op_ty : Type :=
  | hash : msg_ty → hash_op_ty.

Inductive hash_ret_ty : Type :=
  | ret_hash : hash_ty → hash_ret_ty.

Definition hash_step (op : hash_op_ty) (state : hash_state_ty) : (hash_ret_ty * hash_state_ty) :=
  match op with
  | hash msg =>
    match state.(hashes) !! msg with
    | Some h =>
      (ret_hash h, state)
    | None =>
      (* maintains inv that all hashes have same len. *)
      let new_hash := arb_bytes_len hash_len in
      match bool_decide (map_Exists (λ _ h, h = new_hash) state.(hashes)) with
      | true =>
        (* hash collision. infinite loop the machine. *)
        (ret_hash [], state)
      | false =>
        (ret_hash new_hash, state <| hashes ::= <[msg:=new_hash]> |>)
      end
    end
  end.

End hashes.
