From RecordUpdate Require Import RecordSet.
From Perennial.Helpers Require Import List Fractional.
From Perennial.goose_lang Require Import proofmode.
(* From Perennial.new_goose_lang.lib Require Import persistent_readonly typed_mem. *)
From Perennial.new_goose_lang.lib Require Export slice.impl.
From Perennial.goose_lang.lib Require Import control.control.

Set Default Proof Using "Type".

Module slice.
  Record t :=
    mk { ptr: loc;
         sz: u64;
         cap: u64; }.
  Global Instance _eta: Settable _ := settable! mk <ptr; sz; cap>.
  Global Instance _witness: Inhabited _ := populate (mk inhabitant inhabitant inhabitant).
  Notation extra s := (uint.Z (cap s) - uint.Z (sz s)).
  Definition nil := mk null (W64 0) (W64 0).
End slice.

Section goose_lang.
Context `{ffi_semantics}.

Coercion slice_val (s: slice.t) : val := (#s.(slice.ptr), #s.(slice.sz), #s.(slice.cap)).
Definition val_slice v : option slice.t :=
  match v with
  | (#(LitLoc ptr), #(LitInt sz), #(LitInt cap))%V => Some (slice.mk ptr sz cap)
  | _ => None
  end.
End goose_lang.
