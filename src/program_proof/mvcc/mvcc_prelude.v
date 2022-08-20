From Perennial.program_proof Require Export grove_prelude.
(* Prefer untyped slices. *)
Export Perennial.goose_lang.lib.slice.slice.

Definition dbval := option u64.
Notation Nil := (None : dbval).
Notation Value x := (Some x : dbval).

Definition to_dbval (b : bool) (v : u64) :=
  if b then Value v else Nil.

Definition dbmap := gmap u64 dbval.

Definition N_TXN_SITES : Z := 64.

Definition keys_all : gset u64 := fin_to_set u64.
Definition sids_all : list u64 := U64 <$> seqZ 0 N_TXN_SITES.
