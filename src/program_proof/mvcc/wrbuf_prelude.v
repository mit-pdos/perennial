From Perennial.program_proof.mvcc Require Export mvcc_prelude mvcc_misc mvcc_ghost.
From Goose.github_com.mit_pdos.vmvcc Require Export wrbuf.

Definition wrent := (u64 * byte_string * bool * loc)%type.

Definition wrent_to_val (x : wrent) :=
  (#x.1.1.1, (#(LitString x.1.1.2), (#x.1.2, (#x.2, #()))))%V.

Lemma wrent_to_val_unfold (k : u64) (v : byte_string) (w : bool) (t : loc) :
  (#k, (#(LitString v), (#w, (#t, #()))))%V = wrent_to_val (k, v, w, t).
Proof. reflexivity. Qed.

Definition wrent_to_key_dbval (x : wrent) : (u64 * dbval) :=
  (x.1.1.1, (to_dbval x.1.2 x.1.1.2)).

Definition wrent_to_key_tpl (x : wrent) : (u64 * loc) :=
  (x.1.1.1, x.2).

Lemma val_to_wrent_with_val_ty (x : val) :
  val_ty x (uint64T * (stringT * (boolT * (ptrT * unitT))))%ht ->
  (∃ (k : u64) (v : byte_string) (w : bool) (t : loc), x = wrent_to_val (k, v, w, t)).
Proof.
  intros H.
  inversion_clear H. 
  { inversion H0. }
  inversion_clear H0.
  inversion_clear H.
  inversion_clear H1.
  { inversion H. }
  inversion_clear H.
  inversion_clear H1.
  inversion_clear H0.
  { inversion H. }
  inversion_clear H.
  inversion_clear H0.
  inversion_clear H1.
  { inversion H. }
  inversion_clear H.
  inversion_clear H1.
  inversion_clear H0.
  inversion_clear H.
  exists x0, x1, x2, x3.
  unfold wrent_to_val.
  reflexivity.
Qed.

Lemma wrent_to_val_with_lookup (x : val) (l : list wrent) (i : nat) :
  (wrent_to_val <$> l) !! i = Some x ->
  (∃ (k : u64) (v : byte_string) (w : bool) (t : loc), x = wrent_to_val (k, v, w, t) ∧ l !! i = Some (k, v, w, t)).
Proof.
  intros H.
  apply list_lookup_fmap_inv in H as [[[[k v] w] t] [Heq Hsome]].
  naive_solver.
Qed.
