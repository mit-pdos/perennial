From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.tulip Require Import base.

Definition encode_string (x : byte_string) : list u8 :=
  u64_le (U64 (length x)) ++ x.

Definition encode_strings_step (bs : list u8) (x : byte_string) : list u8 :=
  bs ++ encode_string x.

Definition encode_strings_xlen (xs : list byte_string) : list u8 :=
  foldl encode_strings_step [] xs.

Definition encode_strings (xs : list byte_string) : list u8 :=
  u64_le (U64 (length xs)) ++ encode_strings_xlen xs.

Lemma encode_strings_xlen_snoc xs x :
  encode_strings_xlen (xs ++ [x]) = encode_strings_xlen xs ++ encode_string x.
Proof.
  by rewrite /encode_strings_xlen foldl_snoc /encode_strings_step.
Qed.

Lemma foldl_encode_strings_step_app (bs : list u8) (xs : list byte_string) :
  foldl encode_strings_step bs xs = bs ++ foldl encode_strings_step [] xs.
Proof.
  generalize dependent bs.
  induction xs as [| x xs IH]; intros bs.
  { by rewrite /= app_nil_r. }
  rewrite /= (IH (encode_strings_step bs x)) (IH (encode_strings_step [] x)).
  rewrite {1 3}/encode_strings_step.
  by rewrite app_nil_l app_assoc.
Qed.

Lemma encode_strings_xlen_cons xs x :
  encode_strings_xlen (x :: xs) = encode_string x ++ encode_strings_xlen xs.
Proof.
  rewrite /encode_strings_xlen /= foldl_encode_strings_step_app.
  by rewrite {1}/encode_strings_step app_nil_l.
Qed.

Lemma encode_strings_xlen_length_inv xs n :
  (length (encode_strings_xlen xs) ≤ n)%nat ->
  (length xs ≤ n)%nat.
Proof.
  generalize dependent n.
  induction xs as [| x xs IH]; intros n; first done.
  rewrite encode_strings_xlen_cons length_app /=.
  assert (length (encode_string x) ≠ O).
  { by destruct (nil_or_length_pos (encode_string x)). }
  intros Hlen.
  assert (Hlenxs : (length xs ≤ pred n)%nat).
  { apply IH. lia. }
  lia.
Qed.

Lemma encode_strings_length_inv xs n :
  (length (encode_strings xs) ≤ n)%nat ->
  (length xs ≤ n)%nat.
Proof.
  rewrite /encode_strings length_app.
  intros Hn.
  pose proof (encode_strings_xlen_length_inv xs n) as Hlen.
  lia.
Qed.

Definition encode_dbval (x : dbval) : list u8 :=
  match x with
  | Some v => [U8 1] ++ encode_string v
  | None => [U8 0]
  end.

Definition encode_dbmod (x : dbmod) : list u8 :=
  encode_string x.1 ++ encode_dbval x.2.

Definition encode_dbmods_step (bs : list u8) (x : dbmod) : list u8 :=
  bs ++ encode_dbmod x.

Definition encode_dbmods_xlen (xs : list dbmod) : list u8 :=
  foldl encode_dbmods_step [] xs.

Definition encode_dbmods (xs : list dbmod) : list u8 :=
  u64_le (U64 (length xs)) ++ encode_dbmods_xlen xs.

Lemma encode_dbmods_xlen_snoc xs x :
  encode_dbmods_xlen (xs ++ [x]) = encode_dbmods_xlen xs ++ encode_dbmod x.
Proof.
  by rewrite /encode_dbmods_xlen foldl_snoc /encode_dbmods_step.
Qed.

Lemma foldl_encode_dbmods_step_app (bs : list u8) (xs : list dbmod) :
  foldl encode_dbmods_step bs xs = bs ++ foldl encode_dbmods_step [] xs.
Proof.
  generalize dependent bs.
  induction xs as [| x xs IH]; intros bs.
  { by rewrite /= app_nil_r. }
  rewrite /= (IH (encode_dbmods_step bs x)) (IH (encode_dbmods_step [] x)).
  rewrite {1 3}/encode_dbmods_step.
  by rewrite app_nil_l app_assoc.
Qed.

Lemma encode_dbmods_xlen_cons xs x :
  encode_dbmods_xlen (x :: xs) = encode_dbmod x ++ encode_dbmods_xlen xs.
Proof.
  rewrite /encode_dbmods_xlen /= foldl_encode_dbmods_step_app.
  by rewrite {1}/encode_dbmods_step app_nil_l.
Qed.

Lemma encode_dbmods_xlen_length_inv xs n :
  (length (encode_dbmods_xlen xs) ≤ n)%nat ->
  (length xs ≤ n)%nat.
Proof.
  generalize dependent n.
  induction xs as [| x xs IH]; intros n; first done.
  rewrite encode_dbmods_xlen_cons length_app /=.
  assert (length (encode_dbmod x) ≠ O).
  { by destruct x as [[] []]. }
  intros Hlen.
  assert (Hlenxs : (length xs ≤ pred n)%nat).
  { apply IH. lia. }
  lia.
Qed.

Lemma encode_dbmods_length_inv xs n :
  (length (encode_dbmods xs) ≤ n)%nat ->
  (length xs ≤ n)%nat.
Proof.
  rewrite /encode_dbmods length_app.
  intros Hn.
  pose proof (encode_dbmods_xlen_length_inv xs n) as Hlen.
  lia.
Qed.

Definition encode_dbmap (m : dbmap) (data : list u8) :=
  ∃ xs, data = encode_dbmods xs ∧ xs ≡ₚ map_to_list m.

Definition encode_dbpver (x : dbpver) : list u8 :=
  u64_le x.1 ++ encode_dbval x.2.
