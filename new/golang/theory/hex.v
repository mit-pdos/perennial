From New.golang.defn Require Export hex.
From stdpp Require Import base.
From stdpp Require Export ssreflect.
From Coq Require Import Equality.

Lemma hex_encode_length (w : w8) :
  length (hex_encode_w8 w) = 2%nat.
Proof.
  rewrite -(ByteString.w8_to_byte_to_w8 w).
  generalize (w8_to_byte w). clear.
  by intros [].
Qed.

Local Delimit Scope byte_string_scope with go.
Delimit Scope byte_char_scope with go_byte.

Local Definition hex := ["00";"01";"02";"03";"04";"05";"06";"07";"08";"09";"0a";"0b";"0c";"0d";"0e";"0f";"10";"11";"12";"13";"14";"15";"16";"17";"18";"19";"1a";"1b";"1c";"1d";"1e";"1f";"20";"21";"22";"23";"24";"25";"26";"27";"28";"29";"2a";"2b";"2c";"2d";"2e";"2f";"30";"31";"32";"33";"34";"35";"36";"37";"38";"39";"3a";"3b";"3c";"3d";"3e";"3f";"40";"41";"42";"43";"44";"45";"46";"47";"48";"49";"4a";"4b";"4c";"4d";"4e";"4f";"50";"51";"52";"53";"54";"55";"56";"57";"58";"59";"5a";"5b";"5c";"5d";"5e";"5f";"60";"61";"62";"63";"64";"65";"66";"67";"68";"69";"6a";"6b";"6c";"6d";"6e";"6f";"70";"71";"72";"73";"74";"75";"76";"77";"78";"79";"7a";"7b";"7c";"7d";"7e";"7f";"80";"81";"82";"83";"84";"85";"86";"87";"88";"89";"8a";"8b";"8c";"8d";"8e";"8f";"90";"91";"92";"93";"94";"95";"96";"97";"98";"99";"9a";"9b";"9c";"9d";"9e";"9f";"a0";"a1";"a2";"a3";"a4";"a5";"a6";"a7";"a8";"a9";"aa";"ab";"ac";"ad";"ae";"af";"b0";"b1";"b2";"b3";"b4";"b5";"b6";"b7";"b8";"b9";"ba";"bb";"bc";"bd";"be";"bf";"c0";"c1";"c2";"c3";"c4";"c5";"c6";"c7";"c8";"c9";"ca";"cb";"cc";"cd";"ce";"cf";"d0";"d1";"d2";"d3";"d4";"d5";"d6";"d7";"d8";"d9";"da";"db";"dc";"dd";"de";"df";"e0";"e1";"e2";"e3";"e4";"e5";"e6";"e7";"e8";"e9";"ea";"eb";"ec";"ed";"ee";"ef";"f0";"f1";"f2";"f3";"f4";"f5";"f6";"f7";"f8";"f9";"fa";"fb";"fc";"fd";"fe";"ff"]%go.
Local Lemma hex_NoDup_helper : hex = remove_dups hex.
Proof. reflexivity. Qed.
Local Lemma hex_NoDup : NoDup hex.
Proof. rewrite hex_NoDup_helper. apply NoDup_remove_dups. Qed.
Local Definition hex_encode_w8' (x : w8) := default "00"%go (hex !! uint.nat x).
Local Lemma hex_encode_eq (x : w8) : hex_encode_w8' x = hex_encode_w8 x.
Proof.
  rewrite -(ByteString.w8_to_byte_to_w8 x).
  generalize (w8_to_byte x) as x'. clear. by intros [].
Qed.
Local Lemma hex_lookup (x : w8) :
  ∃ y, hex !! (uint.nat x) = Some y.
Proof.
  destruct (hex !! _) eqn:Hbad.
  { by eexists. }
  exfalso.
  rewrite lookup_ge_None /= in Hbad.
  word.
Qed.

Definition hex_chars :=
  ["0"; "1"; "2"; "3"; "4"; "5"; "6"; "7"; "8"; "9"; "a"; "b"; "c"; "d"; "e"; "f" ]%go_byte.

Lemma hex_encode_subseteq x : (hex_encode x ⊆ hex_chars).
Proof.
  induction x.
  { set_solver. }
  simpl.
  rewrite -hex_encode_eq.
  rewrite list_subseteq_app_iff_l.
  split; try done.
  rewrite -(ByteString.w8_to_byte_to_w8 a).
  generalize (w8_to_byte a) as x'. clear.
  intros [].
  1-50: set_solver.
  1-50: set_solver.
  1-50: set_solver.
  1-50: set_solver.
  1-50: set_solver.
  all: set_solver.
Qed.

Instance hex_encode_w8_inj : Inj (=) (=) hex_encode_w8.
Proof.
  hnf. intros x y.
  rewrite -!hex_encode_eq.
  intros Heq.
  rewrite /hex_encode_w8' in Heq.
  pose proof (hex_lookup x) as [? Hl1].
  pose proof (hex_lookup y) as [? Hl2].
  rewrite Hl1 Hl2 /= in Heq. subst.
  apply word.unsigned_inj.
  apply Z2Nat.inj; try word.
  eapply NoDup_lookup; try done.
  apply hex_NoDup.
Qed.

Lemma hex_encode_w8_length x : length (hex_encode_w8 x) = 2%nat.
Proof.
  rewrite -(ByteString.w8_to_byte_to_w8 x).
  generalize (w8_to_byte x) as x'. clear. by intros [].
Qed.

Instance hex_encode_inj : Inj (=) (=) hex_encode.
Proof.
  hnf. intros?? Heq.
  move x after y.
  dependent induction x generalizing y.
  { destruct y; first done.
    exfalso. apply (f_equal length) in Heq.
    rewrite /= length_app hex_encode_length in Heq. lia.
  }
  destruct y.
  { exfalso. apply (f_equal length) in Heq.
    rewrite /= length_app hex_encode_length in Heq. lia. }
  apply app_inj_1 in Heq.
  2:{ rewrite !hex_encode_w8_length //. }
  intuition.
  f_equal.
  - by apply hex_encode_w8_inj.
  - by apply IHx.
Qed.

Lemma hex_encode_app_inj a1 a2 b1 b2:
  hex_encode a1 ++ " "%go ++ hex_encode b1 =
  hex_encode a2 ++ " "%go ++ hex_encode b2 →
  a1 = a2 ∧ b1 = b2.
Proof.
  intros Heq.
  change (" "%go) with ([" "%go_byte]) in Heq.
  rewrite -!cons_middle in Heq.
  apply app_inj_pivot in Heq as [Hbad|Heq].
  {
    exfalso.
    rewrite -!elem_of_list_In in Hbad.
    pose proof (hex_encode_subseteq a1).
    pose proof (hex_encode_subseteq a2).
    set_solver.
  }
  destruct Heq as [? ?].
  repeat match goal with
  | [ H : context [hex_encode] |- _] => apply (hex_encode_inj) in H
  end. by subst.
Qed.
