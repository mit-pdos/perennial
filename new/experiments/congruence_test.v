Inductive t1 :=
  mk1 (a1 : unit).
Lemma congruence_test1 f a1 :
  f a1 = a1 ->
  mk1 (f a1)  =
  mk1 a1.
Proof. time congruence. Qed.

Inductive t2 :=
  mk2 (a1 a2 : unit).
Lemma congruence_test2 f a1 a2 :
  f a1 = a1 ->
  mk2 (f a1)  a2 =
  mk2 a1 a2.
Proof. time congruence. Qed.

Inductive t3 :=
  mk3 (a1 a2 a3 : unit).
Lemma congruence_test3 f a1 a2 a3 :
  f a1 = a1 ->
  mk3 (f a1)  a2 a3 =
  mk3 a1 a2 a3.
Proof. time congruence. Qed.

Inductive t4 :=
  mk4 (a1 a2 a3 a4 : unit).
Lemma congruence_test4 f a1 a2 a3 a4 :
  f a1 = a1 ->
  mk4 (f a1)  a2 a3 a4 =
  mk4 a1 a2 a3 a4.
Proof. time congruence. Qed.

Inductive t5 :=
  mk5 (a1 a2 a3 a4 a5 : unit).
Lemma congruence_test5 f a1 a2 a3 a4 a5 :
  f a1 = a1 ->
  mk5 (f a1)  a2 a3 a4 a5 =
  mk5 a1 a2 a3 a4 a5.
Proof. time congruence. Qed.

Inductive t6 :=
  mk6 (a1 a2 a3 a4 a5 a6 : unit).
Lemma congruence_test6 f a1 a2 a3 a4 a5 a6 :
  f a1 = a1 ->
  mk6 (f a1)  a2 a3 a4 a5 a6 =
  mk6 a1 a2 a3 a4 a5 a6.
Proof. time congruence. Qed.

Inductive t7 :=
  mk7 (a1 a2 a3 a4 a5 a6 a7 : unit).
Lemma congruence_test7 f a1 a2 a3 a4 a5 a6 a7 :
  f a1 = a1 ->
  mk7 (f a1)  a2 a3 a4 a5 a6 a7 =
  mk7 a1 a2 a3 a4 a5 a6 a7.
Proof. time congruence. Qed.

Inductive t8 :=
  mk8 (a1 a2 a3 a4 a5 a6 a7 a8 : unit).
Lemma congruence_test8 f a1 a2 a3 a4 a5 a6 a7 a8 :
  f a1 = a1 ->
  mk8 (f a1)  a2 a3 a4 a5 a6 a7 a8 =
  mk8 a1 a2 a3 a4 a5 a6 a7 a8.
Proof. time congruence. Qed.

Inductive t9 :=
  mk9 (a1 a2 a3 a4 a5 a6 a7 a8 a9 : unit).
Lemma congruence_test9 f a1 a2 a3 a4 a5 a6 a7 a8 a9 :
  f a1 = a1 ->
  mk9 (f a1)  a2 a3 a4 a5 a6 a7 a8 a9 =
  mk9 a1 a2 a3 a4 a5 a6 a7 a8 a9.
Proof. time congruence. Qed.

Inductive t10 :=
  mk10 (a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 : unit).
Lemma congruence_test10 f a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 :
  f a1 = a1 ->
  mk10 (f a1)  a2 a3 a4 a5 a6 a7 a8 a9 a10 =
  mk10 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10.
Proof. time congruence. Qed.

Inductive t11 :=
  mk11 (a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 : unit).
Lemma congruence_test11 f a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 :
  f a1 = a1 ->
  mk11 (f a1)  a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 =
  mk11 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11.
Proof. time congruence. Qed.

Inductive t12 :=
  mk12 (a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 : unit).
Lemma congruence_test12 f a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 :
  f a1 = a1 ->
  mk12 (f a1)  a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 =
  mk12 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12.
Proof. time congruence. Qed.

Inductive t13 :=
  mk13 (a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 : unit).
Lemma congruence_test13 f a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 :
  f a1 = a1 ->
  mk13 (f a1)  a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 =
  mk13 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13.
Proof. time congruence. Qed.

Inductive t14 :=
  mk14 (a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 : unit).
Lemma congruence_test14 f a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 :
  f a1 = a1 ->
  mk14 (f a1)  a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 =
  mk14 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14.
Proof. time congruence. Qed.

Inductive t15 :=
  mk15 (a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : unit).
Lemma congruence_test15 f a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 :
  f a1 = a1 ->
  mk15 (f a1)  a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 =
  mk15 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15.
Proof. time congruence. Qed.

Inductive t16 :=
  mk16 (a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 : unit).
Lemma congruence_test16 f a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 :
  f a1 = a1 ->
  mk16 (f a1)  a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 =
  mk16 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16.
Proof. time congruence. Qed.

Inductive t17 :=
  mk17 (a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 : unit).
Lemma congruence_test17 f a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 :
  f a1 = a1 ->
  mk17 (f a1)  a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 =
  mk17 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17.
Proof. time congruence. Qed.

Inductive t18 :=
  mk18 (a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 : unit).
Lemma congruence_test18 f a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 :
  f a1 = a1 ->
  mk18 (f a1)  a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 =
  mk18 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18.
Proof. time congruence. Qed.

Inductive t19 :=
  mk19 (a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 : unit).
Lemma congruence_test19 f a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 :
  f a1 = a1 ->
  mk19 (f a1)  a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 =
  mk19 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19.
Proof. time congruence. Qed.

Inductive t20 :=
  mk20 (a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 : unit).
Lemma congruence_test20 f a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 :
  f a1 = a1 ->
  mk20 (f a1)  a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 =
  mk20 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20.
Proof. time congruence. Qed.

Inductive t21 :=
  mk21 (a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 : unit).
Lemma congruence_test21 f a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 :
  f a1 = a1 ->
  mk21 (f a1)  a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 =
  mk21 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21.
Proof. time congruence. Qed.

Inductive t22 :=
  mk22 (a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 : unit).
Lemma congruence_test22 f a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 :
  f a1 = a1 ->
  mk22 (f a1)  a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 =
  mk22 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22.
Proof. time congruence. Qed.

Inductive t23 :=
  mk23 (a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 : unit).
Lemma congruence_test23 f a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 :
  f a1 = a1 ->
  mk23 (f a1)  a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 =
  mk23 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23.
Proof. time congruence. Qed.

Inductive t24 :=
  mk24 (a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 : unit).
Lemma congruence_test24 f a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 :
  f a1 = a1 ->
  mk24 (f a1)  a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 =
  mk24 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24.
Proof. time congruence. Qed.

Inductive t25 :=
  mk25 (a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 : unit).
Lemma congruence_test25 f a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 :
  f a1 = a1 ->
  mk25 (f a1)  a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 =
  mk25 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25.
Proof. time congruence. Qed.

Inductive t26 :=
  mk26 (a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 : unit).
Lemma congruence_test26 f a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 :
  f a1 = a1 ->
  mk26 (f a1)  a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 =
  mk26 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26.
Proof. time congruence. Qed.

Inductive t27 :=
  mk27 (a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 : unit).
Lemma congruence_test27 f a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 :
  f a1 = a1 ->
  mk27 (f a1)  a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 =
  mk27 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27.
Proof. time congruence. Qed.

Inductive t28 :=
  mk28 (a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 : unit).
Lemma congruence_test28 f a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 :
  f a1 = a1 ->
  mk28 (f a1)  a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 =
  mk28 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28.
Proof. time congruence. Qed.

(*
 Looks exponential. The number of terms should be Θ(n^2) (all partially applied
`mk`s). So, the basic Nelson-Oppen should take time O(n^4) and
Downey-Sethi-Tarjan should take time O(n^2 log(n)) (despite the documentation
saying `congruence` uses the former, the implementation actually does the
latter).

Tactic call ran for 0. secs (0.u,0.s) (success)
Tactic call ran for 0. secs (0.u,0.s) (success)
Tactic call ran for 0. secs (0.u,0.s) (success)
Tactic call ran for 0. secs (0.u,0.s) (success)
Tactic call ran for 0. secs (0.u,0.s) (success)
Tactic call ran for 0. secs (0.u,0.s) (success)
Tactic call ran for 0. secs (0.u,0.s) (success)
Tactic call ran for 0. secs (0.u,0.s) (success)
Tactic call ran for 0.001 secs (0.001u,0.s) (success)
Tactic call ran for 0.001 secs (0.001u,0.s) (success)
Tactic call ran for 0.002 secs (0.002u,0.s) (success)
Tactic call ran for 0.007 secs (0.007u,0.s) (success)
Tactic call ran for 0.007 secs (0.007u,0.s) (success)
Tactic call ran for 0.013 secs (0.013u,0.s) (success)
Tactic call ran for 0.025 secs (0.025u,0.s) (success)
Tactic call ran for 0.05 secs (0.05u,0.s) (success)
Tactic call ran for 0.105 secs (0.105u,0.s) (success)
Tactic call ran for 0.22 secs (0.22u,0.s) (success)
Tactic call ran for 0.456 secs (0.455u,0.s) (success)
Tactic call ran for 0.95 secs (0.948u,0.s) (success)
Tactic call ran for 1.916 secs (1.912u,0.s) (success)
Tactic call ran for 3.976 secs (3.968u,0.s) (success)
Tactic call ran for 8.272 secs (8.256u,0.s) (success)
Tactic call ran for 16.757 secs (16.723u,0.001s) (success)
Tactic call ran for 34.58 secs (34.512u,0.s) (success)
Tactic call ran for 72.507 secs (72.361u,0.s) (success)
Tactic call ran for 144.8 secs (144.525u,0.s) (success)
Tactic call ran for 304.017 secs (303.14u,0.005s) (success)
*)
