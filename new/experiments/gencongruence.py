#!/usr/bin/env python3


def print_lem(n):
    all_args = " ".join([f"a{i + 1}" for i in range(n)])
    all_but_first_args = "".join([f" a{i + 2}" for i in range(n - 1)])
    print(f"Inductive t{n} :=")
    print(f"  mk{n} ({all_args} : unit).")
    print(f"Lemma congruence_test{n} f {all_args} :")
    print("  f a1 = a1 ->")
    print(f"  mk{n} (f a1) {all_but_first_args} =")
    print(f"  mk{n} {all_args}.")
    print("Proof. time congruence. Qed.")
    print("")


for i in range(1, 100):
    print_lem(i)
