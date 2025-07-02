#!/usr/bin/env python3


def print_lem(n):
    all_args = " ".join([f"a{i + 1}" for i in range(n)])
    print(f"Lemma congruence_test{n} f g ({all_args} : unit) :")
    print("  f = g ->")
    print(f"  @eq unit (f {all_args}) (g {all_args}).")
    print("Proof. time congruence. Qed.")
    print("")


for i in range(1, 100):
    print_lem(i)

print("""
(*
  Looks exponential. The number of terms should be Θ(n^2) (all partially applied
`mk`s). So, the basic Nelson-Oppen should take time O(n^4) and
Downey-Sethi-Tarjan should take time O(n^2 log(n)) (despite the documentation
saying `congruence` uses the former, the implementation actually does the
latter). *)
""")
