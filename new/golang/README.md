# Golang for Iris 

The `./defn` directory contains trusted definitions. It specifically
defines the semantics of types, control flow like early return and for loops, and
built-in Go objects such as maps, slices, etc. It is built on top of the minimal
and untyped GooseLang.

The `./theory` directory contains theorems about the Go concepts defined here.
This theory need not be trusted for the most part, since it consists of lemmas
for other libraries to prove higher-level theorems. Parts may be trusted with
respect to a particular top-level theorem if definitions from the theory are
used in the statement of that theorem.
