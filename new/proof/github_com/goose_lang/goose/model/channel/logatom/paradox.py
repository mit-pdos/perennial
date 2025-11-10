#!/usr/bin/env python3
#
# /// script
# dependencies = [
#   "z3-solver",
# ]
# ///

# ruff: noqa: F403, F405
from z3 import *

State = Datatype("State")
State.declare("Init")
State.declare("S1")
State.declare("R1")
State.declare("A")
# State.declare('B')
State.declare("Invalid")
State = State.create()

# chan send = send1; send2, chan recv = recv1; recv2
send1 = Function("send1", State, State)
recv1 = Function("recv1", State, State)
send2 = Function("send2", State, State)
recv2 = Function("recv2", State, State)

s = Solver()
# WOLOG, want to assume they are not equal
s.add(send1(State.Init) == State.S1)
s.add(recv1(State.Init) == State.R1)

# Invalid is like None
s.add(send1(State.Invalid) == State.Invalid)
s.add(recv1(State.Invalid) == State.Invalid)
s.add(send2(State.Invalid) == State.Invalid)
s.add(recv2(State.Invalid) == State.Invalid)

s.add(send1(send1(State.Init)) == State.Invalid)
s.add(recv1(recv1(State.Init)) == State.Invalid)
s.add(send2(send1(State.Init)) == State.Invalid)
s.add(recv2(recv1(State.Init)) == State.Invalid)
s.add(send2(State.Init) == State.Invalid)
s.add(recv2(State.Init) == State.Invalid)
s.add(send2(recv1(State.Init)) == State.Invalid)
s.add(recv2(send1(State.Init)) == State.Invalid)

s.push()
print(
    "Looking for transition systems in which the first operation has two\n"
    + "linearization steps but the second operation only has one\n"
    + "(e.g. `send1; recv1; send2` is complete)"
)

# valid and invalid sequences
s.add(send2(recv1(send1(State.Init))) == State.Init)
s.add(recv2(send1(recv1(State.Init))) == State.Init)
s.add(recv2(recv1(send1(State.Init))) == State.Invalid)
s.add(send2(send1(recv1(State.Init))) == State.Invalid)

if s.check() == sat:
    print("found one:")
    m = s.model()
    print(m)

    f = True
    # find all send1 functions
    for i in range(State.num_constructors()):
        f = And(
            f,
            send1(State.constructor(i)()) == m.eval(send1(State.constructor(i)())),
        )
        f = And(
            f,
            recv1(State.constructor(i)()) == m.eval(recv1(State.constructor(i)())),
        )
        s.add(Not(f))
else:
    print("There is no such transition system")

s.pop()

print("")
print(
    "Looking for transition systems that always requires two linearization\n"
    + "points per operation (e.g. `send1; recv1; send2; recv2` is complete)"
)

# valid
s.add(recv2(send2(recv1(send1(State.Init)))) == State.Init)
s.add(send2(recv2(send1(recv1(State.Init)))) == State.Init)

if s.check() == sat:
    print("found one:")
    m = s.model()
    print(m)
else:
    print("There is no such transition system")
