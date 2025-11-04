#!/usr/bin/env python3

from z3 import *

State = Datatype('State')
State.declare('Init')
State.declare('S1')
State.declare('R1')
State.declare('A')
# State.declare('B')
State.declare('Invalid')
State = State.create()

# chan send = send1; send2, chan recv = recv1; recv2
send1 = Function('send1', State, State)
recv1 = Function('recv1', State, State)
send2 = Function('send2', State, State)
recv2 = Function('recv2', State, State)

def I(op_seq):
    current = State.Init
    last_sent1 = False
    last_recv1= False
    for op in op_seq:
        if op == 's':
            if last_sent1:
                current = send2(current)
            else:
                current = send1(current)
            last_sent1 = not last_sent1
        if op == 'r':
            if last_recv1:
                current = recv2(current)
            else:
                current = recv1(current)
            last_recv1 = not last_recv1
    return current

s = Solver()

# WOLOG, want to assume they are not equal
s.add(send1(State.Init) == State.S1)
s.add(recv1(State.Init) == State.R1)

# valid sequences
s.add(I('srs') == State.Init)
s.add(I('rsr') == State.Init)
s.add(I('srr') == State.Invalid)
s.add(I('rss') == State.Invalid)

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

# NOT STRICTLY NECESSARY
# s.add(I('sr') != I('rs'))

j = 0
while True:
    print(j)
    j+=1
    if s.check() == sat:
        m = s.model()
        print(m)

        f = True
        # find all send1 functions
        for i in range(State.num_constructors()):
            f = And(f, send1(State.constructor(i)()) == m.eval(send1(State.constructor(i)())))
            f = And(f, recv1(State.constructor(i)()) == m.eval(recv1(State.constructor(i)())))
        s.add(Not(f))
    else:
        print("unsat")
        break
