#!/usr/bin/env python3

from z3 import *

State = Datatype('State')
State.declare('Init')
State.declare('S1')
State.declare('R1')
State.declare('A')
State.declare('B')
State.declare('Invalid')
State = State.create()

# chan send = send1; send2, chan recv = recv1; recv2
send1 = Function('send1', State, State)
recv1 = Function('recv1', State, State)
send2 = Function('send2', State, State)
recv2 = Function('recv2', State, State)

def I(op_seq):
    current = State.Init
    last_sent1_state = None
    last_recv1_state = None
    for op in op_seq:
        if op == 's':
            if last_sent1_state is not None:
                current = send2(last_sent1_state, current)
                last_sent1_state = None
            else:
                current = send1(current)
                last_sent1_state = current
        if op == 'r':
            if last_recv1_state is not None:
                current = recv2(last_recv1_state, current)
                last_recv1_state = None
            else:
                current = recv1(current)
                last_recv1_state = current
    return current

s = Solver()

# WOLOG, want to assume they are not equal
s.add(send1(State.Init) == State.S1)
s.add(recv1(State.Init) == State.R1)

# valid sequences
s.add(I('srsr') == State.Init)
s.add(I('srsr') == I('srsrsrsr'))
s.add(I('srsr') == I('srrs'))
s.add(I('srrs') == I('rsrs'))
s.add(I('rsrs') == I('rssr'))
s.add(I('rssr') == I('srsr'))

st = Const('st', State)

# Invalid is like None
s.add(send1(State.Invalid) == State.Invalid)
s.add(recv1(State.Invalid) == State.Invalid)
s.add(ForAll([st], send2(st, State.Invalid) == State.Invalid))
s.add(ForAll([st], recv2(st, State.Invalid) == State.Invalid))

s.add(send1(send1(State.Init)) == State.Invalid)
s.add(recv1(recv1(State.Init)) == State.Invalid)
s.add(ForAll([st], send2(st, State.Init) == State.Invalid))
s.add(ForAll([st], recv2(st, State.Init) == State.Invalid))
s.add(ForAll([st], send2(st, recv1(State.Init)) == State.Invalid))
s.add(ForAll([st], recv2(st, send1(State.Init)) == State.Invalid))

s.add(I('ss') == State.Invalid)
s.add(I('rr') == State.Invalid)
s.add(I('srss') == State.Invalid)
s.add(I('rsrr') == State.Invalid)
s.add(I('rsss') == State.Invalid)
s.add(I('srrr') == State.Invalid)

j = 0
while True:
    print(j)
    j+=1
    if s.check() == sat:
        m = s.model()
        print(m)
        print(m.eval(I('rss')))

        f = True
        # find all send1 functions
        for i in range(State.num_constructors()):
            f = And(f, send1(State.constructor(i)()) == m.eval(send1(State.constructor(i)())))
            f = And(f, recv1(State.constructor(i)()) == m.eval(recv1(State.constructor(i)())))
        s.add(Not(f))
    else:
        print("unsat")
        break
