## ahead of time:
##   export PYTHONPATH=/home/nickolai/refsrc/z3/build/python
##   export PYTHONPATH=$PWD/pyrpcgen

import json
import json_eval
import json_sym
import z3
import nfs_trace
import rfc1813

# z3.set_param("smt.string_solver", "z3str3")

with open('NFS3API.json') as f:
  code = f.read()
  j = json.loads(code)

jc = json_eval.Context()
jc.load(j)

m = jc.get_module('Main')

stateType = m.get_type("state")

sym = json_sym.SymbolicJSON(jc)
sym.register_base_type("nat", lambda args: z3.IntSort())
sym.register_base_type("string", lambda args: z3.StringSort())
sym.register_base_type("gmap", lambda args: z3.ArraySort(sym.z3_sort(args[0]),
  sym.z3_sort({
    'what': 'type:glob',
    'name': 'option',
    'args': [args[1]],
    'mod': m,
  })))
sym.register_base_type("buf", lambda args: z3.SeqSort(z3.BitVecSort(8)))
# sym.register_base_type("list", lambda args: z3.SeqSort(sym.z3_sort(args[0])))
# XXX hack: list is always of inode_state
sym.register_base_type("list", lambda args: z3.SeqSort(sym.z3_sort({
  'what': 'type:glob',
  'name': 'inode_state',
  'args': [],
  'mod': m,
})))
sym.register_base_type("fh", lambda args: z3.StringSort())
sym.register_base_type("uint32", lambda args: z3.BitVecSort(32))
sym.register_base_type("uint64", lambda args: z3.BitVecSort(64))

### Fix later
sym.register_base_type("fileid", lambda args: z3.BitVecSort(64))
sym.register_base_type("createverf", lambda args: z3.BitVecSort(64))
sym.register_base_type("writeverf", lambda args: z3.BitVecSort(64))

sym.set_bool_type(m.get_type("bool"))
sym.set_sumbool_type(m.get_type("sumbool"))
sym.set_unit_tt(sym.z3_sort(m.get_type("unit")).constructor(0)())

m.redefine_term('gmap_lookup', {
  'what': 'expr:lambda',
  'argnames': ['unused0', 'unused1'],
  'body': {
    'what': 'expr:special',
    'id': 'gmap_lookup',
  },
})
m.redefine_term('map_insert', {
  'what': 'expr:lambda',
  'argnames': ['unused0'],
  'body': {
    'what': 'expr:special',
    'id': 'map_insert',
  },
})
for id in ('eq_dec_fh', 'len_buf', 'eqDec_time', 'u64_zero', 'eq_dec_inode_state', 'countable_inode_state', 'u32_zero', 'countable_fh', 'resize_buf', 'uint64_gt', 'uint32_gt', 'uint32_eq',):
  m.redefine_term(id, {
    'what': 'expr:special',
    'id': id,
  })

# stateSort = sym.z3_sort(stateType)
# s0 = z3.Const('s0', stateSort)
#
#
# getattr_step, _ = m.get_term("getattr_step")
#
# arg = z3.String('fh')
#
# expr = {
#   'what': 'expr:apply',
#   'args': [arg],
#   'func': getattr_step,
# }
#
# getattr_step_fh = jc.reduce(expr)
#
# s1, res = sym.proc(getattr_step_fh, s0)
# print s1
# print res
#
# ERR_PERM = res.sort().accessor(1, 1)(res).sort().constructor(0)()
#
# s = z3.Solver()
# # s.add(s0 != s1)
# # s.add(res.sort().recognizer(0)(res))
# s.add(res.sort().recognizer(1)(res))
# s.add(res.sort().accessor(1, 1)(res) == ERR_PERM)
# print 'Check:', s.check()


stateSort = sym.z3_sort(stateType)
current_state = z3.Const('s_init', stateSort)

## Invariant: GETATTR cannot return both ERR_STALE and OK in the same state
fh = z3.String("getattr_fh")
getattr_step, _ = m.get_term("getattr_step")
step = jc.reduce({
  'what': 'expr:apply',
  'args': [fh],
  'func': getattr_step,
})
_, res0 = sym.proc(step, current_state)
_, res1 = sym.proc(step, current_state)
s = z3.Solver()
s.add(res0.sort().recognizer(0)(res0))
s.add(res1.sort().recognizer(1)(res1))
assert(s.check() == z3.unsat)



def lift_ftype(t):
  ftypeSort = sym.z3_sort(m.get_type("ftype"))
  if t == rfc1813.const.NF3REG:
    return json_sym.constructor_by_name(ftypeSort, "NF3REG")()
  elif t == rfc1813.const.NF3DIR:
    return json_sym.constructor_by_name(ftypeSort, "NF3DIR")()
  else:
    raise Exception("unknown ftype", t)

def lift_u32(v):
  return z3.BitVecVal(v, 32)

def lift_u64(v):
  return z3.BitVecVal(v, 64)

def lift_time(t):
  timeSort = sym.z3_sort(m.get_type("time"))
  return timeSort.constructor(0)(lift_u32(t.seconds), lift_u32(t.nseconds))

def lift_major_minor(t):
  mmSort = sym.z3_sort(m.get_type("major_minor"))
  return mmSort.constructor(0)(lift_u32(t.specdata1), lift_u32(t.specdata2))

def lift_fattr3(fattr3):
  fattrSort = sym.z3_sort(m.get_type("fattr"))
  return fattrSort.constructor(0)(
    lift_ftype(fattr3.ftype),
    lift_u32(fattr3.mode),
    lift_u32(fattr3.nlink),
    lift_u32(fattr3.uid),
    lift_u32(fattr3.gid),
    lift_u64(fattr3.size),
    lift_u64(fattr3.used),
    lift_major_minor(fattr3.rdev),
    lift_u64(fattr3.fsid),
    lift_u64(fattr3.fileid),
    lift_time(fattr3.atime),
    lift_time(fattr3.mtime),
    lift_time(fattr3.ctime))

s = z3.Solver()
s.set(**{"solver.smtlib2_log": "filename.smt2"})

trace = nfs_trace.call_reply_pairs("./nfs.pcap")
for (proc, call, reply) in trace:
  if proc == 1: #getattr
    arg = z3.StringVal(call.object.data)
    LAST_FH = arg
    getattr_step, _ = m.get_term("getattr_step")
    step = jc.reduce({
      'what': 'expr:apply',
      'args': [arg],
      'func': getattr_step,
    })
    next_state, spec_res = sym.proc(step, current_state)
    # next_state, badspec_res = sym.proc(step, current_state)

    # print "spec_res:", spec_res.sexpr()
    # print "trace reply:", reply

    rs = spec_res.sort()
    if reply.status == rfc1813.const.NFS3_OK:
      arg0sort = rs.accessor(0, 0)(spec_res).sort()
      arg1sort = rs.accessor(0, 1)(spec_res).sort()
      arg0 = arg0sort.constructor(0)()
      arg1 = lift_fattr3(reply.resok.obj_attributes)
      reply_res = rs.constructor(0)(arg0, arg1)

      # arg1sort = rs.accessor(1, 1)(spec_res).sort()
      # badarg1 = json_sym.constructor_by_name(arg1sort, "ERR_STALE")()
      # badreply_res = rs.constructor(1)(arg0, badarg1)
      # reply_res, badreply_res = badreply_res, reply_res
    else:
      reply_res = rs.constructor(1)
      raise Exception("error not supported")

    spec_res = z3.simplify(spec_res)
    next_state = z3.simplify(next_state)

    # print "SPEC_RES:"
    # print spec_res.sexpr()

    # print "REPLY_RES:"
    # print reply_res.sexpr()

    s.add(spec_res == reply_res)
    print s.check()

    # s.add(badspec_res == badreply_res)
    # print s.check()
  else:
    raise Exception("unknown proc", proc)

  current_state = next_state

print s.check()


## symbolic nfs server: ask for satisfying assignment for new RPC call
current_state = z3.Const('s_init', stateSort)

print "SYMBOLIC NFS SERVER"
if False:
  arg = z3.String("getattr_fh")
  getattr_step, _ = m.get_term("getattr_step")
  step = jc.reduce({
    'what': 'expr:apply',
    'args': [arg],
    'func': getattr_step,
  })
else:
  arg0 = z3.String("setattr_fh")
  arg1 = z3.Const("setattr_sattr", sym.z3_sort(m.get_type("sattr")))
  option_time = {
    "what": "type:glob",
    "name": "option",
    "mod": m,
    "args": [{
      "what": "type:glob",
      "name": "time",
      "mod": m,
      "args": [],
    }],
  }
  arg2 = z3.Const("setattr_ctime_guard", sym.z3_sort(option_time))
  setattr_step, _ = m.get_term("setattr_step")
  step = jc.reduce({
    'what': 'expr:apply',
    'args': [arg0, arg1, arg2],
    'func': setattr_step,
  })

next_state, spec_res = sym.proc(step, current_state)
spec_res = z3.simplify(spec_res)
print "SETATTR SPEC_RES:", spec_res.sexpr()
the_response = z3.Const('the_response', spec_res.sort())
s.add(the_response == spec_res)

while s.check() == z3.sat:
  print "Synthetisizing response"
  m = s.model()
  this_response = m[the_response]
  print this_response
  s.add(the_response != this_response)
