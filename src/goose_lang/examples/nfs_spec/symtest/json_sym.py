import json_eval
import collections
import z3

class SymbolicJSON(object):
  def __init__(self, context):
    self.context = context
    self.base_types = {}
    self.bool_sort = None
    self.sumbool_sort = None
    self.unit_tt = None

  def set_bool_type(self, t):
    self.bool_sort = self.z3_sort(t)

  def set_sumbool_type(self, t):
    self.sumbool_sort = self.z3_sort(t)

  def set_unit_tt(self, t):
    self.unit_tt = t

  def register_base_type(self, name, z3sort_lam):
    self.base_types[name] = z3sort_lam

  def z3_sort(self, typeexpr):
    ## Check for a base type before reduction, for types
    ## like gmap that we want to avoid unfolding in reduce.
    base_lam = self.base_types.get(typeexpr['name'])
    if base_lam is not None:
      return base_lam(typeexpr['args'])

    typeexpr = self.context.reduce(typeexpr)

    ## Check again for a base type, for types like nat, where
    ## we may have had an alias (like uint32) before.
    base_lam = self.base_types.get(typeexpr['name'])
    if base_lam is not None:
      return base_lam(typeexpr['args'])

    z3name = typeexpr.get('name_with_args', typeexpr['name'])
    datatype = z3.Datatype(str(z3name))
    for c in typeexpr['constructors']:
      cname = str(c['name'])
      datatype.declare(cname, *[(cname + '_%d' % idx, self.z3_sort(argtype))
                                for (idx, argtype) in enumerate(c['argtypes'])])

    t = datatype.create()
    return t

  def proc_apply(self, expr, state):
    f = self.context.reduce(expr['func'])
    args = expr['args']
    if f['what'] == 'expr:special':
      if f['id'] == 'gmap_lookup':
        state, k = self.proc(args[0], state)
        state, m = self.proc(args[1], state)
        return state, m[k]
      elif f['id'] == 'map_insert':
        state, k = self.proc(args[0], state)
        state, v = self.proc(args[1], state)
        state, m = self.proc(args[2], state)

        rangesort = m.range()
        vsome = constructor_by_name(rangesort, "Some")(v)

        return state, z3.Store(m, k, vsome)
      elif f['id'] == 'len_buf':
        state, buf = self.proc(args[0], state)
        return state, z3.Int2BV(z3.Length(buf), 64)
      elif f['id'] == 'resize_buf':
        state, newlen = self.proc(args[0], state)
        state, buf = self.proc(args[1], state)
        ## XXX should be of length newlen, not empty..
        return state, z3.Empty(buf.sort())
      elif f['id'] == 'uint64_gt':
        state, a0 = self.proc(args[0], state)
        state, a1 = self.proc(args[1], state)
        return state, z3.If(a0 > a1, self.bool_sort.constructor(0)(), self.bool_sort.constructor(1)())
      elif f['id'] == 'eqDec_time':
        state, a0 = self.proc(args[0], state)
        state, a1 = self.proc(args[1], state)
        return state, z3.If(a0 == a1, self.sumbool_sort.constructor(0)(), self.sumbool_sort.constructor(1)())
      else:
        raise Exception('unknown special function', f['id'])
    else:
      print expr
      raise Exception('unknown apply on', f['what'])

  def proc_case(self, expr, state):
    state, victim = self.proc(expr['expr'], state)
    resstate = None
    resvalue = None

    for case in expr['cases'][::-1]:
      pat = case['pat']
      if pat['what'] == 'pat:constructor':
        body = case['body']
        cidx = constructor_idx_by_name(victim.sort(), pat['name'])
        patCondition = victim.sort().recognizer(cidx)(victim)
        for (idx, argname) in enumerate(pat['argnames']):
          if argname == '_': continue
          val = victim.sort().accessor(cidx, idx)(victim)
          body = json_eval.subst_what(body, 'expr:rel', argname, val)
        patstate, patbody = self.proc(body, state)
        if resstate is None:
          resstate = patstate
          resvalue = patbody
        else:
          resstate = z3.If(patCondition, patstate, resstate)
          resvalue = z3.If(patCondition, patbody, resvalue)
      elif pat['what'] == 'pat:wild':
        if resstate is not None:
          raise Exception('wildcard not the last pattern')
        resstate, resvalue = self.proc(case['body'], state)
      else:
        raise Exception('unknown pattern type', pat['what'])

    return resstate, resvalue

  def proc(self, procexpr, state):
    procexpr0 = procexpr
    procexpr = self.context.reduce(procexpr)

    while True:
      if type(procexpr) != dict:
        return state, procexpr

      if procexpr['what'] == 'expr:apply':
        state, procexpr = self.proc_apply(procexpr, state)
        continue

      if procexpr['what'] == 'expr:case':
        state, procexpr = self.proc_case(procexpr, state)
        continue

      if procexpr['what'] == 'expr:constructor':
        mod, name = self.context.scope_name(procexpr['name'], procexpr['mod'])
        c = mod.get_constructor(name)
        print name, c
        # XXX todo
        state, procexpr = self.proc_constructor_proc(procexpr, state)
        continue

      # XXX todo axioms
      if procexpr['what'] == 'expr:special':
        if procexpr['id'] == 'u64_zero':
          procexpr = 0
          continue
        elif procexpr['id'] == 'u32_zero':
          procexpr = 0
          continue

        else:
          raise Exception("unknown special", procexpr['id'])

      print procexpr0
      raise Exception("proc() on unexpected thing", procexpr['what'])

  def proc_constructor_other(self, procexpr, state):
    other_state_sort = self.z3_sort({
        'what': 'type:glob',
        'mod': procexpr['mod'],
        'args': [],
        'name': 'other',
      })
    cid = constructor_idx_by_name(other_state_sort, procexpr['name'])

    cargs = []
    for arg in procexpr['args']:
      state, carg = self.proc(arg, state)
      cargs.append(carg)

    return state, sort.constructor(cid)(*cargs)
  '''
    t = procexpr['type']

    if t['name'] == 'list':
      ## What a hack: lists are always of inode_state
      inode_state_sort = self.z3_sort({
        'what': 'type:glob',
        'mod': procexpr['mod'],
        'args': [],
        'name': 'inode_state',
      })
      if procexpr['name'] == 'Nil':
        return state, z3.Empty(z3.SeqSort(inode_state_sort))

    if t['name'] == 'res':
      ## What a hack: guess the type arguments for `res`...

      # print "RES ARG 0:", procexpr['args'][0]
      # print "RES ARG 1:", procexpr['args'][1]

      if procexpr['args'][0]['name'] == 'Tt':
        t['args'][0] = {'what': 'type:glob', 'mod': t['mod'], 'name': 'unit'}
        t['args'][1] = {'what': 'type:glob', 'mod': t['mod'], 'name': 'fattr'}
      else:
        t['args'][0] = {'what': 'type:glob', 'mod': t['mod'], 'name': 'wcc_data'}
        t['args'][1] = {'what': 'type:glob', 'mod': t['mod'], 'name': 'unit'}
    sort = self.z3_sort(t)
    cid = constructor_idx_by_name(sort, procexpr['name'])

    cargs = []
    for arg in procexpr['args']:
      state, carg = self.proc(arg, state)
      cargs.append(carg)

    return state, sort.constructor(cid)(*cargs)
'''

  def proc_constructor_proc(self, procexpr, state):
    if procexpr['name'] == 'Bind':
      p0 = procexpr['args'][0]
      p1lam = procexpr['args'][1]

      state0, res0 = self.proc(p0, state)
      p1 = {
        'what': 'expr:apply',
        'args': [res0],
        'func': p1lam,
      }
      return self.proc(p1, state0)
    elif procexpr['name'] == 'SuchThatBool':
      procexpr['args']['']
    #elif procexpr['name'] == 'Ret':
      retval = self.context.reduce(procexpr['args'][0])
      return state, retval
    elif procexpr['name'] == 'RunF':
      callop = self.context.reduce(procexpr['args'][0])
      if callop['what'] != 'expr:constructor':
        raise Exception("callop expected constructor, got", callop['what'])

      if callop['name'] == 'Reads':
        return state, state
      elif callop['name'] == 'SymBool':
        return state, z3.Const(anon(), self.bool_sort)
      elif callop['name'] == 'SymU32':
        return state, z3.Const(anon(), z3.BitVecSort(32))
      elif callop['name'] == 'SymU64':
        return state, z3.Const(anon(), z3.BitVecSort(64))
      elif callop['name'] == 'Assert':
        # XXX how to add a solver constraint?
        return state, self.unit_tt
      elif callop['name'] == 'Puts':
        _, newstate = self.proc(callop['args'][0], state)
        return newstate, self.unit_tt
      else:
        raise Exception("unexpected callop constructor", callop['name'])
    else:
      raise Exception("unexpected proc constructor", procexpr['name'])

def constructor_idx_by_name(sort, cname):
  for i in range(0, sort.num_constructors()):
    if sort.constructor(i).name() == cname:
      return i
  raise Exception("Unknown constructor", sort, cname)

def constructor_by_name(sort, cname):
  return sort.constructor(constructor_idx_by_name(sort, cname))

anonctr = 0
def anon():
  global anonctr
  anonctr += 1
  return "anon%d" % anonctr
