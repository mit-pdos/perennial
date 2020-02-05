## ahead of time:
##   export PYTHONPATH=/home/nickolai/z3/build/python

import json
import z3

class Module(object):
  def __init__(self, j, context):
    self.types = {}
    self.decls = {}
    self.constructors = {}
    self.json_to_sort = {}

    self.modname = j['name']
    self.context = context

    for d in j['declarations']:
      if d['what'] == 'decl:ind':
        self.types[d['name']] = d
        for c in d['constructors']:
          self.constructors[c['name']] = {
            'typename': d['name'],
            'argtypes': c['argtypes'],
          }
      if d['what'] == 'decl:term':
        self.decls[d['name']] = d
      if d['what'] == 'decl:type':
        self.types[d['name']] = d['value']

  def z3_sort(self, typename, typeargs = []):
    mod, typename = self.context.scope_name(typename, self)
    t = mod.types[typename]
    return mod._z3_sort(t, typeargs)

  def execute(self, name, args):
    mod, name = self.context.scope_name(name, self)
    if name in mod.decls:
      d = mod.decls[name]

      namespace = {}
      dvalue = d['value']

      for (idx, argname) in enumerate(dvalue['argnames']):
        namespace[argname] = args[idx]

      dbody = dvalue['body']
      return mod._execute(dbody, namespace)

    if name in mod.constructors:
      print "Looking up constructor", name
      c = mod.constructors[name]
      t = mod.z3_sort(c['typename'])
      idx = self._constructor_by_name(t, name)
      z3c = t.constructor(idx)
      return z3c(*args)

    print "execute(): unknown name", name, "in module", mod.modname

  def proc_expr(self, name, args, state):
    mod, name = self.context.scope_name(name, self)
    if name in mod.decls:
      d = mod.decls[name]

      namespace = {}
      dvalue = d['value']

      for (idx, argname) in enumerate(dvalue['argnames']):
        namespace[argname] = args[idx]

      dbody = dvalue['body']
      return mod._proc_expr(dbody, namespace, state)

    print "proc_expr(): unknown name", name, "in module", mod.modname

  def _type_var_lookup(self, typeargnames, x):
    if x['what'] == 'type:var':
      return typeargnames[x['name']]
    return x

  def _z3_sort(self, json_type, typeargs = [], typeargnames = {}):
    # print "Looking up type %s (%s, %s): %s" % (json_type['name'], typeargs, typeargnames, json_type)

    ## Hard-coded Z3 correspondence for some types
    if json_type['name'] == 'nat':
      return z3.IntSort()

    if json_type['name'] == 'string':
      return z3.StringSort()

    if json_type['name'] == 'gmap':
      return z3.ArraySort(self._z3_sort(json_type['args'][0]),
                          self._z3_sort(json_type['args'][1]))

    if json_type['what'] == 'type:var':
      t = typeargnames[json_type['name']]
      return self._z3_sort(t)

    if json_type['what'] == 'type:glob':
      if json_type['name'] == 'buf':
        return z3.SeqSort(z3.BitVecSort(8))

      return self.z3_sort(json_type['name'], [self._type_var_lookup(typeargnames, x) for x in json_type['args']])

    if str(json_type) in self.json_to_sort:
      return self.json_to_sort[str(json_type)]

    if json_type['name'] == 'list':
      return z3.SeqSort(self._z3_sort(typeargs[0]))

    datatype = z3.Datatype(str(json_type['name']))
    typeargnames = {}
    for i in range(0, len(typeargs)):
      typeargname = json_type['argnames'][i]
      typeargnames[typeargname] = typeargs[i]
    for c in json_type['constructors']:
      cname = str(c['name'])
      datatype.declare(cname, *[(cname + '_%d' % idx, self._z3_sort(argtype, [], typeargnames))
                                for (idx, argtype) in enumerate(c['argtypes'])])

    t = datatype.create()
    self.json_to_sort[str(json_type)] = t
    return t

  def _constructor_by_name(self, sort, cname):
    for i in range(0, sort.num_constructors()):
      if sort.constructor(i).name() == cname:
        return i
    print "Unknown constructor", sort, cname
    return None

  def _execute(self, expr, namespace):
    print "NAMESPACE: f =", namespace.get('f', None)

    while expr['what'] == 'expr:coerce':
      expr = expr['value']

    if expr['what'] == 'expr:case':
      victim = self._execute(expr['expr'], namespace)
      symExpr = None

      for case in expr['cases']:
        case_namespace = namespace.copy()
        pat = case['pat']
        if pat['what'] == 'pat:constructor':
          cidx = self._constructor_by_name(victim.sort(), pat['name'])
          patCondition = victim.sort().recognizer(cidx)(victim)
          for (idx, argname) in enumerate(pat['argnames']):
            if argname == '_': continue
            case_namespace[argname] = victim.sort().accessor(cidx, idx)(victim)
        symBody = self._execute(case['body'], case_namespace)
        if symExpr is None:
          symExpr = symBody
        else:
          symExpr = z3.If(patCondition, symBody, symExpr)

      return symExpr
    elif expr['what'] == 'expr:rel':
      return namespace[expr['name']]
    elif expr['what'] == 'expr:constructor':
      ## Special case for nat 0
      if expr['name'] == 'O':
        return 0

      args = [self._execute(a, namespace) for a in expr['args']]
      return self.execute(expr['name'], args)
    elif expr['what'] == 'expr:apply':
      ## Chase down the func
      f = expr['func']
      print "APPLY", f, "TO", expr['args'], "IN NAMESPACE", namespace
      while True:
        if f['what'] == 'expr:global':
          if f['name'] == 'lookup0':
            break
          mod, name = self.context.scope_name(f['name'], self)
          f = mod.decls[name]
        elif f['what'] == 'expr:coerce':
          f = f['value']
        elif f['what'] == 'decl:term':
          f = f['value']
        elif f['what'] == 'expr:rel':
          f = namespace[f['name']]
        else:
          break

      posargs = []
      for i in range(len(expr['args'])):
        a = expr['args'][i]
        while True:
          if type(a) != dict:
            break
          if a['what'] == 'expr:rel':
            a = namespace[a['name']]
          elif a['what'] == 'expr:coerce':
            a = a['value']
          else:
            break
        posargs.append(a)

      if f['what'] == 'expr:global':
        if f['name'] == 'lookup0':
          m = self._execute(posargs[2], namespace)
          k = posargs[1]
          return m[k]

      assert(f['what'] == 'expr:lambda')
      apply_namespace = {k: v for k, v in namespace.items()}
      assert(len(expr['args']) == len(f['argnames']))
      for i in range(len(posargs)):
        apply_namespace[f['argnames'][i]] = posargs[i]

      return self._execute(f['body'], apply_namespace)
    else:
      print "_execute unmatched: %s" % expr['what']

    print "_execute(%s) returning None" % str(expr)
    return None

  def _proc_expr(self, expr, namespace, state):
    print "PROC_EXPR: %s" % expr
    print "NAMESPACE: f =", namespace.get('f', None)

    while expr['what'] == 'expr:coerce':
      expr = expr['value']

    if expr['what'] == 'expr:apply':
      ## Chase down the func
      f = expr['func']
      while True:
        if f['what'] == 'expr:global':
          mod, name = self.context.scope_name(f['name'], self)
          f = mod.decls[name]
        elif f['what'] == 'expr:coerce':
          f = f['value']
        elif f['what'] == 'decl:term':
          f = f['value']
        else:
          break

      assert(f['what'] == 'expr:lambda')

      print "NAMESPACE: f =", namespace.get('f', None)
      apply_namespace = {k: v for k, v in namespace.items()}
      print "APPLY_NAMESPACE: f =", apply_namespace.get('f', None)
      print "LAMBDA:", f
      print "LAMBDA ARGNAMES:", f['argnames']
      assert(len(expr['args']) == len(f['argnames']))

      for i in range(len(expr['args'])):
        a = expr['args'][i]
        while True:
          if type(a) != dict:
            break
          if a['what'] == 'expr:rel':
            a = namespace[a['name']]
          elif a['what'] == 'expr:coerce':
            a = a['value']
          else:
            break
        apply_namespace[f['argnames'][i]] = a

      print "APPLY_NAMESPACE: f =", apply_namespace.get('f', None)
      return self._proc_expr(f['body'], apply_namespace, state)
    elif expr['what'] == 'expr:constructor':
      if expr['name'] == 'Bind':
        p1 = expr['args'][0]
        p2 = expr['args'][1]
        state1, res1 = self._proc_expr(p1, namespace, state)
        p2apply = {
          'what': 'expr:apply',
          'func': p2,
          'args': [res1],
        }
        print "BIND PART 1 STATE:", state1
        print "BIND PART 1 RES:", res1
        return self._proc_expr(p2apply, namespace, state1)
      elif expr['name'] == 'Ret':
        res = self._execute(expr['args'][0], namespace)
        return state, res
      elif expr['name'] == 'Call':
        argname = expr['args'][0]['name']
        if argname == 'Reads':
          return state, state
        else:
          print "Unsupported call op %s" % argname
      else:
        print "Unsupported constructor %s" % expr['name']

    print "_proc_expr(%s) returning None" % expr['what']
    return None

class SymbolicJSON(object):
  def __init__(self):
    self.modules = {}

  def load(self, pn):
    with open(pn) as f:
      code = f.read()
      j = json.loads(code)

    for modname in j['used_modules']:
      if modname not in self.modules:
        raise Exception("Module %s needed but not loaded yet" % modname)

    self.modules[j['name']] = Module(j, self)

  def scope_name(self, name, module_context):
    if '.' in name:
      modname, localname = name.split('.')
      return self.modules[modname], localname
    else:
      return module_context, name

if __name__ == "__main__":
  test = SymbolicJSON()
  test.load('NFS3API.json')
  s = z3.Const('s', test.modules['Main'].z3_sort('state'))
  fh = z3.Const('fh', test.modules['Main'].z3_sort('fh'))

  print test.modules['Main'].proc_expr('getattr_step', [fh], s)
