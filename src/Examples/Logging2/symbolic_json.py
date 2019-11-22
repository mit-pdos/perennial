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
      c = mod.constructors[name]
      t = mod.z3_sort(c['typename'])
      idx = self._constructor_by_name(t, name)
      z3c = t.constructor(idx)
      return z3c(*args)

    print "execute(): unknown name", name, "in module", mod.modname

  def _type_var_lookup(self, typeargnames, x):
    if x['what'] == 'type:var':
      return typeargnames[x['name']]
    return x

  def _z3_sort(self, json_type, typeargs = [], typeargnames = {}):
    print "Looking up type %s (%s, %s): %s" % (json_type['name'], typeargs, typeargnames, json_type)

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
    if 'argnames' in json_type:
      for i in range(0, len(json_type['argnames'])):
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

    print "_execute(%s) returning None" % str(expr)
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
  print test.modules['Main'].z3_sort('state')
  s = z3.Const('s', test.modules['Main'].z3_sort('state'))
  # print test.modules['Main'].execute('getFst_sem', [p])
