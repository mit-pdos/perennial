class Module(object):
  def __init__(self, j):
    self.types = {}
    self.decls = {}
    self.constructors = {}

    self.modname = j['name']

    for d in j['declarations']:
      self._annotate_globals(d)
      if d['what'] == 'decl:ind':
        self.types[d['name']] = d
        for c in d['constructors']:
          self.constructors[c['name']] = {
            'typename': d['name'],
            'argtypes': c['argtypes'],
          }
      elif d['what'] == 'decl:term':
        d['value'] = rename_binders(d['value'], {})
        self.decls[d['name']] = d
      elif d['what'] == 'decl:type':
        self.types[d['name']] = d['value']
      elif d['what'] == 'decl:fixgroup':
        ## Not handled yet
        pass
      else:
        raise Exception("Unknown declaration", d['what'])

  def _annotate_globals(self, expr):
    if type(expr) == dict:
      if expr.get('what') == 'expr:global':
        expr['mod'] = self
      if expr.get('what') == 'type:glob':
        expr['mod'] = self
      if expr.get('what') == 'expr:constructor':
        expr['mod'] = self
      for k, v in expr.items():
        self._annotate_globals(v)

    if type(expr) == list:
      for v in expr:
        self._annotate_globals(v)

  def redefine_term(self, n, val):
    self.decls[n]['value'] = val

  def get_type(self, n):
    return self.types[n]

  def get_term(self, n):
    t = self.decls[n]
    return t['value'], t['type']

  def get_constructor(self, n):
    return self.constructors[n]

class Context(object):
  def __init__(self):
    self.modules = {}

  def load(self, j):
    m = Module(j)
    self.modules[m.modname] = m

  def get_module(self, n):
    return self.modules[n]

  def reduce(self, expr):
    while True:
      if type(expr) != dict:
        return expr

      if expr['what'] == 'expr:apply':
        f = self.reduce(expr['func'])
        if f['what'] == 'expr:lambda':
          args = expr['args']
          res = apply(f, args[0])
          expr = {
            'what': 'expr:apply',
            'args': args[1:],
            'func': res,
          }
          if len(expr['args']) == 0:
            expr = expr['func']
          continue

      if expr['what'] == 'expr:lambda':
        if len(expr['argnames']) == 0:
          expr = expr['body']
          continue

      if expr['what'] == 'expr:coerce':
        expr = expr['value']
        continue

      if expr['what'] == 'expr:global':
        mod, name = self.scope_name(expr['name'], expr['mod'])
        expr, _ = mod.get_term(name)
        continue

      if expr['what'] == 'type:glob':
        mod, name = self.scope_name(expr['name'], expr['mod'])
        res = mod.get_type(name)
        res = {k: v for k, v in res.items()}
        res['args'] = res.get('args', []) + expr.get('args', [])
        expr = res
        continue

      if expr['what'] == 'decl:ind':
        args = expr.get('args', [])
        if len(args) > 0:
          arg = args[0]
          argname = expr['argnames'][0]

          ## Another hack: what's the type?
          if arg['what'] == 'type:varidx':
            assert(expr['name'] == 'async')
            arg = {
              'what': 'type:glob',
              'mod': expr['constructors'][0]['argtypes'][1]['mod'],
              'name': 'inode_state',
              'args': [],
            }

          res = {
            'what': expr['what'],
            'constructors': subst_what(expr['constructors'], 'type:var', argname, arg),
            'argnames': expr['argnames'][1:],
            'args': expr['args'][1:],
            'name': expr['name'],
            'name_with_args': expr.get('name_with_args', expr['name']) + "_" + arg['name'],
          }
          expr = res
          continue

      if expr['what'] == 'expr:let':
        expr = subst_what(expr['body'], 'expr:rel', expr['name'], expr['nameval'])
        continue

      ## No reductions possible
      return expr

  def scope_name(self, name, module_context):
    if '.' in name:
      modname, localname = name.split('.')
      return self.modules[modname], localname
    else:
      return module_context, name

def subst_what(expr, what, argname, argval):
  if type(expr) == dict:
    if expr.get('what') == what and expr['name'] == argname:
      return argval
    return {k: subst_what(v, what, argname, argval) for k, v in expr.items()}

  if type(expr) == list:
    return [subst_what(v, what, argname, argval) for v in expr]

  return expr

def apply(lam, argval):
  if lam['what'] != 'expr:lambda':
    raise Exception("apply on", lam['what'])

  argname = lam['argnames'][0]
  res = {
    'what': 'expr:lambda',
    'argnames': lam['argnames'][1:],
    'body': subst_what(lam['body'], 'expr:rel', argname, argval),
  }

  if len(res['argnames']) == 0:
    res = res['body']

  return res

def rename_binders(expr, namemap):
  if expr['what'] == 'expr:lambda':
    newnamemap = {k: v for k, v in namemap.items()}
    newargnames = []
    for argname in expr['argnames']:
      n = anon_binder(argname)
      newargnames.append(n)
      newnamemap[argname] = n
    return {
      'what': expr['what'],
      'argnames': newargnames,
      'body': rename_binders(expr['body'], newnamemap),
    }
  elif expr['what'] == 'expr:let':
    newnamemap = {k: v for k, v in namemap.items()}
    n = anon_binder(expr['name'])
    newnamemap[expr['name']] = n
    return {
      'what': expr['what'],
      'name': n,
      'nameval': rename_binders(expr['nameval'], namemap),
      'body': rename_binders(expr['body'], newnamemap),
    }
  elif expr['what'] == 'expr:case':
    newcases = []
    for case in expr['cases']:
      casenamemap = {k: v for k, v in namemap.items()}
      pat = case['pat']
      if pat['what'] == 'pat:constructor':
        newargnames = []
        for argname in pat['argnames']:
          n = anon_binder(argname)
          newargnames.append(n)
          casenamemap[argname] = n
        newpat = {
          'what': pat['what'],
          'name': pat['name'],
          'argnames': newargnames,
        }
      elif pat['what'] == 'pat:wild':
        newpat = pat
      else:
        raise Exception('unhandled pat', pat['what'])
      newcase = {
        'what': case['what'],
        'pat': newpat,
        'body': rename_binders(case['body'], casenamemap),
      }
      newcases.append(newcase)
    return {
      'what': expr['what'],
      #'type': expr['type'],
      'expr': rename_binders(expr['expr'], namemap),
      'cases': newcases,
    }
  elif expr['what'] == 'expr:constructor':
    return {
      'what': expr['what'],
      #'type': expr['type'],
      'mod': expr['mod'],
      'name': expr['name'],
      'args': [rename_binders(a, namemap) for a in expr['args']],
    }
  elif expr['what'] == 'expr:apply':
    return {
      'what': expr['what'],
      'args': [rename_binders(a, namemap) for a in expr['args']],
      'func': rename_binders(expr['func'], namemap),
    }
  elif expr['what'] == 'expr:rel':
    return {
      'what': expr['what'],
      'name': namemap[expr['name']],
    }
  elif expr['what'] == 'expr:global':
    return expr
  elif expr['what'] == 'expr:dummy':
    return expr
  elif expr['what'] == 'expr:axiom':
    return expr
  elif expr['what'] == 'expr:coerce':
    return {
      'what': expr['what'],
      'value': rename_binders(expr['value'], namemap),
    }
  else:
    raise Exception('unknown expr', expr['what'])

anon_binder_ctr = 0
def anon_binder(origname):
  global anon_binder_ctr
  anon_binder_ctr += 1
  return "__anon_binder_%s_%d" % (origname, anon_binder_ctr)
