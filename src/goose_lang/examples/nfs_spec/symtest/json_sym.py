import pprint
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
        self.last_option_type = None
        self.res_type = 'unit'
        self.opt_type = 'unit'

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
        ## for something like positive, this can cause infinite recursion
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
            # for converting Z to u32
            if f['id'] == 'u3' or f['id'] == 'u2':
                arg = args[0]
                # be able to distinguish between Z->u32 and Z->u64
                if f['id'] == 'u3':
                    arg['name'] = 'u32'
                else:
                    arg['name'] = 'u64'
                state, val = self.proc(arg, state)
                return state, z3.Const(anon(), val)

            elif f['id'] == 'gtb':
                arg0 = args[0]['cases'][0]['body']['args'][0]
                nstate, arg1 = self.proc(args[1]['cases'][0]['body']['args'][0], state)
                print arg0, arg1
                return nstate, z3.If(arg0 > arg1, self.bool_sort.constructor(0)(), self.bool_sort.constructor(1)())

            elif f['id'] == 'gmap_lookup':
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

            elif f['id'] == 'reads':
                return state, state

            elif f['id'] == 'modify':
                pprint.pprint(args)
                _, newstate = self.proc(args[0]['body'], state)
                return newstate, self.unit_tt

            elif f['id'] == 'ret':
                state, res = self.proc(args[0], state)
                return state, res

            elif f['id'] == 'len_buf':
                state, buf = self.proc(args[0], state)
                return state, z3.Int2BV(z3.Length(buf), 64)

            elif f['id'] == 'resize_buf':
                state, newlen = self.proc(args[0], state)
                state, buf = self.proc(args[1], state)
                ## XXX should be of length newlen, not empty..
                return state, z3.Empty(buf.sort())

            elif f['id'] == 'eqDec_time':
                state, a0 = self.proc(args[0], state)
                state, a1 = self.proc(args[1], state)
                return state, z3.If(a0 == a1, self.sumbool_sort.constructor(0)(), self.sumbool_sort.constructor(1)())

            elif f['id'] == 'time_ge':
                state, a0 = self.proc(args[0], state)
                state, a1 = self.proc(args[1], state)
                # constructor 0 is true, 1 is false
                return state, z3.If(a0 >= a1, self.bool_sort.constructor(0)(), self.bool_sort.constructor(1)())

            elif f['id'] == 'symAssert':
                state, a = self.proc(args[0], state)
                return state, z3.And(a == self.bool_sort.constructor(0)())

            else:
                raise Exception('unknown special function', f['id'])
        else:
            raise Exception('unknown apply on', f['what'])

    def proc_case(self, expr, state):
        state, victim = self.proc(expr['expr'], state)
        resstate = None
        resvalue = None

        # process wildcard case first
        cases = expr['cases']
        if cases[-1]['pat']['what'] == 'pat:wild':
            cases.insert(0, cases.pop(-1))
        print "CASES"
        pprint.pprint(cases)

        for case in cases:
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
                    print "CASE PATBODY, RESVALUE: ", patbody.sort(), resvalue.sort()
                    pprint.pprint(patbody)
                    pprint.pprint(resvalue)
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
            print "-------------------- NEW PROC ----------------------"
            pprint.pprint(procexpr)
            if type(procexpr) != dict:
                return state, procexpr

            if procexpr['what'] == 'expr:apply':
                state, procexpr = self.proc_apply(procexpr, state)
                continue

            if procexpr['what'] == 'expr:case':
                state, procexpr = self.proc_case(procexpr, state)
                continue

            if procexpr['what'] == 'expr:constructor':
                state, procexpr = self.proc_constructor(procexpr, state)
                continue

            # axioms
            if procexpr['what'] == 'expr:special':
                if procexpr['id'] == 'symBool':
                    return state, z3.Const(anon(), self.bool_sort)
                if procexpr['id'] == 'symU32':
                    return state, z3.Const(anon(), z3.BitVecSort(32))
                if procexpr['id'] == 'symU64':
                    return state, z3.Const(anon(), z3.BitVecSort(64))
                if procexpr['id'] == 'u64':
                    return state, z3.Const(anon(), z3.BitVecSort(64))
                if procexpr['id'] == 'u32':
                    return state, z3.Const(anon(), z3.BitVecSort(32))
                if procexpr['id'] == 'undefined':
                    return state, z3.Const(anon(), z3.BitVecSort(64))

                else:
                    raise Exception("unknown special", procexpr['id'])

            raise Exception("proc() on unexpected thing", procexpr['what'])

    def proc_constructor(self, procexpr, state):
        if procexpr['name'] == 'Bind':
            p0 = procexpr['args'][0]
            p1lam = procexpr['args'][1]
            #print "-------------------- BIND PROC ----------------------", p0
            state0, res0 = self.proc(p0, state)
            p1 = {
                'what': 'expr:apply',
                'args': [res0],
                'func': p1lam,
            }
            return self.proc(p1, state0)

        if procexpr['name'] == 'Tt':
            return state, self.unit_tt

        t = {}
        if "ERR" in procexpr['name']:
            t = {'what': 'type:glob', 'mod': procexpr['mod'], 'name': 'err', 'args' : []}

        elif procexpr['name'] == 'Err' or procexpr['name'] == 'OK':
            cargs = []
            for arg in procexpr['args']:
                state, carg = self.proc(arg, state)
                cargs.append(carg)

            # can't just use 1st carg type here because could be err...
            arg0 = {'what': 'type:glob', 'mod': procexpr['mod'], 'name': str(cargs[0].sort())}
            if procexpr['name'] == 'OK':
                self.res_type = str(cargs[1].sort())
            arg1 = {'what': 'type:glob', 'mod': procexpr['mod'], 'name': self.res_type}
            t = {'what': 'type:glob', 'mod': procexpr['mod'], 'name': 'res', 'args' : [arg0, arg1]}

            sort = self.z3_sort(t)
            print "result! ", sort, cargs[0].sort(), cargs[1].sort()
            cid = constructor_idx_by_name(sort, procexpr['name'])
            return state, sort.constructor(cid)(*cargs)

        elif procexpr['name'] == 'None' or procexpr['name'] == 'Some':
            # pass in argument for type 'A' in res XXX hacky?
            if self.opt_type == 'wcc_data':
                self.opt_type = 'wcc_attr'
            t = {'what': 'type:glob', 'mod': procexpr['mod'], 'name': 'option', 'args': [
                {'what': 'type:glob', 'mod': procexpr['mod'], 'name': self.opt_type}
            ]}

        elif "NF3" in procexpr['name']:
            t = {'what': 'type:glob', 'mod': procexpr['mod'], 'name': 'ftype', 'args': []}

        elif "Build" in procexpr['name']:
            self.opt_type = procexpr['name'][6:].lower()
            t = {'what': 'type:glob', 'mod': procexpr['mod'], 'name': self.opt_type, 'args': []}

        elif procexpr['name'] == 'u32':
            return state, z3.BitVecSort(32)

        elif procexpr['name'] == 'u64':
            return state, z3.BitVecSort(64)

        else:
            raise Exception("UNKNOWN CONSTRUCTOR in proc")
            t = {'what': 'type:glob', 'mod': procexpr['mod'], 'name': procexpr['name'], 'args': []}

        sort = self.z3_sort(t)
        cid = constructor_idx_by_name(sort, procexpr['name'])
        cargs = []
        for arg in procexpr['args']:
            state, carg = self.proc(arg, state)
            cargs.append(carg)
            print "CARG", carg.sort()
        print sort.constructor(cid)
        return state, sort.constructor(cid)(*cargs)

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
