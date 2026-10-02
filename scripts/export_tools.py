"""Tools for the independent check of the proofs with nanoda (see `nanoda_check.sh`).

    python3 export_tools.py partA main.json mainA.json certnames.txt
        replace the certificate theorems of the export `main.json` (`C4.Cert.*.cK` for a run of
        cells, `C4.Cert.*.kN_I` for a piece of the cell `N`) by axioms with the same names and
        types, drop the auxiliary theorems `C4.Cert.*.cK._proof_N` that `decide +kernel`
        creates (they carry the computation, and only the certificate uses them; they are
        private to the module, so their names begin with `_private.C4Cert.*.0.`), and list
        the names of the certificates
    python3 export_tools.py config EXPORT.json CFG.json [NAMES]
        write a nanoda configuration that checks EXPORT.json and permits only the three
        standard axioms and the axioms named in the file NAMES
    python3 export_tools.py glue mainA.json certnames.txt B1.json B2.json ...
        check that the module exports B1, B2, ... prove every certificate exactly once, with the
        type it has as an axiom in mainA.json, that their other declarations are those of
        mainA.json with the same names, and that they use only the three standard axioms

Declarations are compared by SHA-256 hashes of a canonical form in which names are spelled out
and subexpressions are replaced by their hashes, so the hashes do not depend on the numbering of
the export file.  Binder names and annotations are left out: the kernel ignores them, and the
exporter shares alpha-equivalent terms, so they depend on what else is exported.
"""
import hashlib
import json
import re
import sys

CERT = re.compile(r'^C4\.Cert\.(Dir|Ch)\d{3}\.(c\d+|k\d+_\d+)$')
AUX = re.compile(r'^_private\.C4Cert\.((Dir|Ch)\d{3})\.0\.C4\.Cert\.\1\.(c\d+|k\d+_\d+)'
                 r'\._proof_\d+$')
STD = ['propext', 'Classical.choice', 'Quot.sound']
# the fields of a declaration record whose integers are names, resp. expressions
NAME_KEYS = {'name', 'induct', 'all', 'ctors', 'ctor', 'levelParams', 'declName', 'typeName'}
EXPR_KEYS = {'type', 'value', 'rhs'}
# the fields of an expression that are subexpressions, and the fields of a binder that the
# kernel ignores
SUB_KEYS = ('fn', 'arg', 'body', 'type', 'value', 'struct', 'expr')
BINDER_META = ('name', 'binderInfo', 'nondep')


class Export:
    def __init__(self, path):
        self.names = {0: None}
        self.levels = {}
        self.exprs = {}
        self.decls = []          # (kind, record)
        with open(path) as f:
            for line in f:
                d = json.loads(line)
                if 'in' in d:
                    self.names[d['in']] = d
                elif 'il' in d:
                    self.levels[d['il']] = d
                elif 'ie' in d:
                    self.exprs[d['ie']] = d
                elif 'meta' not in d:
                    (k, v), = d.items()
                    self.decls.append((k, v))
        self._n, self._l, self._e = {}, {}, {}

    def name(self, i):
        if i not in self._n:
            if i == 0:
                s = ''
            else:
                d = self.names[i]
                k = 'str' if 'str' in d else 'num'
                p = self.name(d[k]['pre'])
                s = (p + '.' if p else '') + str(d[k]['str' if k == 'str' else 'i'])
            self._n[i] = s
        return self._n[i]

    def level(self, i):
        if i not in self._l:
            if i == 0:
                s = '0'
            else:
                d = self.levels[i]
                (k, v), = ((k, v) for k, v in d.items() if k != 'il')
                if k == 'succ':
                    s = 'S(' + self.level(v) + ')'
                elif k in ('max', 'imax'):
                    s = k + '(' + self.level(v[0]) + ',' + self.level(v[1]) + ')'
                elif k == 'param':
                    s = 'P(' + self.name(v) + ')'
                else:
                    raise ValueError(d)
            self._l[i] = s
        return self._l[i]

    def field(self, v, key):
        """canonical form of a field of an expression"""
        if key in ('name', 'declName', 'typeName'):
            return 'N:' + self.name(v)
        if key == 'us':
            return 'U:[' + ','.join(self.level(u) for u in v) + ']'
        if key in SUB_KEYS:
            return 'E:' + self.expr(v)
        return 'V:' + json.dumps(v, sort_keys=True)

    def expr(self, i):
        """hash of an expression (iterative, since the terms can be deep)"""
        stack = [i]
        while stack:
            j = stack[-1]
            if j in self._e:
                stack.pop()
                continue
            (k, v), = ((k, v) for k, v in self.exprs[j].items() if k != 'ie')
            subs = [v[kk] for kk in SUB_KEYS
                    if isinstance(v, dict) and kk in v and v[kk] not in self._e]
            if subs:
                stack.extend(subs)
                continue
            if k == 'sort':
                c = 'sort|' + self.level(v)
            elif isinstance(v, dict):
                skip = BINDER_META if k in ('forallE', 'lam', 'letE') else ()
                c = k + '|' + '|'.join(kk + '=' + self.field(v[kk], kk)
                                       for kk in sorted(v) if kk not in skip)
            else:
                c = k + '|' + json.dumps(v)
            self._e[j] = hashlib.sha256(c.encode()).hexdigest()
            stack.pop()
        return self._e[i]

    def record(self, v, key=None):
        """canonical form of (a field of) a declaration record"""
        if isinstance(v, dict):
            return '{' + ','.join(k + ':' + self.record(v[k], k) for k in sorted(v)) + '}'
        if isinstance(v, list):
            return '[' + ','.join(self.record(x, key) for x in v) + ']'
        if isinstance(v, int) and not isinstance(v, bool):
            if key in NAME_KEYS:
                return 'N:' + self.name(v)
            if key in EXPR_KEYS:
                return 'E:' + self.expr(v)
        return 'V:' + json.dumps(v)


def decl_hashes(ex, only=None):
    """name -> (kind, hash of the whole record); an inductive record defines several names"""
    out = {}
    for k, v in ex.decls:
        if k == 'inductive':
            names = [ex.name(x['name']) for part in ('types', 'ctors', 'recs') for x in v[part]]
        else:
            names = [ex.name(v['name'])]
        if only is not None and not any(n in only for n in names):
            continue
        h = hashlib.sha256((k + ':' + ex.record(v)).encode()).hexdigest()
        for n in names:
            assert n not in out, n
            out[n] = (k, h)
    return out


def part_a(src, dst, names_out):
    ex = Export(src)
    certs, dropped = [], 0
    with open(src) as g, open(dst, 'w') as f:
        for line in g:
            if line.startswith('{"thm"'):
                v = json.loads(line)['thm']
                n = ex.name(v['name'])
                if AUX.match(n):
                    dropped += 1
                    continue
                if CERT.match(n):
                    assert v['levelParams'] == [] and v['all'] == [v['name']]
                    certs.append(n)
                    line = json.dumps({'axiom': {'isUnsafe': False, 'levelParams': [],
                                                 'name': v['name'], 'type': v['type']}},
                                      separators=(',', ':')) + '\n'
            f.write(line)
    open(names_out, 'w').write(''.join(n + '\n' for n in sorted(certs)))
    axioms = [ex.name(v['name']) for k, v in ex.decls if k == 'axiom']
    print(f'{src}: {len(ex.decls)} declarations, axioms {axioms}')
    print(f'{dst}: {len(certs)} certificates made axioms, {dropped} auxiliary theorems dropped')


def config(export, cfg, names=None):
    permitted = STD + (open(names).read().split() if names else [])
    json.dump({'export_file_path': export, 'use_stdin': False,
               'permitted_axioms': permitted, 'unpermitted_axiom_hard_error': True,
               'nat_extension': True, 'string_extension': True,
               'pp_declars': [], 'pp_to_stdout': True, 'print_success_message': True},
              open(cfg, 'w'), indent=1)


def glue(a_path, names_path, b_paths):
    certnames = set(open(names_path).read().split())
    b_decls, b_certs, b_axioms, bad = {}, {}, set(), []
    for p in b_paths:
        ex = Export(p)
        for n, kh in decl_hashes(ex).items():
            if CERT.match(n) or AUX.match(n):
                continue
            if b_decls.setdefault(n, kh) != kh:
                bad.append(('two versions in the module exports', n))
        for k, v in ex.decls:
            n = ex.name(v['name']) if 'name' in v else ''
            if k == 'thm' and CERT.match(n):
                assert v['levelParams'] == []
                b_certs.setdefault(n, []).append(ex.expr(v['type']))
            elif k == 'axiom':
                b_axioms.add(n)
    print(f'{len(b_paths)} module exports: {len(b_certs)} certificates proved, '
          f'{len(b_decls)} other declarations, axioms {sorted(b_axioms)}')
    ex = Export(a_path)
    a_decls = decl_hashes(ex, only=set(b_decls))
    a_axioms = {ex.name(v['name']): ex.expr(v['type']) for k, v in ex.decls if k == 'axiom'}
    a_certs = {n: h for n, h in a_axioms.items() if n not in STD}
    print(f'{a_path}: {len(ex.decls)} declarations, {len(a_certs)} axioms besides '
          f'{sorted(set(a_axioms) & set(STD))}')
    if set(a_certs) != certnames:
        bad.append(('axioms of part A other than the certificates', len(a_certs)))
    if set(b_certs) != certnames:
        bad.append(('certificates proved in the modules', len(b_certs)))
    for n, hs in b_certs.items():
        if len(hs) != 1:
            bad.append(('proved more than once', n))
        elif hs[0] != a_certs.get(n):
            bad.append(('type differs from part A', n))
    for n, kh in b_decls.items():
        if a_decls.get(n) != kh:
            bad.append(('declaration differs from part A', n))
    if not b_axioms <= set(STD):
        bad.append(('nonstandard axioms in the modules', sorted(b_axioms - set(STD))))
    print(f'{len(bad)} problems', bad[:20])
    print('GLUE OK' if not bad else 'GLUE FAILED')
    return not bad


def main():
    cmd, args = sys.argv[1], sys.argv[2:]
    if cmd == 'partA':
        part_a(*args)
    elif cmd == 'config':
        config(*args)
    elif cmd == 'glue':
        sys.exit(0 if glue(args[0], args[1], args[2:]) else 1)
    else:
        raise SystemExit(__doc__)


if __name__ == '__main__':
    main()
