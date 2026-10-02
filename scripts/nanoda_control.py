"""A control for the check with nanoda (see `nanoda_check.sh`): change one number in the statement
of a certificate in the export of its module so that the statement becomes false, and check that
nanoda rejects the result.

    python3 scripts/nanoda_control.py OUTDIR        (after scripts/nanoda_check.sh OUTDIR)

The certificate is `C4.Cert.Dir000.c15`, the last run of cells of the module `C4Cert.Dir000`, and
the number is the largest natural-number literal of its statement that no other declaration of
the export uses, a packed hint.  A hint is replayed, not trusted, so a changed hint may still
certify its cell (adding 1 may change only the coordinate along which the cell is first split).
So the control adds to the number the smallest `k ≥ 1` for which Lean's kernel proves the changed
statement false (`decide +kernel` in `OUTDIR/control.lean`).  The auxiliary theorem of the
certificate and the proof of `cover` contain the statement too, so they change with it.
"""
import json
import os
import re
import subprocess
import sys

sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from export_tools import Export, SUB_KEYS, config  # noqa: E402

MODULE, CERT = 'Dir000', 'C4.Cert.Dir000.c15'
AUX = '_private.C4Cert.%s.0.%s.' % (MODULE, CERT)   # the auxiliary theorems are private


def own(ex, v):
    """the certificate, its auxiliary theorems and the theorem `cover` of the module"""
    n = ex.name(v['name']) if isinstance(v.get('name'), int) else ''
    return n == CERT or n.startswith(AUX) or n == 'C4.Cert.%s.cover' % MODULE


def roots(o):
    """the expressions in the fields type, value and rhs of a declaration record"""
    if isinstance(o, dict):
        for k, v in o.items():
            if k in ('type', 'value', 'rhs') and isinstance(v, int):
                yield v
            else:
                yield from roots(v)
    elif isinstance(o, list):
        for v in o:
            yield from roots(v)


def closure(ex, start):
    seen, stack = set(), list(start)
    while stack:
        j = stack.pop()
        if j in seen:
            continue
        seen.add(j)
        v = next(v for k, v in ex.exprs[j].items() if k != 'ie')
        if isinstance(v, dict):
            stack.extend(v[k] for k in SUB_KEYS if k in v)
    return seen


def kernel_proves(stmt, path):
    """whether Lean's kernel proves the closed statement `stmt` with `decide +kernel`"""
    with open(path, 'w') as f:
        f.write(f'import C4Check\nopen C4\n\nexample : {stmt} := by\n  decide +kernel\n')
    return subprocess.run(['lake', 'env', 'lean', path], capture_output=True).returncode == 0


def main():
    c4 = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    out = os.path.relpath(os.path.abspath(sys.argv[1]), c4)
    os.chdir(c4)
    src = os.path.join(out, 'B', MODULE + '.json')
    ex = Export(src)
    thm = next(v for k, v in ex.decls if k == 'thm' and ex.name(v['name']) == CERT)
    lits = [j for j in closure(ex, [thm['type']]) if 'natVal' in ex.exprs[j]]
    other = closure(ex, [j for k, v in ex.decls if not own(ex, v) for j in roots(v)])
    cands = sorted((j for j in lits if j not in other), key=lambda j: -int(ex.exprs[j]['natVal']))
    j = cands[0]
    old = ex.exprs[j]['natVal']
    print(f'{src}: the statement of {CERT} has {len(lits)} literals, {len(cands)} of them used by '
          f'no other declaration; the largest has {len(old)} digits, ...{old[-6:]}')
    # the statement in the source, `allCells dirCell n₀ n₁ [hints] = true`
    text = open(os.path.join('C4Cert', MODULE + '.lean')).read()
    stmt = re.search(r'^theorem %s : (.*?) := by$' % CERT.rsplit('.', 1)[1], text, re.M | re.S)
    stmt = ' '.join(stmt.group(1).split())
    assert stmt.endswith(' = true') and len(re.findall(r'\b%s\b' % old, stmt)) == 1
    lean = os.path.join(out, 'control.lean')
    for k in range(1, 65):
        new = str(int(old) + k)
        changed = re.sub(r'\b%s\b' % old, new, stmt)
        if kernel_proves(changed[:-len('true')] + 'false', lean):
            print(f'adding {k}: Lean\'s kernel proves the changed statement false ({lean})')
            break
        value = 'true' if kernel_proves(changed, lean) else 'neither true nor false'
        print(f'adding {k}: Lean\'s kernel proves the changed statement {value}')
    else:
        sys.exit('no k up to 64 makes the statement false')
    dst, cfg = os.path.join(out, 'control.json'), os.path.join(out, 'control.cfg.json')
    with open(src) as f, open(dst, 'w') as g:
        for line in f:
            if line.startswith('{"ie":%d,' % j):
                line = json.dumps({'ie': j, 'natVal': new}, separators=(',', ':')) + '\n'
            g.write(line)
    config(dst, cfg)
    print(f'changed the literal in the export from ...{old[-6:]} to ...{new[-6:]}')
    passed = open(os.path.join(out, 'B', MODULE + '.log')).read().strip().split('\n')[-1]
    print(f'the unchanged export, in part B: {passed}')
    r = subprocess.run(['lake', 'env', 'nanoda_bin', cfg], capture_output=True, text=True)
    # nanoda names its thread with the process id, which changes from run to run
    msg = re.sub(r"thread '(\w+)' \(\d+\) ", r"thread '\1' ", r.stdout + r.stderr)
    print(f'the changed export: nanoda exits with status {r.returncode}')
    print(''.join('  ' + line + '\n' for line in msg.strip().split('\n')), end='')
    print('REJECTED' if r.returncode != 0 else 'ACCEPTED')
    sys.exit(0 if r.returncode != 0 else 1)


if __name__ == '__main__':
    main()
