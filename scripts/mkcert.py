"""Write the certificate modules `C4Cert/*.lean` from the hints found by `gen`, cut by `cut`.

    lake exe gen dir dir.txt && lake exe gen ch ch.txt
    lake exe cut dir dir.txt dir.cut 4000 && lake exe cut ch ch.txt ch.cut 4000
    python3 scripts/mkcert.py dir.cut ch.cut

`cut` replays each hint and predicts its cost in the kernel, in units of about 0.75 s of Lean's
kernel (`0.169 P + 0.459 C` for `P` jets of `P` and `C` jets of `tr S`).  Its line for a cell is
* `C n cost hint` if the whole cell costs at most the cap (4 units above), or else
* `P n cost path hint` (or `PL`, a single leaf over the cap) for each piece of the cell: the
  top-most boxes of the cell's tree of splits that cost at most the cap, with the path of
  splits that leads to the piece (`s.1` or `s.2` for the first or second half of a split along
  coordinate `s - 1`) and the part of the hint for that piece.

A run of consecutive light cells becomes one `allCells` theorem, of predicted cost at most the
cap; each piece of a heavy cell becomes one theorem about its box, and the pieces are put back
together with `Certified.split`.  The theorems are kept small because each kernel needs memory
in proportion to the work of the theorem it is checking, and con-ron checks 16 at once.  The
runs and cells go into modules of about MODULE units, which lake builds in parallel; each module
chains its parts into a `Cover` of its range of cells, and `C4Cert/Cover.lean` chains the modules
into `dirCover : Cover dirMode dirCellBox 0 7840` and `chCover : Cover chMode chCellBox 0 9216`.
"""
import os
import sys

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'C4Cert')
CAP = float(os.environ.get('CAP', 4.0))           # predicted cost of one theorem, at most
MODULE = float(os.environ.get('MODULE', 120.0))   # predicted cost of one module, about
EMPTY = 0.01        # the cost of a cell whose range of the dependent coordinate is empty
RUN_CELLS = 400     # cells in one `allCells` theorem, at most
GRIDS = {'dir': ('Dir', 'dirCell', 'dirMode', 'dirCellBox', 'Cover.dir', 7840, 'direct'),
         'ch': ('Ch', 'chCell', 'chMode', 'chCellBox', 'Cover.ch', 9216, 'blow-up')}


def load(path, N):
    """cell n -> ('C', cost, hint) or ('P', [(cost, path, hint, over)])"""
    cells = {}
    for line in open(path):
        f = line.split()
        n = int(f[1])
        if f[0] == 'C':
            cells[n] = ('C', int(f[2]) / 1000, f[3])
        elif f[0] in ('P', 'PL'):
            path_ = [] if f[3] == '-' else [tuple(map(int, p.split('.'))) for p in f[3].split(',')]
            cells.setdefault(n, ('P', []))[1].append((int(f[2]) / 1000, path_, f[4], f[0] == 'PL'))
        else:
            sys.exit(f'{path}: bad line {line!r}')
    assert sorted(cells) == list(range(N)), path
    return cells


def parts(cells, N):
    """('run', a, b, cost) for runs of light cells, ('cell', n, cost) for the heavy ones"""
    out, a, c = [], None, 0.0
    for n in range(N):
        kind = cells[n][0]
        cn = (cells[n][1] or EMPTY) if kind == 'C' else 0.0
        if a is not None and (kind != 'C' or c + cn > CAP or n - a >= RUN_CELLS):
            out.append(('run', a, n, c))
            a, c = None, 0.0
        if kind == 'C':
            if a is None:
                a = n
            c += cn
        else:
            out.append(('cell', n, sum(p[0] for p in cells[n][1])))
    if a is not None:
        out.append(('run', a, N, c))
    return out


def modules(ps):
    out, cur, c = [], [], 0.0
    for p in ps:
        if cur and c + p[-1] > MODULE:
            out.append(cur)
            cur, c = [], 0.0
        cur.append(p)
        c += p[-1]
    out.append(cur)
    return out


def box_expr(cellbox, n, path_):
    e = f'({cellbox} {n})'
    for s, side in path_:
        e = f'(splitBox {e} {s}).{side}'
    return e


def tree(pieces, names, prefix):
    """the `Certified` term for the box at `prefix`, from its pieces"""
    here = [k for k, p in enumerate(pieces) if p[1] == prefix]
    if here:
        return f'.leaf _ {names[here[0]]}'
    below = [p[1][len(prefix)] for p in pieces if p[1][:len(prefix)] == prefix]
    s = below[0][0]
    assert all(b[0] == s for b in below)
    return (f'.split {s} ({tree(pieces, names, prefix + [(s, 1)])}) '
            f'({tree(pieces, names, prefix + [(s, 2)])})')


def hint_lines(hs, indent='    '):
    lines, cur = [], indent
    for i, h in enumerate(hs):
        item = h + (',' if i + 1 < len(hs) else ']')
        if len(cur) > len(indent) and len(cur) + 1 + len(item) > 100:
            lines.append(cur)
            cur = indent
        cur += (' ' if len(cur) > len(indent) else '') + item
    lines.append(cur)
    return lines


def write_module(name, grid, cells, ps):
    _, cell, mode, cellbox, run_cover, _, chart = GRIDS[grid]
    a0 = ps[0][1]
    b0 = ps[-1][2] if ps[-1][0] == 'run' else ps[-1][1] + 1
    L = ['module', '', 'public import C4Check', '', 'public section', '',
         f'/-! Cells `{a0} ≤ n < {b0}` of the {chart} grid: `decide +kernel` checks that '
         '`checkBoxH` succeeds\non each light cell, and on each piece of a heavy one, with its '
         'hint. -/', '',
         'set_option Elab.async false', '',
         f'namespace C4.Cert.{name}', '']
    chain = []
    for k, p in enumerate(ps):
        if p[0] == 'run':
            _, a, b, _ = p
            L.append(f'theorem c{k} : allCells {cell} {a} {b} [')
            L.extend(hint_lines([cells[n][2] for n in range(a, b)]))
            L[-1] += ' = true := by'
            L += ['  decide +kernel', '']
            chain.append(f'({run_cover} c{k})')
        else:
            n = p[1]
            pieces = cells[n][1]
            names = [f'k{n}_{i}' for i in range(len(pieces))]
            for nm, (_, path_, h, _) in zip(names, pieces):
                L.append(f'theorem {nm} : (checkBoxH {mode} depth '
                         f'{box_expr(cellbox, n, path_)}')
                L.extend(hint_lines([h], '      '))
                L[-1] = L[-1][:-1] + ').isSome = true := by'
                L += ['  decide +kernel', '']
            chain.append(f'(Cover.one (box := {cellbox}) (n := {n})\n      '
                         f'({tree(pieces, names, [])}))')
    L.append(f'theorem cover : Cover {mode} {cellbox} {a0} {b0} :=')
    L.append('  ' + ''.join(c + '.trans <|\n  ' for c in chain[:-1]) + chain[-1])
    L += ['', f'end C4.Cert.{name}', '']
    assert len(L) <= 10000, (name, len(L))
    open(os.path.join(ROOT, name + '.lean'), 'w').write('\n'.join(L))
    return a0, b0


def main():
    os.makedirs(ROOT, exist_ok=True)
    for f in os.listdir(ROOT):
        if f.endswith('.lean'):
            os.remove(os.path.join(ROOT, f))
    cover = ['module', '']
    names = {}
    stats = []
    for grid, path in (('dir', sys.argv[1]), ('ch', sys.argv[2])):
        prefix, _, mode, cellbox, _, N, _ = GRIDS[grid]
        cells = load(path, N)
        ms = modules(parts(cells, N))
        names[grid] = []
        for i, m in enumerate(ms):
            name = f'{prefix}{i:03d}'
            write_module(name, grid, cells, m)
            names[grid].append(name)
            big = max(p[-1] if p[0] == 'run' else max(q[0] for q in cells[p[1]][1]) for p in m)
            stats.append((name, sum(p[-1] for p in m), big, len(m)))
        cover += [f'public import C4Cert.{nm}' for nm in names[grid]]
    cover += ['', 'public section', '',
              '/-! The certificates chained into covers of the two grids. -/', '',
              'namespace C4', '']
    for grid in ('dir', 'ch'):
        _, _, mode, cellbox, _, N, _ = GRIDS[grid]
        cover.append(f'theorem {grid}Cover : Cover {mode} {cellbox} 0 {N} :=')
        cover += [f'  Cert.{nm}.cover.trans <|' for nm in names[grid][:-1]]
        cover.append(f'  Cert.{names[grid][-1]}.cover')
        cover.append('')
    cover += ['end C4', '']
    open(os.path.join(ROOT, 'Cover.lean'), 'w').write('\n'.join(cover))
    tot = sum(s[1] for s in stats)
    print(f'{len(stats)} modules, predicted {tot:.0f} units; largest module '
          f'{max(s[1] for s in stats):.1f}, largest theorem {max(s[2] for s in stats):.2f}')


if __name__ == '__main__':
    main()
