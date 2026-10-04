#!/usr/bin/env python3
"""The final job of the continuous-integration check: put the shards' results together, build the
rest and check the parts the shards do not.

    python3 ci/final.py SHARDS OUTDIR

SHARDS holds the results of all the shards, merged (B/, build/ and steps-*.tsv, see ci/shard.py).
In order:
  1. every certificate module was built and its export accepted by all three kernels;
  2. the shards' build outputs belong to these sources: with them in place, `lake build --no-build`
     finds every certificate module up to date (lake compares the trace it recorded for a module, a
     hash of its source, its imports and its options, with the sources);
  3. lake builds the rest (the theorems, with Mathlib from its cache), and `#print axioms` gives
     what logs/axioms.log records: only propext, Classical.choice and Quot.sound;
  4. part A of scripts/nanoda_check.sh: the closure of the main theorems, with the certificates as
     axioms, accepted by Lean's kernel and nanoda (con-ron declines any axiom but the standard
     three, in both its modes, so it checks the certificates in the shards but not part A);
  5. the glue (export_tools.py glue): the certificates part A assumes are, hash for hash, the ones
     the shards' exports prove, and the declarations the two parts share are the same;
  6. the control (scripts/nanoda_control.py): one number changed in the statement of the
     certificate C4.Cert.Dir000.c20, and all three kernels reject the result, Lean's kernel and
     con-ron naming that certificate.
Writes logs to OUTDIR, the time and peak memory of every step to OUTDIR/steps.tsv, and a summary to
OUTDIR/summary.md.  Exits 1 if anything fails.
"""
import glob
import json
import os
import re
import shutil
import subprocess
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
KERNELS = ('lean', 'nanoda', 'con-ron')


def main():
    shards, out = (os.path.abspath(a) for a in sys.argv[1:3])
    os.makedirs(out, exist_ok=True)
    os.chdir(ROOT)
    tsv = open(os.path.join(out, 'steps.tsv'), 'w')
    tsv.write('step\texit\twall_s\tuser_s\tsys_s\tmaxrss_mb\n')
    t0, results = time.time(), []

    def run(name, cmd, log=None, expect=0, env=None, want=None):
        """runs cmd in the project; log: the file for its output (default: this job's output),
        which must contain want if given"""
        print(f'\n== {name} [{time.time() - t0:.0f} s]: {" ".join(cmd)[:300]}', flush=True)
        start = time.time()
        f = open(os.path.join(out, log), 'w') if log else None
        p = subprocess.Popen(cmd, env=env, stdout=f, stderr=subprocess.STDOUT if f else None)
        _, status, ru = os.wait4(p.pid, 0)
        p.returncode = code = os.waitstatus_to_exitcode(status)
        wall = time.time() - start
        if f:
            f.close()
        good = code == expect and (want is None or want in open(os.path.join(out, log)).read())
        tsv.write(f'{name}\t{code}\t{wall:.1f}\t{ru.ru_utime:.1f}\t{ru.ru_stime:.1f}\t'
                  f'{ru.ru_maxrss // 1024}\n')
        tsv.flush()
        print(f'{name}: exit {code}, {"ok" if good else "FAILED"}, {wall:.0f} s, '
              f'{ru.ru_maxrss / 2**20:.1f} GB', flush=True)
        if log:
            tail = open(os.path.join(out, log), errors='replace').read().strip().split('\n')[-3:]
            print(''.join('  | ' + line[:300] + '\n' for line in tail), end='', flush=True)
        results.append((name, good, wall))
        return good

    def finish():
        bad = [n for n, good, _ in results if not good]
        lines = ['| step | result | seconds |', '|---|---|---|']
        lines += [f'| {n} | {"ok" if good else "**FAILED**"} | {w:.0f} |' for n, good, w in results]
        lines += ['', 'ALL CHECKS PASSED' if not bad else 'FAILED: ' + ', '.join(bad)]
        text = '\n'.join(lines) + '\n'
        open(os.path.join(out, 'summary.md'), 'w').write(text)
        if os.environ.get('GITHUB_STEP_SUMMARY'):
            open(os.environ['GITHUB_STEP_SUMMARY'], 'a').write(text)
        print('\n' + text, end='')
        sys.exit(1 if bad else 0)

    # 1. the shards
    mods = sorted(f[:-5] for f in os.listdir('C4Cert') if re.fullmatch(r'(Dir|Ch)\d{3}\.lean', f))
    seen = {}
    for path in sorted(glob.glob(os.path.join(shards, 'steps-*.tsv'))):
        for line in open(path).read().split('\n')[1:]:
            if line:
                m, step, code = line.split('\t')[:3]
                seen.setdefault((m, step), []).append(int(code))
    missing = [f'{m} {s}' for m in mods for s in ('export',) + KERNELS
               if seen.get((m, s)) != [0]]
    print(f'{len(mods)} certificate modules; steps not passed exactly once: {missing[:20]}')
    results.append(('every module exported and accepted by the three kernels', not missing, 0))

    # 2. the build outputs
    shutil.copytree(os.path.join(shards, 'build'), os.path.join(ROOT, '.lake', 'build'),
                    dirs_exist_ok=True)
    if not run('build C4Check', ['lake', 'build', 'C4Check']):
        finish()
    run('certificate modules up to date', ['lake', 'build', '--no-build'] +
        ['C4Cert.' + m for m in mods], log='nobuild.log')

    # 3. the rest of the build, and the axioms
    if not (run('Mathlib from its cache', ['lake', 'exe', 'cache', 'get'], log='cache.log') and
            run('build C4Cert', ['lake', 'build', 'C4Cert'], log='build_cert.log') and
            run('build C4', ['lake', 'build'], log='build.log')):
        finish()
    logs = open(os.path.join(out, 'build_cert.log')).read() + open(os.path.join(out, 'build.log')).read()
    built = re.findall(r'Built (C4Cert\.(?:Dir|Ch)\d{3})\b', logs)
    print('certificate modules lake built again:', built)
    results.append(('no certificate module built again', not built, 0))
    if run('print axioms', ['lake', 'env', 'lean', 'Axioms.lean'], log='axioms.log'):
        same = open(os.path.join(out, 'axioms.log')).read() == open('logs/axioms.log').read()
        print('the axioms are', 'as' if same else 'NOT as', 'logs/axioms.log records')
        results.append(('axioms as logs/axioms.log records', same, 0))

    # 4. part A, with the names scripts/nanoda_check.sh exports
    env = json.loads(subprocess.check_output(
        ['lake', 'env', sys.executable, '-c', 'import json, os; print(json.dumps(dict(os.environ)))']))
    env['LEAN_ABORT_ON_PANIC'] = '1'
    exe = {k: shutil.which(k, path=env['PATH'])
           for k in ('leanexport', 'leanchecker', 'nanoda_bin', 'con-ron')}
    src = open('scripts/nanoda_check.sh').read()
    names = re.search(r'lake env leanexport C4 -- (.*?) > \$OUT/main\.json', src, re.S).group(1)
    names = names.replace('\\\n', ' ').split()
    assert all(re.fullmatch(r'C4\.[\w.]+', n) for n in names), names
    print(f'\npart A: {len(names)} theorems, from {names[0]} to {names[-1]}')
    py, tools = [sys.executable, '-B'], ['scripts/export_tools.py']
    A = lambda f: os.path.join(out, f)  # noqa: E731
    with open(A('main.json'), 'w') as f, open(A('main.err'), 'w') as g:
        start = time.time()
        p = subprocess.run([exe['leanexport'], 'C4', '--'] + names, stdout=f, stderr=g, env=env)
    # leanexport reports a missing name with a PANIC and still exits with 0
    good = p.returncode == 0 and 'PANIC' not in open(A('main.err')).read()
    print(f'export part A: exit {p.returncode}, {"ok" if good else "FAILED"}, '
          f'{time.time() - start:.0f} s, {os.path.getsize(A("main.json")) / 2**20:.0f} MB')
    results.append(('export part A', good, time.time() - start))
    if not (good and
            run('part A: certificates made axioms',
                py + tools + ['partA', A('main.json'), A('mainA.json'), A('certnames.txt')],
                log='partA.log') and
            run('part A: nanoda config',
                py + tools + ['config', A('mainA.json'), A('mainA.cfg.json'), A('certnames.txt')])):
        finish()
    os.remove(A('main.json'))
    run('part A: Lean', [exe['leanchecker'], '--silent', '--from-export', A('mainA.json')],
        log='mainA.lean.log', env=env)
    run('part A: nanoda', [exe['nanoda_bin'], A('mainA.cfg.json')], log='mainA.log', env=env)

    # 5. the glue
    run('glue', py + tools + ['glue', A('mainA.json'), A('certnames.txt')] +
        sorted(glob.glob(os.path.join(shards, 'B', '*[0-9].json'))), log='glue.log')

    # 6. the control: nanoda_control.py writes SHARDS/control.json and exits 0 if nanoda rejects it
    control = os.path.join(shards, 'control.json')
    if run('control: nanoda rejects', py + ['scripts/nanoda_control.py', shards],
           log='control.log'):
        run('control: Lean rejects', [exe['leanchecker'], '--from-export', control],
            log='control.lean.log', expect=1, env=env, want='C4.Cert.Dir000.c20._proof_1')
        run('control: con-ron rejects', [exe['con-ron'], '--jobs=4', control],
            log='control.con-ron.log', expect=1, env=env, want='C4.Cert.Dir000.c20._proof_1')
    finish()


if __name__ == '__main__':
    main()
