#!/usr/bin/env python3
"""One shard of the continuous-integration check: build some of the certificate modules and check
each of them with three kernels.

    python3 ci/shard.py N OUTDIR

N picks a line of ci/shards.txt and OUTDIR is where the results go.  For each module X on the line
this
  builds C4Cert.X (lake checks every theorem with Lean's kernel as it builds);
  exports the closure of C4.Cert.X.cover with leanexport, as scripts/nanoda_check.sh does for its
    part B, to OUTDIR/B/X.json;
  checks that export with
    Lean's kernel   leanchecker --silent --from-export             (log OUTDIR/B/X.lean.log)
    nanoda          nanoda_bin, configured by export_tools.py      (log OUTDIR/B/X.log)
    con-ron         con-ron --jobs=1                               (log OUTDIR/B/X.con-ron.log)
  which all come with the Lean toolchain, the way `lake comparator` runs them;
  copies the build outputs of C4Cert.X to OUTDIR/build for the final job.
The time and peak memory of every step go to OUTDIR/steps-N.tsv.  Exits 1 if any step fails.

The steps of different modules run in parallel, SHARD_JOBS at a time (default: one per processor),
as long as the peak memory predicted for them (MEM_GB below) fits in SHARD_MEM_GB (default 13 GB;
a runner has 16).
"""
import json
import os
import shutil
import subprocess
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
KERNELS = ('lean', 'nanoda', 'con-ron')
# predicted peak memory of a step in GB; measured on the module with the most predicted work,
# C4Cert.Dir056: 0.8 GB in the export and in nanoda
MEM_GB = {'export': 1.5, 'lean': 2.0, 'nanoda': 2.0, 'con-ron': 3.5}
# predicted time of a step, as a multiple of the time logs/build.log gives the module, to start
# the longest steps first
TIME_X = {'export': 0.1, 'lean': 1.0, 'nanoda': 1.3, 'con-ron': 3.5}


def build_times():
    out = {}
    for line in open(os.path.join(ROOT, 'logs', 'build.log')):
        if 'Built C4Cert.' in line:
            name = line.split('Built C4Cert.')[1].split()[0]
            t = line.rsplit('(', 1)[1].rstrip(')\n')
            out[name] = float(t[:-2]) / 1000 if t.endswith('ms') else float(t[:-1])
    out.pop('Cover')
    return out


class Step:
    def __init__(self, module, kind, cmd, stdout, est):
        self.module, self.kind, self.cmd, self.stdout = module, kind, cmd, stdout
        self.mem = MEM_GB[kind]
        self.est = est * TIME_X[kind]


def main():
    n, out = int(sys.argv[1]), os.path.abspath(sys.argv[2])
    modules = open(os.path.join(ROOT, 'ci', 'shards.txt')).read().split('\n')[n].split()
    times = build_times()
    budget = float(os.environ.get('SHARD_MEM_GB', 13))
    jobs = int(os.environ.get('SHARD_JOBS', len(os.sched_getaffinity(0))))
    os.makedirs(os.path.join(out, 'B'), exist_ok=True)
    tsv = open(os.path.join(out, f'steps-{n}.tsv'), 'w')
    tsv.write('module\tstep\texit\twall_s\tuser_s\tsys_s\tmaxrss_mb\n')
    t0 = time.time()

    def record(module, kind, status, wall, ru):
        code = os.waitstatus_to_exitcode(status)
        tsv.write(f'{module}\t{kind}\t{code}\t{wall:.1f}\t{ru.ru_utime:.1f}\t{ru.ru_stime:.1f}\t'
                  f'{ru.ru_maxrss // 1024}\n')
        tsv.flush()
        verdict = 'ok' if code == 0 else f'FAILED, exit {code}'
        print(f'[{time.time() - t0:6.0f} s] {module} {kind}: {verdict}, {wall:.0f} s, '
              f'{ru.ru_maxrss / 2**20:.1f} GB', flush=True)
        return code == 0

    def run(module, kind, cmd):
        start = time.time()
        p = subprocess.Popen(cmd, cwd=ROOT)
        _, status, ru = os.wait4(p.pid, 0)
        p.returncode = os.waitstatus_to_exitcode(status)
        return record(module, kind, status, time.time() - start, ru)

    print(f'shard {n}: {len(modules)} modules; {jobs} processors, {budget:g} GB for the checks',
          flush=True)
    # lake builds the modules of the shard together, one per processor
    if not (run('-', 'build C4Check', ['lake', 'build', 'C4Check']) and
            run('all', 'build', ['lake', 'build'] + ['C4Cert.' + m for m in modules])):
        sys.exit(1)

    # the environment `lake env` gives (LEAN_PATH, and PATH with the toolchain's binaries)
    env = json.loads(subprocess.check_output(
        ['lake', 'env', sys.executable, '-c', 'import json, os; print(json.dumps(dict(os.environ)))'],
        cwd=ROOT))
    env['LEAN_ABORT_ON_PANIC'] = '1'
    exe = {k: shutil.which(k, path=env['PATH'])
           for k in ('leanexport', 'leanchecker', 'nanoda_bin', 'con-ron')}
    print('tools:', ', '.join(f'{k} {v}' for k, v in exe.items()), flush=True)
    assert all(exe.values()), exe

    B = os.path.join(out, 'B')
    pending = [Step(m, 'export', [exe['leanexport'], 'C4Cert.' + m, '--', f'C4.Cert.{m}.cover'],
                    os.path.join(B, m) + '.json', times[m]) for m in modules]
    after_export = {}
    for m in modules:
        b = os.path.join(B, m)
        after_export[m] = [
            Step(m, 'lean', [exe['leanchecker'], '--silent', '--from-export', b + '.json'],
                 b + '.lean.log', times[m]),
            Step(m, 'nanoda', [exe['nanoda_bin'], b + '.cfg.json'], b + '.log', times[m]),
            Step(m, 'con-ron', [exe['con-ron'], '--jobs=1', b + '.json'], b + '.con-ron.log',
                 times[m])]

    running, failed, used = {}, [], 0.0
    while pending or running:
        pending.sort(key=lambda s: -s.est)
        for s in list(pending):
            if len(running) >= jobs:
                break
            if running and used + s.mem > budget:
                continue
            f = open(s.stdout, 'w')
            err = open(s.stdout[:-5] + '.export.err', 'w') if s.kind == 'export' else subprocess.STDOUT
            p = subprocess.Popen(s.cmd, cwd=ROOT, env=env, stdout=f, stderr=err)
            f.close()
            if s.kind == 'export':
                err.close()
            # keep p: a Popen object dropped while its process runs gets reaped by subprocess itself
            running[p.pid] = (s, time.time(), p)
            used += s.mem
            pending.remove(s)
        pid, status, ru = os.wait4(-1, 0)
        s, start, p = running.pop(pid)
        p.returncode = os.waitstatus_to_exitcode(status)
        used -= s.mem
        good = record(s.module, s.kind, status, time.time() - start, ru)
        if s.kind == 'export':
            b = os.path.join(B, s.module)
            # leanexport reports a missing name with a PANIC and still exits with 0
            good = good and 'PANIC' not in open(b + '.export.err').read()
            good = good and subprocess.run(
                [sys.executable, '-B', os.path.join(ROOT, 'scripts', 'export_tools.py'), 'config',
                 b + '.json', b + '.cfg.json'], cwd=ROOT).returncode == 0
            if good:
                pending += after_export[s.module]
        if not good:
            failed.append(f'{s.module} {s.kind}')

    for m in modules:
        for sub in ('lib/lean/C4Cert', 'ir/C4Cert'):
            src, dst = os.path.join(ROOT, '.lake/build', sub), os.path.join(out, 'build', sub)
            os.makedirs(dst, exist_ok=True)
            for f in os.listdir(src):
                if f.split('.')[0] == m:
                    shutil.copy2(os.path.join(src, f), dst)
    print(f'shard {n}: {len(modules)} modules, {len(failed)} failed steps {failed}; '
          f'{time.time() - t0:.0f} s', flush=True)
    sys.exit(1 if failed else 0)


if __name__ == '__main__':
    main()
