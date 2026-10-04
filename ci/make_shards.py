#!/usr/bin/env python3
"""Write ci/shards.txt: the certificate modules in N shards of about equal work.

    python3 ci/make_shards.py [N]        (N defaults to 20)

The work of a module is predicted from the time logs/build.log gives it (its checks take a fixed
multiple of that, see TIME_X in ci/shard.py).  The modules go to the shards greedily, the largest
first, each to the shard with the least work so far.
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from shard import ROOT, build_times  # noqa: E402


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 20
    times = build_times()
    mods = sorted(f[:-5] for f in os.listdir(os.path.join(ROOT, 'C4Cert'))
                  if f.endswith('.lean') and f[:-5] != 'Cover')
    assert sorted(times) == mods, (len(times), len(mods))
    shards = [[0.0, []] for _ in range(n)]
    for m in sorted(mods, key=lambda m: (-times[m], m)):
        s = min(shards, key=lambda s: s[0])
        s[0] += times[m]
        s[1].append(m)
    open(os.path.join(ROOT, 'ci', 'shards.txt'), 'w').write(
        ''.join(' '.join(sorted(s[1])) + '\n' for s in shards))
    w = [s[0] for s in shards]
    print(f'{n} shards of {min(len(s[1]) for s in shards)}-{max(len(s[1]) for s in shards)} modules, '
          f'build seconds per shard {min(w):.0f}-{max(w):.0f} (total {sum(w):.0f})')


if __name__ == '__main__':
    main()
