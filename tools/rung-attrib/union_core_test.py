#!/usr/bin/env python3
"""Union-core validation: does ONE fixed core list close every
fixed-core/core-extended theorem of the census? Phase A: bare;
phase B (failures): <;> omega tail.

Usage: union_core_test.py <census.csv>   (see MEASUREMENT-s2a-derivability.md §6)

Reads theorems whose axis2 is REWRITE-CLOSURE(fixed-core|core-extended)
from the squeeze-census CSV, takes the UNION of their lemma lists, and
re-runs every one of them against `simp_all only [UNION]` (phase B adds
`<;> omega` to failures). Hardcoded LEAN_PATH / artifact paths match the
2026-07-16 census environment; adjust LIB/ENV for reruns."""
import csv, os, re, subprocess, sys
from collections import defaultdict

LIB = '/tmp/census-emit/lib'
OUT = '/tmp/squeeze-union'
ENV = dict(os.environ,
    PATH='/nix/store/4gr3n4nrp0xxgykyyzdxi3xjj2ikn5x1-lean4-4.25.0/bin:' + os.environ['PATH'],
    LEAN_PATH=os.path.expanduser('~/.cache/tactus/prelude') + ':/tmp/w4a-b2-ingate4/lib')
THM = re.compile(r"^theorem (_tactus_[A-Za-z0-9_.]+)", re.M)
TOPLEVEL = re.compile(
    r"^(theorem|axiom|noncomputable def|@\[|def |class |instance|inductive"
    r"|structure|mutual|open |set_option|import|end )", re.M)

def split_blocks(src):
    starts = [m.start() for m in TOPLEVEL.finditer(src)] + [len(src)]
    raw = [src[starts[i]:starts[i+1]] for i in range(len(starts)-1)]
    head = src[:starts[0]] if starts else src
    blocks, carry = [], ""
    for b in raw:
        if re.match(r"^set_option [^\n]* in\s*\n?$", b):
            carry += b; continue
        blocks.append(carry + b); carry = ""
    if carry: blocks.append(carry)
    return head, blocks

def scan_back(lines, ln):
    for j in range(min(ln, len(lines)-1), -1, -1):
        t = THM.match(lines[j])
        if t: return t.group(1)

def main():
    census = sys.argv[1]
    rows = [r for r in csv.DictReader(open(census))
            if r['axis2'].startswith('REWRITE-CLOSURE(fixed-core)')
            or r['axis2'].startswith('REWRITE-CLOSURE(core-extended)')]
    union = sorted({l for r in rows for l in r['lemmas'].split(';') if l})
    print(f"theorems: {len(rows)}, union core set: {len(union)} lemmas")
    print("union:", ";".join(union))
    by_file = defaultdict(list)
    for r in rows: by_file[r['file']].append(r['theorem'])
    os.makedirs(OUT, exist_ok=True)
    union_tac = "simp_all only [" + ", ".join(union) + "]"
    failures = {}
    import concurrent.futures as cf
    def run_file(item):
        fname, thms = item
        src = open(os.path.join(LIB, fname + '.lean')).read()
        head, blocks = split_blocks(src)
        targets = {}
        for b in blocks:
            m = THM.search(b)
            if m and m.group(1) in thms and 'tactus_auto' in b:
                nb = b.replace('tactus_auto', union_tac, 1)
                targets[m.group(1)] = nb
        csrc = head + "".join(targets.get((THM.search(b) or [None]).group(1)
                     if THM.search(b) else None, b) for b in blocks)
        # simpler: rebuild by substitution map keyed on block identity
        sub = {}
        for b in blocks:
            m = THM.search(b)
            if m and m.group(1) in targets: sub[id(b)] = targets[m.group(1)]
        csrc = head + "".join(sub.get(id(b), b) for b in blocks)
        path = os.path.join(OUT, fname + '.union.lean')
        open(path, 'w').write(csrc)
        r = subprocess.run(['lean', path], capture_output=True, text=True, env=ENV, timeout=900)
        lines = csrc.splitlines()
        bad = set()
        for m in re.finditer(re.escape(path) + r":(\d+):\d+: error", r.stdout + r.stderr):
            t = scan_back(lines, int(m.group(1)) - 1)
            if t: bad.add(t)
        return fname, bad, len(targets)
    with cf.ThreadPoolExecutor(max_workers=8) as ex:
        for fname, bad, n in ex.map(run_file, sorted(by_file.items())):
            if bad: failures[fname] = sorted(bad)
    n_bad = sum(len(v) for v in failures.values())
    print(f"\nphase A (bare union): {len(rows)-n_bad}/{len(rows)} close")
    # phase B: omega tail on failures
    still = {}
    def run_omega(item):
        fname, thms = item
        src = open(os.path.join(LIB, fname + '.lean')).read()
        head, blocks = split_blocks(src)
        sub = {}
        for b in blocks:
            m = THM.search(b)
            if m and m.group(1) in thms and 'tactus_auto' in b:
                sub[id(b)] = b.replace('tactus_auto', union_tac + ' <;> omega', 1)
        csrc = head + "".join(sub.get(id(b), b) for b in blocks)
        path = os.path.join(OUT, fname + '.unionomega.lean')
        open(path, 'w').write(csrc)
        r = subprocess.run(['lean', path], capture_output=True, text=True, env=ENV, timeout=900)
        lines = csrc.splitlines()
        bad = set()
        for m in re.finditer(re.escape(path) + r":(\d+):\d+: error", r.stdout + r.stderr):
            t = scan_back(lines, int(m.group(1)) - 1)
            if t: bad.add(t)
        return fname, sorted(bad)
    if failures:
        with cf.ThreadPoolExecutor(max_workers=8) as ex:
            for fname, bad in ex.map(run_omega, sorted(failures.items())):
                if bad: still[fname] = bad
    n_still = sum(len(v) for v in still.values())
    print(f"phase B (+omega tail): closes {n_bad - n_still} more; residual failures: {n_still}")
    for f, ts in still.items():
        for t in ts: print(f"  RESIDUAL: {f} :: {t}")

if __name__ == '__main__':
    main()
