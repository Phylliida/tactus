#!/usr/bin/env python3
"""mainline-05 feasibility gate: does the uniform derived tactic
`simp_all only [CORE] <;> omega` close the FULL Brick-1 pool (all
buckets, all rungs — including lower-rung winners), not just T2?"""
import csv, os, re, subprocess, sys
from collections import defaultdict

LIB = '/tmp/census-emit/lib'
OUT = '/tmp/squeeze-gate'
CORE = "Classical.not_forall, Decidable.not_not, Int.add_emod_left, Int.cast_ofNat_Int, Int.natCast_add, Int.neg_add_emod_self, Int.ofNat_eq_coe, Int.ofNat_zero_le, Int.sub_zero, Int.toNat_natCast_add_one, Int.zero_add, Int.zero_sub, Int.mul_add, Int.add_mul, Int.toNat_zero, Int.toNat_one, Int.add_sub_cancel, Nat.add_le_add_iff_right, Nat.add_left_cancel_iff, Nat.add_zero, Nat.le_add_left, Nat.le_add_right, Nat.le_refl, Nat.not_le, Nat.not_lt, Nat.reduceLeDiff, Nat.sub_le_iff_le_add, Nat.zero_add, Nat.zero_le, Nat.mul_add, Nat.add_mul, Nat.add_sub_cancel, and_imp, and_self, and_true, eq_iff_iff, forall_const, forall_eq, ge_iff_le, gt_iff_lt, iff_true, imp_false, imp_self, implies_true, not_and, not_exists, not_false_eq_true, not_imp, not_or, not_true_eq_false, true_and"
TAC = "first | rfl | decide | (tactus_peel <;> (first | rfl | decide | omega)) | (simp_all only [" + CORE + "] <;> omega)"
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
    buckets = defaultdict(set)
    for line in open(sys.argv[1]):
        if line.startswith('file,'): continue
        f, thm, rung = line.rstrip('\n').split(',', 2)
        buckets[f].add(thm)
    os.makedirs(OUT, exist_ok=True)
    import concurrent.futures as cf
    def run_file(item):
        fname, prefixes = item
        src = open(os.path.join(LIB, fname + '.lean')).read()
        head, blocks = split_blocks(src)
        sub, targeted = {}, 0
        for b in blocks:
            m = THM.search(b)
            if not m or 'tactus_auto' not in b: continue
            if re.search(r"\|\s*tactus_auto\b", b): continue
            full = m.group(1)
            if any(full.startswith(p) for p in prefixes):
                sub[id(b)] = b.replace('tactus_auto', TAC, 1)
                targeted += 1
        if not targeted: return fname, 0, set()
        csrc = head + "".join(sub.get(id(b), b) for b in blocks)
        path = os.path.join(OUT, fname + '.gate.lean')
        open(path, 'w').write(csrc)
        r = subprocess.run(['lean', path], capture_output=True, text=True, env=ENV, timeout=900)
        lines = csrc.splitlines()
        bad = set()
        for m in re.finditer(re.escape(path) + r":(\d+):\d+: error", r.stdout + r.stderr):
            t = scan_back(lines, int(m.group(1)) - 1)
            if t: bad.add(t)
        return fname, targeted, bad
    total, failures = 0, {}
    with cf.ThreadPoolExecutor(max_workers=8) as ex:
        for fname, n, bad in ex.map(run_file, sorted(buckets.items())):
            total += n
            if bad: failures[fname] = sorted(bad)
    n_bad = sum(len(v) for v in failures.values())
    print(f"theorems replaced: {total}; failures: {n_bad}")
    for f, ts in failures.items():
        for t in ts: print(f"  FAIL: {f} :: {t}")

if __name__ == '__main__':
    main()
