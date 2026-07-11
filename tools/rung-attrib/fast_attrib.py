#!/usr/bin/env python3
"""Brick 1 rung attribution: per-THEOREM minimal-prefix analysis.

For each sampled emitted `.lean` artifact, builds ONE combined file in
which every `_tactus_*` obligation theorem is duplicated once per
tactic variant (suffixed names), so the file's preamble — the dominant
elaboration cost — is paid once instead of once per variant. Runs bare
`lean` (no `lake env` lock overhead) with LEAN_PATH pointing at the
prelude cache, N-way parallel. ~40 min of naive per-variant lake runs
become ~2 min.

Output: a histogram of the MINIMAL prefix chain that closes each
theorem — rfl → +decide → +omega → +tactus_peel∘T1 → full tactus_auto.
Theorems needing the last step are the T2 (`simp_all`/case-split)
share: the squeeze-and-pin workload (DESIGN-transparent-automation §3;
Brick 1 decision table is §6, measured result recorded at the bottom
of that doc).

Usage:
  fast_attrib.py --lib <emitted-lib-dir> [--failing <fn-name-list>]
                 [--sample N] [--jobs N] [--out DIR]

  --lib      directory of emitted per-fn .lean files (module__fn.lean)
  --failing  file of fn names to EXCLUDE (one per line — e.g. the
             distinct failing fns of a full-crate real run); without
             it, every artifact in --lib is eligible
  --sample   stratified sample size over eligible files (default 40)

Caveats:
  * Only theorems named `_tactus_*` AND closed by `tactus_auto` get
    variant copies; preamble helper theorems keep their original
    tactic (they must elaborate for the file to be usable).
  * Theorems whose tactic composes `tactus_auto` with user text
    (`first | tactus_auto | ...`) are skipped — they already carry
    explicit proofs and aren't the default closer's load.
  * Exclusion by fn NAME over-excludes when two modules share a fn
    name — conservative (never samples a failing fn).
  * Error→theorem attribution scans back from the error line to the
    enclosing `theorem` header; `set_option ... in` prefix lines are
    kept glued to their theorem so duplication can't orphan them.
"""
import argparse, concurrent.futures as cf, os, re, subprocess, sys
from collections import Counter

VARIANTS = {
    "v1_rfl":    '(first | rfl | fail "np")',
    "v2_decide": '(first | rfl | decide | fail "np")',
    "v3_omega":  '(first | rfl | decide | omega | fail "np")',
    "v4_peel":   '(first | rfl | decide | omega | '
                 '(tactus_peel <;> (first | rfl | decide | omega)) | fail "np")',
    "v5_auto":   'tactus_auto',
}
THM = re.compile(r"^theorem (_tactus_[A-Za-z0-9_]+)", re.M)
TOPLEVEL = re.compile(
    r"^(theorem|axiom|noncomputable def|@\[|def |class |instance|inductive"
    r"|structure|mutual|open |set_option|import|end )", re.M)


def split_blocks(src: str):
    """Top-level decl blocks, with `set_option ... in` lines glued to
    the following block (they modify the NEXT decl; splitting them off
    orphans the `in`)."""
    starts = [m.start() for m in TOPLEVEL.finditer(src)] + [len(src)]
    raw = [src[starts[i]:starts[i + 1]] for i in range(len(starts) - 1)]
    head = src[:starts[0]] if starts else src
    blocks, carry = [], ""
    for b in raw:
        if re.match(r"^set_option [^\n]* in\s*\n?$", b):
            carry += b
            continue
        blocks.append(carry + b)
        carry = ""
    if carry:
        blocks.append(carry)
    return head, blocks


def build_combined(path: str):
    src = open(path).read()
    head, blocks = split_blocks(src)
    out, mapping = [], {}
    for block in blocks:
        m = THM.search(block)
        # Skip theorems whose tactic COMPOSES tactus_auto with user
        # text (`first | tactus_auto | (site fallback)` — the gt
        # migration idiom): substituting the closer inside a
        # composition changes the composition's semantics (a weak
        # variant makes the user fallback run, and ITS errors escape
        # the `first`). Those sites already carry explicit user proofs
        # — they aren't part of the default closer's load, which is
        # what this histogram measures.
        composed = re.search(r"\|\s*tactus_auto\b", block)
        if m and not composed and re.search(r"\btactus_auto\b", block):
            name = m.group(1)
            for vk, tac in VARIANTS.items():
                nb = block.replace(name, f"{name}_{vk}", 1)
                nb = re.sub(r"\btactus_auto\b", tac, nb)
                out.append(nb)
                mapping[f"{name}_{vk}"] = (name, vk)
        else:
            out.append(block)
    return head + "".join(out), mapping


def run_one(args, path):
    name = os.path.basename(path)[:-5]
    combined, mapping = build_combined(path)
    cf_path = os.path.join(args.out, f"{name}.lean")
    open(cf_path, "w").write(combined)
    env = dict(os.environ,
               LEAN_PATH=os.path.expanduser("~/.cache/tactus/prelude"))
    r = subprocess.run(["lean", cf_path], capture_output=True, text=True,
                       env=env, timeout=600)
    lines = combined.splitlines()
    failed = set()
    for m in re.finditer(rf"{re.escape(cf_path)}:(\d+):", r.stdout + r.stderr):
        ln = int(m.group(1)) - 1
        for j in range(min(ln, len(lines) - 1), -1, -1):
            t = THM.match(lines[j])
            if t:
                failed.add(t.group(1))
                break
    results = {}
    for full, (base, vk) in mapping.items():
        results.setdefault(base, set())
        if full in failed:
            results[base].add(vk)
    return name, results


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--lib", required=True)
    ap.add_argument("--failing")
    ap.add_argument("--sample", type=int, default=40)
    ap.add_argument("--jobs", type=int, default=8)
    ap.add_argument("--out", default="/tmp/rung-attrib-fast")
    ap.add_argument("--csv", help="also write per-theorem results (file,theorem,minimal_rung)")
    args = ap.parse_args()
    os.makedirs(args.out, exist_ok=True)

    failing = set()
    if args.failing:
        failing = set(l.strip() for l in open(args.failing) if l.strip())
    eligible = []
    for f in sorted(os.listdir(args.lib)):
        if not f.endswith(".lean"):
            continue
        fn = f[:-5].rsplit("__", 1)[-1]
        if fn not in failing:
            eligible.append(os.path.join(args.lib, f))
    step = max(1, len(eligible) // args.sample)
    sample = eligible[::step][:args.sample]
    print(f"eligible files: {len(eligible)}, sampled: {len(sample)}")

    def minimal(failedv):
        for vk, label in [("v1_rfl", "rfl"), ("v2_decide", "decide"),
                          ("v3_omega", "omega"), ("v4_peel", "peel∘T1"),
                          ("v5_auto", "T2 (simp_all/case_split)")]:
            if vk not in failedv:
                return label
        return "fails even tactus_auto"

    hist = Counter()
    total = 0
    rows = []
    with cf.ThreadPoolExecutor(max_workers=args.jobs) as ex:
        for name, results in ex.map(lambda p: run_one(args, p), sample):
            for base, failedv in results.items():
                total += 1
                label = minimal(failedv)
                hist[label] += 1
                rows.append((name, base, label))
    if args.csv:
        with open(args.csv, "w") as f:
            f.write("file,theorem,minimal_rung\n")
            for r in sorted(rows):
                f.write(",".join(r) + "\n")
    print(f"\ntheorems analyzed: {total}")
    for k, v in hist.most_common():
        print(f"  {v:4d}  ({100 * v / max(total, 1):5.1f}%)  {k}")


if __name__ == "__main__":
    main()
