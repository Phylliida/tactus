#!/usr/bin/env python3
"""S2a derivability census: squeeze every T2 theorem of the Brick-1 pool
and classify the minimized lemma lists on two axes
(DESIGN-transparent-automation.md §3; board mainline-03).

Input pool: the rung-attribution CSV (results-*.csv). Rows labeled
"T2 (simp_all/case_split)" are (file, truncated-prefix) buckets — the
attribution harness's THM regex truncates dotted theorem names at the
first `.`, so each bucket covers 1..N real location-suffixed theorems.
This census enumerates the REAL theorems under each T2 bucket and
squeezes each one individually.

Method per artifact file (the fast_attrib combined-file trick, twice):
  1. QUERY: one combined file, every `_tactus_*` theorem under a T2
     bucket gets its `tactus_auto` closer replaced by `simp_all?` and
     its name suffixed `_sq`. One `lean` run; each theorem's
     "Try this: [apply] simp_all only [...]" info message is attributed
     back to its theorem by line-scan-back.
  2. VERIFY: second combined file with each theorem's closer replaced
     by its own minimized `simp_all only [...]`. One `lean` run; a
     theorem whose error lines appear = minimized form does NOT close.
  3. OMEGA-TAIL RETRY: theorems failing VERIFY get `<;> omega` appended
     (§3.1: "+ omega tail when the winning rung was the composed one" —
     a bare `simp_all only` suggestion is generated against simp_all?'s
     own progress state and need not replay standalone; the omega tail
     closes the arithmetic residue). Only theorems still failing after
     the tail count as MIN-FAILS. The CSV's `verified` column records
     `yes` | `omega-tail` | `NO`.

Classification (per real theorem):
  kind      precondition | postcondition | assert | loop_invariant | other
            (from the truncated prefix)
  axis1     DERIVABLE      — every lemma is (a) core (no `lib.` prefix),
                             (b) a def-unfold (`<mentioned>.eq_def`) of a
                             goal-mentioned symbol, or (c) a named lib
                             axiom/lemma whose subject symbol's basename
                             appears among the goal-mentioned symbol
                             basenames (proxy — see CSV for raw lists).
            GOAL-SPECIFIC  — any lib.* lemma outside that computable set.
            NO-SQUEEZE     — simp_all? produced no suggestion (theorem
                             does not close under simp_all at all, or
                             elaboration error).
  axis2     UNFOLD-THEN-DECIDE — list ⊆ def-unfolds and the minimized
                             form was verified with an explicit
                             `;<;> omega/rfl/decide` tail accepted…
                             (see note below)
            REWRITE-CLOSURE(fixed-core) — list ⊆ the fixed core set
                             observed across the pool (site-INDEPENDENT).
            REWRITE-CLOSURE(goal-specific) — anything else.
            HEURISTIC-NEEDED — NO-SQUEEZE.

NOTE on axis 2: the squeeze suggestions in this pool close the goal
outright (no `;<;> omega` tail was needed in the hand-spike), so
"UNFOLD-THEN-DECIDE" is recorded only when the simp list is purely
definitional unfoldings AND the goal then closes with no rewriting
beyond that — operationally: list ⊆ def-unfolds. The fixed-core set is
the empirical union of core lemmas seen in the spike; the CSV records
the full list so the doc can re-cut.

Usage:
  squeeze_census.py --csv results-2026-07-11-full-pool.csv \
      --lib /tmp/census-emit/lib [--jobs 8] [--out DIR] \
      [--out-csv per-theorem.csv] [--only-file substr]

Environment: needs `lean` on PATH (v4.25.0) and LEAN_PATH covering the
prelude cache + the TactusDefs_lib_exec oleans (post-sync artifacts
import them). Defaults match this workspace when unset.
"""

import argparse, concurrent.futures as cf, os, re, subprocess, sys
from collections import Counter, defaultdict

LEAN_BIN = os.environ.get("TACTUS_LEAN_BIN",
    "/nix/store/4gr3n4nrp0xxgykyyzdxi3xjj2ikn5x1-lean4-4.25.0/bin")
DEFAULT_LEAN_PATH = (
    os.path.expanduser("~/.cache/tactus/prelude")
    + ":/tmp/w4a-b2-ingate4/lib")

# Theorem header: capture the FULL dotted name.
THM = re.compile(r"^theorem (_tactus_[A-Za-z0-9_.]+)", re.M)
TOPLEVEL = re.compile(
    r"^(theorem|axiom|noncomputable def|@\[|def |class |instance|inductive"
    r"|structure|mutual|open |set_option|import|end )", re.M)

# Fixed core simp set: lemmas with no `lib.` prefix are core/Mathlib by
# construction; we still separate the empirically-seen normalizer set
# from "other core" so the doc can see how small the vocabulary really is.
CORE_WHITELIST = {
    "and_imp", "forall_eq", "and_self", "implies_true", "eq_iff_iff",
    "true_and", "and_true", "or_self", "iff_self", "imp_self",
    "forall_const", "exists_const", "not_false_iff", "not_true",
    "not_true_eq_false", "not_false_eq_true",
    "Nat.zero_add", "Nat.add_zero", "Nat.zero_le", "Nat.sub_zero",
    "Nat.cast_add", "Nat.cast_ofNat", "Nat.cast_zero",
    "Int.cast_ofNat_Int", "Int.zero_add", "Int.add_zero", "Int.sub_zero",
    "Int.natCast_add", "Int.ofNat_eq_coe", "Int.cast_add",
    "zero_add", "add_zero", "sub_zero", "cast_ofNat", "iff_true",
}


def split_blocks(src):
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


def kind_of(prefix):
    m = re.match(r"_tactus_(precondition|postcondition|assert"
                 r"|loop_invariant|loop_decreases)", prefix)
    return m.group(1) if m else "other"


def goal_mentioned_names(block):
    """Full dotted lib.* names mentioned in the theorem STATEMENT
    (text before `:= by`)."""
    stmt = block.split(":= by", 1)[0]
    return set(re.findall(r"lib\.[A-Za-z0-9_.]+", stmt))


def parse_lemma_list(sugg):
    inner = sugg[sugg.index("[") + 1:sugg.rindex("]")]
    return [x.strip() for x in inner.split(",") if x.strip()]


def lemma_subject_basename(lem):
    """Heuristic subject of a lib lemma: for axiom_seq_subrange_len the
    subject op is `subrange` (middle components); for foo.eq_def it is
    `foo`. Used ONLY for the axis-1 proxy; the raw list is in the CSV."""
    base = lem.rsplit(".", 1)[-1]
    if base == "eq_def":
        return lem.rsplit(".", 2)[-2]
    toks = base.split("_")
    # axiom_seq_subrange_len / axiom_set_insert_same: drop prefix
    # marker + module-ish first token and trailing facet words.
    toks = [t for t in toks if t not in (
        "axiom", "lemma", "seq", "set", "array", "vec", "spec", "len",
        "index", "same", "different", "equal", "deep", "left", "right",
        "empty", "finite", "insert", "remove", "update", "push", "add",
        "complement", "new", "has", "resolved", "clone", "view",
        "decreases", "matches", "n", "to", "of", "in", "iff", "ext")]
    return "_".join(toks) if toks else base


def classify(lemmas, mentioned, omega_tail=False):
    """(axis1, axis2) for one verified lemma list. `mentioned` = set of
    full dotted lib.* names in the goal statement. A lib.* lemma is
    site-computable iff some dotted prefix of it is goal-mentioned
    (covers def-unfolds, discriminant/accessor lemmas like
    `lib.option.Option.Some_val0`, and constructors of mentioned
    types), or its axiom-subject basename is mentioned (covers
    `axiom_seq_subrange_len` from `Seq.subrange`)."""
    lib_lemmas = [l for l in lemmas if l.startswith("lib.")]
    mentioned_bases = {n.rsplit(".", 1)[-1] for n in mentioned}
    non_core = []
    for l in lib_lemmas:
        parts = l.split(".")
        prefixes = {".".join(parts[:k]) for k in range(2, len(parts))}
        if prefixes & mentioned:
            continue
        if lemma_subject_basename(l) in mentioned_bases:
            continue
        non_core.append(l)
    axis1 = "DERIVABLE" if not non_core else "GOAL-SPECIFIC"
    tail = "+omega" if omega_tail else ""
    if all(l.endswith(".eq_def") for l in lib_lemmas) and lib_lemmas:
        axis2 = "UNFOLD-THEN-DECIDE" + tail
    elif not lib_lemmas and all(l in CORE_WHITELIST for l in lemmas):
        axis2 = "REWRITE-CLOSURE(fixed-core)" + tail
    elif not lib_lemmas:
        axis2 = "REWRITE-CLOSURE(core-extended)" + tail
    else:
        axis2 = "REWRITE-CLOSURE(goal-specific)" + tail
    return axis1, axis2


def run_lean(path, env, timeout=900):
    return subprocess.run([os.path.join(LEAN_BIN, "lean"), path],
                          capture_output=True, text=True, env=env,
                          timeout=timeout)


def scan_back_theorem(lines, ln):
    for j in range(min(ln, len(lines) - 1), -1, -1):
        t = THM.match(lines[j])
        if t:
            return t.group(1)
    return None


def census_file(args, path, prefixes):
    """Squeeze every theorem under `prefixes` in one artifact file."""
    name = os.path.basename(path)[:-5]
    src = open(path).read()
    head, blocks = split_blocks(src)
    targets = []  # (full_name, truncated_prefix, block)
    for block in blocks:
        m = THM.search(block)
        if not m or "tactus_auto" not in block:
            continue
        if re.search(r"\|\s*tactus_auto\b", block):
            continue  # composed with user text — not default-closer load
        full = m.group(1)
        for p in prefixes:
            if full.startswith(p):
                targets.append((full, p, block))
                break
    if not targets:
        return name, []

    env = dict(os.environ)
    env["PATH"] = LEAN_BIN + ":" + env.get("PATH", "")
    env["LEAN_PATH"] = os.environ.get("TACTUS_LEAN_PATH", DEFAULT_LEAN_PATH)

    # QUERY phase: one combined file — every block kept, target theorems
    # get suffixed names + simp_all? closers.
    qmap = {}
    spike_by_block = {}
    for i, (full, p, block) in enumerate(targets):
        qn = f"{full}__sq{i}"
        nb = block.replace(full, qn, 1)
        nb = nb.replace("tactus_auto", "simp_all?", 1)
        spike_by_block[id(block)] = nb
        qmap[qn] = (full, p, block)
    qsrc = head + "".join(spike_by_block.get(id(b), b) for b in blocks)
    qfile = os.path.join(args.out, f"{name}.query.lean")
    open(qfile, "w").write(qsrc)
    qr = run_lean(qfile, env)

    # `lean` in batch mode elaborates commands sequentially and prints
    # `Try this` info messages bare (no file:line prefix), in
    # elaboration order — the i-th suggestion belongs to the i-th
    # spiked theorem in file order (qmap preserves insertion order).
    # Non-target theorems keep their original closers and never emit
    # `Try this` (tactus_auto is not a `?`-tactic). If the counts
    # disagree (a simp_all? that fails emits an error, no suggestion),
    # fall back to per-theorem single-spike runs for the whole file.
    sugg_re = re.compile(r"Try this:\s*\n?\s*\[apply\] (simp_all only \["
                         r"[^\]]*\])", re.S)
    raw_suggestions = [re.sub(r"\s+", " ", m.group(1))
                       for m in sugg_re.finditer(qr.stdout + qr.stderr)]
    qnames = list(qmap.keys())
    suggestions = {}
    if len(raw_suggestions) == len(qnames):
        for qn, sg in zip(qnames, raw_suggestions):
            suggestions[qn] = parse_lemma_list(sg)
    else:
        # FALLBACK: one spike per run, unambiguous attribution.
        for qn, (full, p, block) in qmap.items():
            one = head + "".join(
                (b.replace(full, qn, 1).replace("tactus_auto", "simp_all?", 1)
                 if b is block else b) for b in blocks)
            ofile = os.path.join(args.out, f"{name}.{qn[-40:]}.one.lean")
            open(ofile, "w").write(one)
            orun = run_lean(ofile, env)
            m = sugg_re.search(orun.stdout + orun.stderr)
            if m:
                suggestions[qn] = parse_lemma_list(
                    re.sub(r"\s+", " ", m.group(1)))

    # VERIFY phase: minimized closers where we have suggestions.
    ver_by_block = {}
    vmap = {}
    for qn, (full, p, block) in qmap.items():
        lemmas = suggestions.get(qn)
        if lemmas is None:
            continue
        vn = qn.replace("__sq", "__vf")
        nb = block.replace(full, vn, 1)
        nb = nb.replace("tactus_auto",
                        "simp_all only [" + ", ".join(lemmas) + "]", 1)
        ver_by_block[id(block)] = nb
        vmap[vn] = qn
    verified = set()
    if ver_by_block:
        vfile = os.path.join(args.out, f"{name}.verify.lean")
        vsrc = head + "".join(ver_by_block.get(id(b), b) for b in blocks)
        open(vfile, "w").write(vsrc)
        vr = run_lean(vfile, env)
        vlines = vsrc.splitlines()
        failed = set()
        for m in re.finditer(re.escape(vfile) + r":(\d+):\d+: error",
                             vr.stdout + vr.stderr):
            thm = scan_back_theorem(vlines, int(m.group(1)) - 1)
            if thm:
                failed.add(thm)
        for vn, qn in vmap.items():
            if vn not in failed:
                verified.add(qn)

    # OMEGA-TAIL RETRY: theorems whose minimized list leaves an
    # arithmetic residue (their T2 win came via the composed rung or
    # case-split, not pure simp_all — `simp_all?`'s suggestion is
    # generated against its own progress state and does not replay
    # standalone). Per §3.1 the minimized form is `simp only [...]
    # (+ omega tail when the winning rung was the composed one)`, so
    # retry failures with `<;> omega` before declaring MIN-FAILS.
    omega_tail = set()
    retry = [qn for vn, qn in vmap.items() if qn not in verified]
    if retry:
        oby_block = {}
        omap = {}
        for qn in retry:
            full, p, block = qmap[qn]
            lemmas = suggestions[qn]
            on = qn.replace("__sq", "__om")
            nb = block.replace(full, on, 1)
            nb = nb.replace(
                "tactus_auto",
                "simp_all only [" + ", ".join(lemmas) + "] <;> omega", 1)
            oby_block[id(block)] = nb
            omap[on] = qn
        ofile = os.path.join(args.out, f"{name}.omega.lean")
        osrc = head + "".join(oby_block.get(id(b), b) for b in blocks)
        open(ofile, "w").write(osrc)
        orun = run_lean(ofile, env)
        olines = osrc.splitlines()
        ofailed = set()
        for m in re.finditer(re.escape(ofile) + r":(\d+):\d+: error",
                             orun.stdout + orun.stderr):
            thm = scan_back_theorem(olines, int(m.group(1)) - 1)
            if thm:
                ofailed.add(thm)
        for on, qn in omap.items():
            if on not in ofailed:
                verified.add(qn)
                omega_tail.add(qn)

    rows = []
    for qn, (full, p, block) in qmap.items():
        mentioned = goal_mentioned_names(block)
        lemmas = suggestions.get(qn)
        if lemmas is None:
            rows.append(dict(file=name, theorem=full, kind=kind_of(p),
                             n="", lemmas="", axis1="NO-SQUEEZE",
                             axis2="HEURISTIC-NEEDED", verified=""))
            continue
        if qn in verified:
            axis1, axis2 = classify(lemmas, mentioned,
                                    omega_tail=qn in omega_tail)
            ver = "omega-tail" if qn in omega_tail else "yes"
        else:
            axis1, axis2 = "MIN-FAILS", "MIN-FAILS"
            ver = "NO"
        rows.append(dict(file=name, theorem=full, kind=kind_of(p),
                         n=len(lemmas), lemmas=";".join(lemmas),
                         axis1=axis1, axis2=axis2, verified=ver))
    return name, rows


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--csv", required=True)
    ap.add_argument("--lib", required=True)
    ap.add_argument("--jobs", type=int, default=8)
    ap.add_argument("--out", default="/tmp/squeeze-census")
    ap.add_argument("--out-csv", default=None)
    ap.add_argument("--only-file", default=None)
    args = ap.parse_args()
    os.makedirs(args.out, exist_ok=True)

    buckets = defaultdict(set)  # file -> {truncated prefixes}
    for line in open(args.csv):
        if line.startswith("file,"):
            continue
        f, thm, rung = line.rstrip("\n").split(",", 2)
        if "T2" in rung:
            buckets[f].add(thm)
    print(f"T2 buckets: {sum(len(v) for v in buckets.values())} "
          f"over {len(buckets)} files")

    work = []
    for f, prefixes in sorted(buckets.items()):
        path = os.path.join(args.lib, f + ".lean")
        if args.only_file and args.only_file not in f:
            continue
        if not os.path.exists(path):
            print(f"MISSING ARTIFACT: {path}")
            continue
        work.append((path, prefixes))

    all_rows = []
    with cf.ThreadPoolExecutor(max_workers=args.jobs) as ex:
        futs = [ex.submit(census_file, args, p, ps) for p, ps in work]
        for fut in cf.as_completed(futs):
            name, rows = fut.result()
            all_rows.extend(rows)
            print(f"  {name}: {len(rows)} theorems squeezed")

    all_rows.sort(key=lambda r: (r["file"], r["theorem"]))
    out_csv = args.out_csv or os.path.join(args.out, "census.csv")
    with open(out_csv, "w") as fh:
        fh.write("file,theorem,kind,n_lemmas,axis1,axis2,verified,lemmas\n")
        for r in all_rows:
            fh.write(",".join(str(r[k]) for k in
                     ("file", "theorem", "kind", "n", "axis1", "axis2",
                      "verified")) + "," + r["lemmas"] + "\n")

    print(f"\nreal theorems: {len(all_rows)}")
    for axis in ("axis1", "axis2"):
        print(f"\n{axis}:")
        for k, v in Counter(r[axis] for r in all_rows).most_common():
            print(f"  {v:4d}  ({100*v/max(len(all_rows),1):5.1f}%)  {k}")
    print("\nper-kind x axis1:")
    by_kind = defaultdict(Counter)
    for r in all_rows:
        by_kind[r["kind"]][r["axis1"]] += 1
    for kind in sorted(by_kind):
        tot = sum(by_kind[kind].values())
        print(f"  {kind:15s} n={tot:3d}  " +
              "  ".join(f"{k}={v}" for k, v in by_kind[kind].most_common()))
    print(f"\nCSV: {out_csv}")


if __name__ == "__main__":
    main()
