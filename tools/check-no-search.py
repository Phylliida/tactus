#!/usr/bin/env python3
"""check-no-search — the B6 gate assertion (DESIGN-transparent-automation.md §5).

Asserts the no-search claim over a directory of emitted .lean artifacts:

  (a) no file contains `import TactusSearch`
  (b) no file contains a search-ladder tactic name in tactic position
      (`tactus_auto`, `tactus_first`, `tactus_case_split`,
      `tactus_bit_vector`, `tactus_usize_bound`) — comments stripped,
      whole-word matched

Exit 0 with the claim printed; exit 1 listing every offender.

Usage:
  check-no-search.py <artifact-dir> [--allow <file> ...]

  --allow   permit specific files (relative to <artifact-dir>) to carry
            search tactics — the counted-residue mechanism. Each use
            prints a NOTE line so the exception is never silent.
"""

import re, sys
from pathlib import Path

SEARCH_TACTICS = [
    "tactus_auto",
    "tactus_first",
    "tactus_case_split",
    "tactus_bit_vector",
    "tactus_usize_bound",
]
NAME_RE = re.compile(
    r"(?<![A-Za-z0-9_])(" + "|".join(SEARCH_TACTICS) + r")(?![A-Za-z0-9_])")


def strip_comments(text):
    return "\n".join(l.split("--", 1)[0] for l in text.splitlines())


def main():
    args = sys.argv[1:]
    if not args:
        print(__doc__)
        return 2
    root = Path(args[0])
    allow = set()
    if "--allow" in args:
        i = args.index("--allow")
        allow = set(args[i + 1:])
        args = args[:i]
    if not root.is_dir():
        print(f"error: no such directory: {root}", file=sys.stderr)
        return 2

    offenders = []
    probes = ["import TactusSearch"] + SEARCH_TACTICS
    for f in sorted(root.rglob("*.lean")):
        if any(part.startswith("build-") for part in f.parts):
            continue  # transient olean-build workdirs, not artifacts
        rel = str(f.relative_to(root))
        try:
            text = f.read_text(errors="replace")
        except OSError:
            continue  # vanished mid-scan (a build workdir was cleaned)
        # Fast substring pre-filter (artifact files can reach 250MB —
        # only run the precise analysis on files that can possibly hit).
        if not any(p in text for p in probes):
            continue
        hits = []
        if re.search(r"(?m)^import TactusSearch\b", text):
            hits.append("imports TactusSearch")
        # Per-line analysis: whole-file comment-strip + lookbehind regex
        # takes minutes on 250MB artifacts; line scans stay C-speed.
        for ln, line in enumerate(text.splitlines(), 1):
            code = line.split("--", 1)[0]
            m = NAME_RE.search(code)
            if m:
                hits.append(f"search tactic `{m.group(1)}` (line {ln})")
        if hits:
            if rel in allow:
                print(f"NOTE: allowed residue: {rel} ({len(hits)} hit(s))")
            else:
                offenders.append((rel, hits))

    if offenders:
        print("NO-SEARCH CLAIM VIOLATED:", file=sys.stderr)
        for rel, hits in offenders:
            for h in hits:
                print(f"  {rel}: {h}", file=sys.stderr)
        return 1

    n = len(list(root.rglob("*.lean")))
    print(f"no-search claim holds: {n} artifacts, no search module "
          f"imported, no search tactic named"
          + (f" ({len(allow)} allowed residue)" if allow else ""))
    return 0


if __name__ == "__main__":
    sys.exit(main())
