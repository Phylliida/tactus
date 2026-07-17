#!/usr/bin/env python3
"""No-search gate (S2c derivation-first claim; see tgt check.sh).

Asserts, over every emitted .lean artifact under the given
target/tactus-lean tree:

  1. no artifact IMPORTS the search module (`TactusSearch`) — the
     mainline-08 prelude split put the dev-only search ladder there
     precisely so artifacts can't silently depend on it;
  2. no search-ladder tactic NAME appears in tactic position — the
     derivation-first closer must emit fully spelled-out tactic text.

Zero allowed residue: any hit fails the gate (exit 1) and prints every
violation with file:line so the offending emission site can be found.

Tactic-position detection is deliberately syntactic and conservative:
a ladder name preceded by start-of-line, `by`, `(`, `|`, `;` or `<;>`
counts. String literals inside `#[verifier::tactus_tactic("…")]` never
reach artifacts, so no allowlist is needed.
"""

import re
import sys
from pathlib import Path

# The dev-only search ladder (TactusSearch.lean). `tactus_auto` is the
# legacy ambient closer; the rest are its rungs. A name here appearing
# in an artifact means the emitter leaked a search dependency.
LADDER = [
    "tactus_auto",
    "tactus_first",
    "tactus_case_split",
    "tactus_usize_bound",
    "tactus_bit_vector",
]

IMPORT_RE = re.compile(r"^\s*import\s+TactusSearch\b")
# tactic position: start of line or after by / ( / | / ; / <;>
TACTIC_RE = re.compile(
    r"(?:^|\bby\b|\(|\||;|<;>)\s*(" + "|".join(LADDER) + r")\b"
)


def main() -> int:
    if len(sys.argv) != 2:
        print(f"usage: {sys.argv[0]} <target/tactus-lean dir>", file=sys.stderr)
        return 2
    root = Path(sys.argv[1])
    if not root.is_dir():
        print(f"[no-search] not a directory: {root}", file=sys.stderr)
        return 2
    violations = []
    # Scope: the PACKAGE layout only — `<crate>/pkg/*.lean` plus the
    # crate-level `TactusDefs_*/TactusStmts_*/TactusLink_*` modules.
    # That is the surface the package gate elaborates from current
    # emission. The target tree also accumulates debris this claim
    # must not read: legacy islands trees (old crate names) and stale
    # per-fn island files that warm-cache runs never rewrite (their
    # cached OLEANS may be reused, but their .lean text predates the
    # derivation-first emitter). For the tree-wide claim, cold-run
    # after `rm -rf target/tactus-lean` — this checker then sees only
    # current emission.
    def in_scope(f: Path) -> bool:
        if f.parent.name == "pkg":
            return True
        return f.name.startswith(
            ("TactusDefs_", "TactusStmts_", "TactusLink_")
        )
    files = sorted(f for f in root.rglob("*.lean") if in_scope(f))
    for f in files:
        if f.name.startswith("TactusSearch"):
            continue  # the ladder module itself
        try:
            text = f.read_text(encoding="utf-8")
        except OSError as e:
            print(f"[no-search] unreadable {f}: {e}", file=sys.stderr)
            return 2
        for ln, line in enumerate(text.splitlines(), 1):
            if IMPORT_RE.search(line):
                violations.append((f, ln, "imports TactusSearch", line))
            else:
                m = TACTIC_RE.search(line)
                if m:
                    violations.append(
                        (f, ln, f"search tactic `{m.group(1)}`", line)
                    )
    if violations:
        for f, ln, what, line in violations:
            print(f"[no-search] {f}:{ln}: {what}: {line.strip()[:120]}",
                  file=sys.stderr)
        print(f"[no-search] {len(violations)} violation(s) in "
              f"{len(files)} artifacts", file=sys.stderr)
        return 1
    print(f"[no-search] clean: {len(files)} artifacts, 0 violations")
    return 0


if __name__ == "__main__":
    sys.exit(main())
