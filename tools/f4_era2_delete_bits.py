#!/usr/bin/env python3
"""F4 era 2: delete the poison bit slots from the tactus-core vocabulary.
FHyp 4->3 fields; Assert 4->3, Assume 3->2, AssertQueryTactus 4->3,
If 7->6 positional; IfCtor/Loop named poison fields dropped. Balanced-paren
arg surgery, then report remaining textual references for hand-fixing."""
import re, sys

PATH = "tactus-core/lib.rs"
src = open(PATH).read()

def drop_arg(text, head, drop_idx, expected_min=2):
    """Find every `head(` occurrence (not preceded by `fn ` or comment)
    and drop the drop_idx-th top-level argument."""
    out, i, n_changed = [], 0, 0
    while True:
        j = text.find(head + "(", i)
        if j == -1:
            out.append(text[i:])
            break
        # skip definitions (their param lists are typed, not arg lists)
        line_start = text.rfind("\n", 0, j) + 1
        prefix = text[line_start:j]
        stripped = prefix.strip()
        is_def = prefix.endswith("fn ") or stripped.startswith("//")
        if is_def:
            out.append(text[i:j + len(head) + 1])
            i = j + len(head) + 1
            continue
        # parse balanced args
        p = j + len(head)
        assert text[p] == "("
        depth, args, cur, k = 0, [], [], p
        while True:
            ch = text[k]
            if ch == "(":
                depth += 1
                if depth > 1:
                    cur.append(ch)
            elif ch == ")":
                depth -= 1
                if depth == 0:
                    args.append("".join(cur))
                    break
                cur.append(ch)
            elif ch == "," and depth == 1:
                args.append("".join(cur))
                cur = []
            else:
                cur.append(ch)
            k += 1
        if len(args) < expected_min:
            out.append(text[i:j + len(head) + 1])
            i = j + len(head) + 1
            continue
        del args[drop_idx]
        out.append(text[i:j] + head + "(" + ", ".join(a.strip() for a in args) + ")")
        i = k + 1
        n_changed += 1
    return "".join(out), n_changed

total = 0
for head, idx in [
    ("FrameList::FHyp", 2),
    ("StmData::AssertQueryTactus", 3),
    ("StmData::Assert", 3),
    ("StmData::Assume", 2),
]:
    src, n = drop_arg(src, head, idx)
    print(f"{head}: dropped arg {idx} at {n} sites")
    total += n

# If: 7 positional args (c, cn, nc, ncn, cp, thn, els) -> drop index 4 (cp)
src, n = drop_arg(src, "StmData::If", 4)
print(f"StmData::If: dropped arg 4 at {n} sites")
total += n

# IfCtor / Loop: named-field sites — drop the poison field bindings.
for field in ["eq_poison", "neg_poison", "cond_poison"]:
    # named form `field: <expr>,` or bare `field,` (pattern shorthand)
    pat = re.compile(r"\s*" + field + r"(:\s*[^,]+)?,")
    src, n = pat.subn("", src)
    print(f"field {field}: removed {n} bindings")
    total += n

open(PATH, "w").write(src)
print("total edits:", total)
print("NOTE: enum definitions, helper signatures (ctor_pos_frame/loop_*_frame),")
print("u_* lemma param lists, and doc comments are hand-fix sites — grep for")
print("cond_poison|eq_poison|neg_poison|hpz|_hp|FHyp to finish.")
