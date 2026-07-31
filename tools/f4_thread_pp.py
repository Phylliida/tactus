#!/usr/bin/env python3
"""F4 era-1: thread `pp: LeafList` (the derived poison set) through the
tactus-core call graph. Inserts `pp, ` at call sites of the threaded
spec fns, then fixpoints: any fn whose body now mentions `(pp,` but
whose signature lacks `pp: LeafList` gains it as first param, and call
sites of that fn get the same insertion. Idempotent."""
import re, sys

PATH = "tactus-core/lib.rs"
BASE = ["has_poisoned_hyp", "gate_wrap", "close_e", "close_each_e",
        "frame_after", "ret_frame", "wp_stm", "close_sem_e",
        "close_sem_obligs", "exec_safe_f"]

src = open(PATH).read()
lines = src.split("\n")

def is_comment(line):
    return line.lstrip().startswith("//")

def insert_calls(text, name):
    # insert `pp, ` after `NAME(` unless: definition site (`fn NAME(`),
    # already inserted (`NAME(pp,` / `NAME(pp)`), or name is a suffix of
    # a longer identifier (word boundary handles this).
    pat = re.compile(r"(?<!fn )\b" + re.escape(name) + r"\((?!pp\b)")
    return pat.sub(name + "(pp, ", text)

pp_set = list(BASE)

# pass 1: base call-site insertion (skip comment lines)
out = []
for line in lines:
    if is_comment(line):
        out.append(line)
        continue
    for n in pp_set:
        line = insert_calls(line, n)
    out.append(line)
src = "\n".join(out)

# chunk the file into top-level fns for the signature fixpoint
fn_re = re.compile(r"^(?:pub )?(?:open )?(?:spec |proof )?fn (\w+)", re.M)
# note: proof fns are `pub proof fn name(`; spec `pub open spec fn name(`

def chunks(text):
    marks = [(m.start(), m.group(1)) for m in fn_re.finditer(text)]
    marks.append((len(text), None))
    return [(name, text[s:e]) for (s, name), (e, _) in zip(marks, marks[1:])]

changed = True
rounds = 0
while changed and rounds < 20:
    changed = False
    rounds += 1
    cs = chunks(src)
    need_param = set()
    for name, body in cs:
        if name is None:
            continue
        sig_end = body.find("{")
        sig = body[:sig_end]
        if "pp: LeafList" in sig:
            continue
        # does the body call any pp-threaded fn?
        if any(re.search(r"\b" + re.escape(n) + r"\(pp,", body) for n in pp_set):
            need_param.add(name)
    if not need_param:
        break
    # add pp param to those fns' signatures
    for name in need_param:
        # signature: first `fn name(` — insert right after the paren
        pat = re.compile(r"(fn " + re.escape(name) + r")\(")
        new_src, cnt = pat.subn(r"\1(pp: LeafList, ", src, count=1)
        if cnt:
            src = new_src
            changed = True
    # thread call sites of the newly-parametrized fns
    out = []
    for line in src.split("\n"):
        if is_comment(line):
            out.append(line)
            continue
        for n in need_param:
            line = insert_calls(line, n)
        out.append(line)
    src = "\n".join(out)
    pp_set.extend(need_param)

open(PATH, "w").write(src)

# report: fns that mention `(pp,` but still lack the param (pins/probes
# needing a manual explicit value) + the full pp-parametrized set
cs = chunks(src)
manual = []
for name, body in cs:
    if name is None:
        continue
    sig = body[:body.find("{")]
    if "pp: LeafList" not in sig and re.search(r"\(pp,", body):
        manual.append(name)
print("pp-parametrized fns:", len([n for n in pp_set]))
print("NEED MANUAL FIX (calls but no param):")
for n in manual:
    print("  ", n)
