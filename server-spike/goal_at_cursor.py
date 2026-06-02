#!/usr/bin/env python3
"""End-to-end Tactus-server bridge: `.rs` cursor → Lean goal (SERVER.md
components 2+3).

This is the piece that turns the `--emit-lean` sidecar into the actual user
capability: point at a position in a Tactus `.rs` proof and get the Lean goal
state there. It ties together everything built so far —

    .rs cursor
      → (sourcemap.json sidecar, from `verus --emit-lean`)
      → find the proof fn whose tactic block contains the cursor
      → map the .rs line to a .lean line (content-anchored: line-for-line
         verbatim copy, so match lean_tactic_start_line's text to the .rs)
      → drive `lean --server` ($/lean/plainGoal) on that fn's .lean
      → the goal.

No rustc at query time (the sidecar + .lean were produced by `--emit-lean`).
Proof fns only for now; exec fns use span_marks (coarser) — a later pass.

Usage:
    python3 goal_at_cursor.py <sourcemap.json> <file.rs> <line> <col>

  line/col are 0-indexed (LSP convention). LEAN_PATH resolves like the other
  probes ($LEAN_PATH, else `lake env printenv` in ../lean-project).
"""
import subprocess, json, os, sys, threading, queue, time

HERE = os.path.dirname(os.path.abspath(__file__))


def resolve_lean_path():
    env = os.environ.get('LEAN_PATH')
    if env:
        return env
    proj = os.environ.get('TACTUS_LEAN_PROJECT') or os.path.join(HERE, '..', 'lean-project')
    out = subprocess.run(['lake', 'env', 'printenv', 'LEAN_PATH'],
                         cwd=os.path.abspath(proj), capture_output=True, text=True)
    if out.returncode != 0 or not out.stdout.strip():
        sys.exit('could not resolve LEAN_PATH (set $LEAN_PATH or build ../lean-project)')
    return out.stdout.strip()


def byte_offset_of(rs_bytes, line, col):
    """0-indexed (line, col) -> byte offset in rs_bytes."""
    off = 0
    for i, ln in enumerate(rs_bytes.split(b'\n')):
        if i == line:
            return off + min(col, len(ln))
        off += len(ln) + 1
    return off


def line_of_byte(rs_bytes, byte):
    return rs_bytes[:byte].count(b'\n')


def map_rs_line_to_lean(rs_text, fn, lean_text):
    """Content-anchored line map for a proof fn entry. Returns the constant
    `delta` such that lean_line = rs_line + delta, or None."""
    lean_lines = lean_text.split('\n')
    start = fn['lean_tactic_start_line']
    if start >= len(lean_lines):
        return None
    anchor_text = lean_lines[start].strip()
    if not anchor_text:
        return None
    # Find the .rs line (within the tactic byte range) whose stripped content
    # matches the .lean anchor line. The body is copied verbatim line-for-line,
    # so this pins the constant offset robustly (indent/leading-blank-agnostic).
    s, e = fn['rs_tactic_byte_range']
    rs_bytes = rs_text.encode('utf-8')
    first_line = line_of_byte(rs_bytes, s)
    last_line = line_of_byte(rs_bytes, max(s, e - 1))
    rs_lines = rs_text.split('\n')
    for rl in range(first_line, min(last_line + 1, len(rs_lines))):
        if rs_lines[rl].strip() == anchor_text:
            return start - rl
    return None


def find_fn_for_cursor(sidecar, rs_path, rs_bytes, cursor_byte):
    """Pick the proof fn whose tactic byte range contains the cursor."""
    for fn in sidecar['fns']:
        if fn['kind'] != 'proof':
            continue
        # match on the .lean_file's source — sidecar is per-crate; we assume one
        # .rs here. (A multi-file crate would also key on the fn's source file.)
        s, e = fn['rs_tactic_byte_range']
        if s <= cursor_byte < e:
            return fn
    return None


def plain_goal(lean_file, lean_path, line, col):
    """didOpen lean_file in `lean --server`, wait for processing, return the
    plainGoal `rendered` text at (line, col)."""
    env = dict(os.environ); env['LEAN_PATH'] = lean_path
    proc = subprocess.Popen(['lean', '--server'], stdin=subprocess.PIPE,
                            stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, env=env)
    uri = 'file://' + os.path.abspath(lean_file)
    text = open(lean_file).read()

    def send(m):
        b = json.dumps(m).encode('utf-8')
        proc.stdin.write(b'Content-Length: %d\r\n\r\n' % len(b) + b); proc.stdin.flush()

    inbox = queue.Queue()

    def reader():
        buf = proc.stdout
        while True:
            h = {}
            while True:
                ln = buf.readline()
                if not ln:
                    inbox.put(None); return
                ln = ln.decode('utf-8', 'replace').strip()
                if ln == '':
                    break
                if ':' in ln:
                    k, v = ln.split(':', 1); h[k.strip().lower()] = v.strip()
            n = int(h.get('content-length', 0)); body = b''
            while len(body) < n:
                c = buf.read(n - len(body))
                if not c:
                    inbox.put(None); return
                body += c
            inbox.put(json.loads(body.decode('utf-8', 'replace')))
    threading.Thread(target=reader, daemon=True).start()

    def pump(deadline, want_id=None, on_msg=None):
        while time.time() < deadline:
            try:
                m = inbox.get(timeout=0.2)
            except queue.Empty:
                continue
            if m is None:
                return None
            if on_msg:
                on_msg(m)
            if want_id is not None and m.get('id') == want_id and ('result' in m or 'error' in m):
                return m
        return None

    send({'jsonrpc': '2.0', 'id': 1, 'method': 'initialize',
          'params': {'processId': os.getpid(), 'rootUri': 'file://' + os.path.dirname(os.path.abspath(lean_file)),
                     'capabilities': {}, 'initializationOptions': {}}})
    pump(time.time() + 30, want_id=1)
    send({'jsonrpc': '2.0', 'method': 'initialized', 'params': {}})
    send({'jsonrpc': '2.0', 'method': 'textDocument/didOpen',
          'params': {'textDocument': {'uri': uri, 'languageId': 'lean', 'version': 1, 'text': text}}})

    state = {'done': False, 'saw': False}

    def watch(m):
        if m.get('method') == '$/lean/fileProgress':
            p = m['params'].get('processing', [])
            if p:
                state['saw'] = True
            elif state['saw']:
                state['done'] = True
    t0 = time.time()
    while time.time() < t0 + 180 and not state['done']:
        pump(time.time() + 1, want_id=-1, on_msg=watch)

    send({'jsonrpc': '2.0', 'id': 2, 'method': '$/lean/plainGoal',
          'params': {'textDocument': {'uri': uri}, 'position': {'line': line, 'character': col}}})
    resp = pump(time.time() + 30, want_id=2)
    send({'jsonrpc': '2.0', 'id': 9, 'method': 'shutdown', 'params': None})
    pump(time.time() + 3, want_id=9)
    send({'jsonrpc': '2.0', 'method': 'exit', 'params': None})
    time.sleep(0.2); proc.terminate()
    if not resp or 'result' not in resp:
        return None
    r = resp['result']
    return r.get('rendered') if r else None


def main():
    if len(sys.argv) != 5:
        sys.exit(__doc__)
    sidecar_path, rs_path, line, col = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
    sidecar = json.load(open(sidecar_path))
    rs_text = open(rs_path).read()
    rs_bytes = rs_text.encode('utf-8')
    cursor_byte = byte_offset_of(rs_bytes, line, col)

    fn = find_fn_for_cursor(sidecar, rs_path, rs_bytes, cursor_byte)
    if not fn:
        sys.exit('cursor (%d:%d, byte %d) is not inside any proof fn tactic block' % (line, col, cursor_byte))
    lean_text = open(fn['lean_file']).read()
    delta = map_rs_line_to_lean(rs_text, fn, lean_text)
    if delta is None:
        sys.exit('could not anchor the .rs↔.lean line map for %s' % fn['name'])
    lean_line = line + delta
    lean_lines = lean_text.split('\n')
    lean_col = len(lean_lines[lean_line]) - len(lean_lines[lean_line].lstrip()) if lean_line < len(lean_lines) else 0

    print('fn          : %s (%s)' % (fn['name'], fn['kind']))
    print('.rs cursor  : %d:%d  (byte %d, inside tactic block %s)' % (line, col, cursor_byte, fn['rs_tactic_byte_range']))
    print('.lean map   : line %d  (delta %+d)  ->  %s:%d:%d' % (lean_line, delta, os.path.basename(fn['lean_file']), lean_line, lean_col))
    print('              .lean text: %r' % (lean_lines[lean_line] if lean_line < len(lean_lines) else ''))
    print('querying lean --server (cold ~16s for Mathlib)...')
    goal = plain_goal(fn['lean_file'], resolve_lean_path(), lean_line, lean_col)
    print('\n=== GOAL at .rs %s:%d:%d ===' % (os.path.basename(rs_path), line, col))
    print(goal if goal else '(no goal / null)')


if __name__ == '__main__':
    main()
