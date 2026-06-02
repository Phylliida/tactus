#!/usr/bin/env python3
"""Phase-0 de-risk probe #2 for the Tactus server (see ../SERVER.md).

Tests the "tactic-only splice" fast path — the thing that makes the infoview
feel *live*. SERVER.md's incremental model: when an edit is entirely inside a
tactic block, splice the new text into the `.lean` and `didChange` it to
`lean --server` -> live, Lean-speed, NO rustc.

This probe talks ONLY to `lean --server` (never invokes rustc/Verus). It opens
a real Tactus-generated `.lean` once (paying the cold Mathlib load), then
applies a sequence of in-memory edits to one tactic line and measures, per
edit: the didChange->updated-diagnostics latency, and the error/warning state.
A small latency (<< the cold load) with correct diagnostics proves the
fast-path is real.

Edits applied to the final `nlinarith [...]` line of fib_addition.lean:
  1. break it  -> bare `linarith` (can't prove the nonlinear fib identity) -> ERROR
  2. sorry it  -> `sorry`                                                   -> warning, 0 errors
  3. restore   -> original nlinarith                                        -> clean, 0 errors

Usage: python3 livedit_probe.py   (resolves LEAN_PATH like plaingoal_probe.py)
"""
import subprocess, json, os, sys, threading, time, queue

HERE = os.path.dirname(os.path.abspath(__file__))


def resolve_lean_path():
    env = os.environ.get('LEAN_PATH')
    if env:
        return env
    proj = os.environ.get('TACTUS_LEAN_PROJECT') or os.path.join(HERE, '..', 'lean-project')
    proj = os.path.abspath(proj)
    out = subprocess.run(['lake', 'env', 'printenv', 'LEAN_PATH'],
                         cwd=proj, capture_output=True, text=True)
    if out.returncode != 0 or not out.stdout.strip():
        sys.exit('lake env printenv LEAN_PATH failed: %s' % out.stderr)
    return out.stdout.strip()


FILE = os.path.abspath(os.path.join(
    HERE, '..', 'source', 'target', 'tactus-lean',
    'test_ch3_helpers', 'fib_addition.lean'))
ORIG = open(FILE).read()
LINES = ORIG.splitlines()
# Locate the nlinarith line (the proof's final tactic).
NL = next(i for i, l in enumerate(LINES) if l.strip().startswith('nlinarith'))
INDENT = LINES[NL][:len(LINES[NL]) - len(LINES[NL].lstrip())]


def with_line(new_content):
    ls = list(LINES)
    ls[NL] = INDENT + new_content
    return '\n'.join(ls) + ('\n' if ORIG.endswith('\n') else '')


EDITS = [
    ('break it (-> bare linarith, fails on nonlinear goal)', with_line('linarith')),
    ('sorry it', with_line('sorry')),
    ('restore (-> original nlinarith)', with_line('nlinarith [step_sum, ih1, ih2, step_m, step_m1]')),
]

URI = 'file://' + FILE
ROOT = os.path.dirname(FILE)


def main():
    env = dict(os.environ); env['LEAN_PATH'] = resolve_lean_path()
    proc = subprocess.Popen(['lean', '--server'],
                            stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, env=env)

    def log(*a): print(*a, flush=True)

    def drain_stderr():
        for raw in iter(proc.stderr.readline, b''):
            log('  [server stderr]', raw.decode('utf-8', 'replace').rstrip())
    threading.Thread(target=drain_stderr, daemon=True).start()

    def send(msg):
        body = json.dumps(msg).encode('utf-8')
        proc.stdin.write(b'Content-Length: %d\r\n\r\n' % len(body) + body)
        proc.stdin.flush()

    inbox = queue.Queue()

    def reader():
        buf = proc.stdout
        while True:
            headers = {}
            while True:
                line = buf.readline()
                if not line:
                    inbox.put(None); return
                line = line.decode('utf-8', 'replace').strip()
                if line == '':
                    break
                if ':' in line:
                    k, v = line.split(':', 1); headers[k.strip().lower()] = v.strip()
            n = int(headers.get('content-length', 0))
            body = b''
            while len(body) < n:
                chunk = buf.read(n - len(body))
                if not chunk:
                    inbox.put(None); return
                body += chunk
            inbox.put(json.loads(body.decode('utf-8', 'replace')))
    threading.Thread(target=reader, daemon=True).start()

    # Wait for a "settled" state: file processing empty AND a publishDiagnostics
    # received after the most recent change. Returns (latency, diags).
    def wait_settled(t_sent, timeout=60):
        saw_proc = False
        diags = None
        proc_done = False
        deadline = time.time() + timeout
        while time.time() < deadline:
            try:
                msg = inbox.get(timeout=0.25)
            except queue.Empty:
                continue
            if msg is None:
                return (None, None)
            m = msg.get('method')
            if m == '$/lean/fileProgress':
                p = msg['params'].get('processing', [])
                if p:
                    saw_proc = True
                elif saw_proc:
                    proc_done = True
            elif m == 'textDocument/publishDiagnostics':
                diags = msg['params'].get('diagnostics', [])
                # The authoritative diagnostics arrive once processing is done.
                if proc_done or diags:
                    return (time.time() - t_sent, diags)
            # also accept: processing done + an (already-seen) empty diags
            if proc_done and diags is not None:
                return (time.time() - t_sent, diags)
        return (None, diags)

    def summarize(diags):
        errs = [d for d in (diags or []) if d.get('severity') == 1]
        warns = [d for d in (diags or []) if d.get('severity') == 2]
        out = 'errors=%d warns=%d' % (len(errs), len(warns))
        for d in (errs + warns)[:4]:
            sev = {1: 'ERROR', 2: 'WARN'}.get(d.get('severity'), '?')
            rng = d.get('range', {}).get('start', {})
            out += '\n      %s @ %s:%s  %s' % (
                sev, rng.get('line'), rng.get('character'),
                d.get('message', '').replace('\n', ' / ')[:120])
        return out

    # initialize / initialized / didOpen
    send({'jsonrpc': '2.0', 'id': 1, 'method': 'initialize', 'params': {
        'processId': os.getpid(), 'rootUri': 'file://' + ROOT,
        'capabilities': {}, 'initializationOptions': {}}})
    # drain initialize response
    while True:
        m = inbox.get()
        if m and m.get('id') == 1:
            break
    send({'jsonrpc': '2.0', 'method': 'initialized', 'params': {}})

    log('=== cold open (pays the Mathlib load once) ===')
    t0 = time.time()
    send({'jsonrpc': '2.0', 'method': 'textDocument/didOpen', 'params': {
        'textDocument': {'uri': URI, 'languageId': 'lean', 'version': 1, 'text': ORIG}}})
    lat, diags = wait_settled(t0, timeout=180)
    log('  cold processing: %.1fs, %s' % (lat or -1, summarize(diags)))

    # Apply edits via full-document didChange (what a splice produces), measure each.
    ver = 1
    for label, text in EDITS:
        ver += 1
        log('\n=== edit: %s  (didChange -> lean --server, NO rustc) ===' % label)
        t = time.time()
        send({'jsonrpc': '2.0', 'method': 'textDocument/didChange', 'params': {
            'textDocument': {'uri': URI, 'version': ver},
            'contentChanges': [{'text': text}]}})
        lat, diags = wait_settled(t, timeout=60)
        log('  re-elaborated in %.2fs  |  %s' % (lat if lat is not None else -1, summarize(diags)))

    # After the restore, confirm plainGoal still works at the nlinarith line.
    log('\n=== plainGoal after the edit cycle (line=%d) ===' % NL)
    send({'jsonrpc': '2.0', 'id': 50, 'method': '$/lean/plainGoal', 'params': {
        'textDocument': {'uri': URI}, 'position': {'line': NL, 'character': len(INDENT)}}})
    deadline = time.time() + 20
    while time.time() < deadline:
        m = inbox.get(timeout=20)
        if m and m.get('id') == 50:
            r = m.get('result')
            if r and r.get('rendered'):
                log('\n'.join('  ' + x for x in r['rendered'].splitlines()[:6]) + '\n  ...')
            else:
                log('  result:', r)
            break

    send({'jsonrpc': '2.0', 'id': 999, 'method': 'shutdown', 'params': None})
    time.sleep(0.3); send({'jsonrpc': '2.0', 'method': 'exit', 'params': None})
    time.sleep(0.3); proc.terminate()
    log('\n=== probe done (this process never invoked rustc/Verus) ===')


if __name__ == '__main__':
    main()
