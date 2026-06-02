#!/usr/bin/env python3
"""Phase-0 de-risk probe for the Tactus server (see ../SERVER.md).

Answers the critical unknown: does `lean --server` resolve Mathlib for an
*out-of-Lake* `.lean` file with LEAN_PATH set, and return a real goal via
`$/lean/plainGoal`? If yes, the whole server project is green — everything
downstream is plumbing over existing infra.

Method: drive `lean --server` over LSP/stdio against a real Tactus-generated
`.lean`. rootUri is set to the file's OWN directory, which has no lakefile,
so the server cannot discover a Lake project by walking up — it must fall
back to LEAN_PATH from the environment. That is exactly the deployment
scenario the Tactus server would use.

Usage:
    python3 plaingoal_probe.py <file.lean> [line:char ...]

  - <file.lean>: a Tactus-generated .lean (default: the fib_addition sample
    under source/target/tactus-lean/, if present).
  - line:char:  0-indexed LSP positions to query. If omitted, the probe
    auto-targets the last line containing a Mathlib tactic
    (linarith/nlinarith/ring/omega), at the tactic's starting column.

LEAN_PATH resolution: uses $LEAN_PATH if set, else runs
`lake env printenv LEAN_PATH` in the Tactus lake project
($TACTUS_LEAN_PROJECT, or ../lean-project relative to this script).

Result (observed 2026-06-02, Lean 4.25.0): GREEN. fib_addition.lean
(imports Mathlib.Tactic.Linarith; uses linarith + nlinarith) processed in
~16s with 0 error diagnostics; plainGoal at the nlinarith line returned the
full proof state. Cursor at a tactic's start -> goal *before* it; cursor
past the tactic -> "no goals".
"""
import subprocess, json, os, sys, threading, time, queue, re

HERE = os.path.dirname(os.path.abspath(__file__))


def resolve_lean_path():
    env = os.environ.get('LEAN_PATH')
    if env:
        return env
    proj = os.environ.get('TACTUS_LEAN_PROJECT') or os.path.join(HERE, '..', 'lean-project')
    proj = os.path.abspath(proj)
    if not os.path.exists(os.path.join(proj, 'lakefile.lean')):
        sys.exit('No LEAN_PATH set and no lake project at %s' % proj)
    out = subprocess.run(['lake', 'env', 'printenv', 'LEAN_PATH'],
                         cwd=proj, capture_output=True, text=True)
    if out.returncode != 0 or not out.stdout.strip():
        sys.exit('lake env printenv LEAN_PATH failed: %s' % out.stderr)
    return out.stdout.strip()


def auto_positions(text):
    """Find the last Mathlib-tactic line; return [(line0, char0)]."""
    pat = re.compile(r'^(\s*)(nlinarith|linarith|ring|omega|simp_all)\b')
    hits = []
    for i, line in enumerate(text.splitlines()):
        m = pat.match(line)
        if m:
            hits.append((i, len(m.group(1))))
    return hits[-1:] if hits else [(0, 0)]


def main():
    args = sys.argv[1:]
    default_file = os.path.abspath(os.path.join(
        HERE, '..', 'source', 'target', 'tactus-lean',
        'test_ch3_helpers', 'fib_addition.lean'))
    file = args[0] if args and ':' not in args[0] else default_file
    pos_args = [a for a in args if ':' in a]
    if not os.path.exists(file):
        sys.exit('File not found: %s\n(generate it by running the e2e suite, '
                 'or pass a path to any Tactus-generated .lean)' % file)

    text = open(file).read()
    positions = ([tuple(int(x) for x in a.split(':')) for a in pos_args]
                 if pos_args else auto_positions(text))

    lean_path = resolve_lean_path()
    root = os.path.dirname(os.path.abspath(file))
    uri = 'file://' + os.path.abspath(file)
    if os.path.exists(os.path.join(root, 'lakefile.lean')):
        print('WARNING: rootUri dir has a lakefile; not a clean out-of-Lake test.')

    env = dict(os.environ); env['LEAN_PATH'] = lean_path
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
            try:
                inbox.put(json.loads(body.decode('utf-8', 'replace')))
            except Exception as e:
                log('  [parse error]', e)
    threading.Thread(target=reader, daemon=True).start()

    def pump(deadline, want_id=None, on_msg=None):
        while time.time() < deadline:
            try:
                msg = inbox.get(timeout=0.25)
            except queue.Empty:
                continue
            if msg is None:
                log('  [server closed stream]'); return None
            if on_msg:
                on_msg(msg)
            if want_id is not None and msg.get('id') == want_id and ('result' in msg or 'error' in msg):
                return msg
        return None

    send({'jsonrpc': '2.0', 'id': 1, 'method': 'initialize', 'params': {
        'processId': os.getpid(), 'rootUri': 'file://' + root,
        'capabilities': {}, 'initializationOptions': {}}})
    init = pump(time.time() + 30, want_id=1)
    log('=== initialize: %s ===' % ('OK' if init and 'result' in init else 'FAILED'))

    send({'jsonrpc': '2.0', 'method': 'initialized', 'params': {}})
    send({'jsonrpc': '2.0', 'method': 'textDocument/didOpen', 'params': {
        'textDocument': {'uri': uri, 'languageId': 'lean', 'version': 1, 'text': text}}})
    log('=== didOpen %s (%d bytes); waiting for processing (Mathlib load)...' % (file, len(text)))

    state = {'processed': False, 'diags': None, 'saw': False, 'last': 0.0}
    t0 = time.time()

    def watch(msg):
        m = msg.get('method')
        if m == '$/lean/fileProgress':
            p = msg['params'].get('processing', [])
            now = time.time()
            if p:
                state['saw'] = True
                if now - state['last'] > 2.0:
                    log('  [%5.1fs] processing=%d ranges' % (now - t0, len(p)))
                    state['last'] = now
            elif state['saw']:
                state['processed'] = True
                log('  [%5.1fs] DONE (processing empty)' % (now - t0))
        elif m == 'textDocument/publishDiagnostics':
            state['diags'] = msg['params'].get('diagnostics', [])
            log('  [%5.1fs] publishDiagnostics: %d' % (time.time() - t0, len(state['diags'])))
            for d in state['diags'][:10]:
                sev = {1: 'ERROR', 2: 'WARN', 3: 'INFO', 4: 'HINT'}.get(d.get('severity'), '?')
                rng = d.get('range', {}).get('start', {})
                log('      %s @ %s:%s  %s' % (sev, rng.get('line'), rng.get('character'),
                                              d.get('message', '').replace('\n', ' / ')[:200]))

    deadline = time.time() + 180
    while time.time() < deadline and not state['processed']:
        pump(time.time() + 1, want_id=-999, on_msg=watch)
    pump(time.time() + 2, want_id=-999, on_msg=watch)

    errs = [d for d in (state['diags'] or []) if d.get('severity') == 1]
    log('=== Mathlib resolution: %s (%d error diagnostics) ===' % (
        'CLEAN' if not errs else 'ERRORS PRESENT', len(errs)))

    nid = 10
    for (line, ch) in positions:
        nid += 1
        send({'jsonrpc': '2.0', 'id': nid, 'method': '$/lean/plainGoal', 'params': {
            'textDocument': {'uri': uri}, 'position': {'line': line, 'character': ch}}})
        resp = pump(time.time() + 30, want_id=nid)
        log('\n=== plainGoal @ (line=%d,char=%d) ===' % (line, ch))
        if resp is None:
            log('  (no response / timeout)')
        elif 'error' in resp:
            log('  ERROR:', resp['error'])
        else:
            result = resp['result']
            if result is None:
                log('  result: null (no goal at this position)')
            else:
                rendered = result.get('rendered')
                if rendered:
                    log('\n'.join('  ' + l for l in rendered.splitlines()))

    send({'jsonrpc': '2.0', 'id': 999, 'method': 'shutdown', 'params': None})
    pump(time.time() + 5, want_id=999)
    send({'jsonrpc': '2.0', 'method': 'exit', 'params': None})
    time.sleep(0.3)
    proc.terminate()
    log('\n=== probe done ===')


if __name__ == '__main__':
    main()
