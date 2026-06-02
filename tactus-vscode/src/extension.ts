// Tactus Infoview — a thin VS Code client over `tactus-lsp` (see ../SERVER.md).
//
// On `Tactus: Show Goal`, it spawns `tactus-lsp serve --json <sidecar> <rs>`
// (the warm goal server), opens an infoview panel beside the editor, and on
// each cursor move sends the 0-indexed `<line> <col>` to the server and renders
// the returned Lean goal. The server keeps `lean --server` hot, so after a
// file's first (cold) query each move resolves in ~milliseconds.
//
// The sidecar + `.lean` come from `verus --emit-lean`; this extension only
// consumes them — no rustc here. Proof fns today (exec fns are a later pass in
// tactus-lsp). If you edit the `.rs` structurally (anything but tactic text),
// re-run `--emit-lean` to refresh the sidecar's byte ranges.

import * as vscode from 'vscode';
import { ChildProcessWithoutNullStreams, spawn } from 'child_process';

let server: TactusServer | undefined;
let panel: vscode.WebviewPanel | undefined;
let selectionSub: vscode.Disposable | undefined;
let documentSub: vscode.Disposable | undefined;

/** Wraps the `tactus-lsp serve --json` child. Queries are answered FIFO (the
 *  server emits exactly one JSON line per query, in order), so a queue of
 *  resolvers matched against incoming lines is sufficient. */
class TactusServer {
  private proc: ChildProcessWithoutNullStreams;
  private buf = '';
  private pending: ((v: any) => void)[] = [];
  public lastError: string | undefined;

  constructor(serverPath: string, args: string[], env: NodeJS.ProcessEnv) {
    this.proc = spawn(serverPath, args, { env });
    this.proc.stdout.on('data', (d) => this.onData(d.toString()));
    this.proc.stderr.on('data', (d) => console.log('[tactus-lsp]', d.toString().trimEnd()));
    this.proc.on('error', (e) => {
      this.lastError = `failed to spawn ${serverPath}: ${e.message}`;
      const r = this.pending.shift();
      if (r) r({ error: this.lastError });
    });
    this.proc.on('exit', (code) => {
      console.log('[tactus-lsp] exited', code);
      // Unblock any waiters so the panel doesn't hang.
      while (this.pending.length) this.pending.shift()!({ error: `tactus-lsp exited (${code})` });
    });
  }

  private onData(s: string) {
    this.buf += s;
    let nl: number;
    while ((nl = this.buf.indexOf('\n')) >= 0) {
      const line = this.buf.slice(0, nl).trim();
      this.buf = this.buf.slice(nl + 1);
      if (!line) continue;
      let obj: any;
      try {
        obj = JSON.parse(line);
      } catch {
        continue;
      }
      const resolve = this.pending.shift();
      if (resolve) resolve(obj);
    }
  }

  /** Send one command (a JSON object — a splice `{fn, body, cursor}` or a plain
   *  `{line, col}`) and resolve with the server's JSON reply (FIFO). */
  send(cmd: object): Promise<any> {
    return new Promise((resolve) => {
      this.pending.push(resolve);
      try {
        this.proc.stdin.write(JSON.stringify(cmd) + '\n');
      } catch (e: any) {
        this.pending.pop();
        resolve({ error: `write failed: ${e.message}` });
      }
    });
  }

  dispose() {
    try {
      this.proc.stdin.end();
      this.proc.kill();
    } catch {
      /* ignore */
    }
  }
}

export function activate(context: vscode.ExtensionContext) {
  context.subscriptions.push(
    vscode.commands.registerCommand('tactus.showGoal', () => showGoal(context)),
    vscode.commands.registerCommand('tactus.stop', () => stop()),
  );
}

export function deactivate() {
  stop();
}

async function showGoal(_context: vscode.ExtensionContext) {
  const editor = vscode.window.activeTextEditor;
  if (!editor) {
    vscode.window.showErrorMessage('Tactus: open a Tactus .rs file first.');
    return;
  }
  const rsFile = editor.document.fileName;

  const cfg = vscode.workspace.getConfiguration('tactus');
  const serverPath = cfg.get<string>('serverPath', 'tactus-lsp');

  let sidecar = cfg.get<string>('sidecarPath', '').trim();
  if (!sidecar) {
    const found = await vscode.workspace.findFiles('**/tactus-lean/*/sourcemap.json', null, 1);
    if (found.length === 0) {
      vscode.window.showErrorMessage(
        'Tactus: no sourcemap.json found. Run `verus --emit-lean` first, or set tactus.sidecarPath.',
      );
      return;
    }
    sidecar = found[0].fsPath;
  }

  // Build the spawned server's environment. GUI-launched VS Code usually does
  // NOT inherit a shell PATH with the Lean toolchain, so tactus-lsp can't find
  // `lake` (to resolve LEAN_PATH) or `lean` (to spawn the worker). Two settings
  // fix that: `leanPath` passes LEAN_PATH directly (skipping `lake`), and
  // `toolchainBin` is prepended to PATH so `lean --server` is spawnable.
  const env: NodeJS.ProcessEnv = { ...process.env };
  const leanProject = cfg.get<string>('leanProject', '').trim();
  if (leanProject) {
    env.TACTUS_LEAN_PROJECT = leanProject;
  }
  const leanPath = cfg.get<string>('leanPath', '').trim();
  if (leanPath) {
    env.LEAN_PATH = leanPath;
  }
  const toolchainBin = cfg.get<string>('toolchainBin', '').trim();
  if (toolchainBin) {
    env.PATH = toolchainBin + (env.PATH ? ':' + env.PATH : '');
  }

  // (Re)start the server for this file.
  stop();
  server = new TactusServer(serverPath, ['serve', '--json', sidecar, rsFile], env);

  panel = vscode.window.createWebviewPanel(
    'tactusInfoview',
    'Tactus Goal',
    { viewColumn: vscode.ViewColumn.Beside, preserveFocus: true },
    { enableScripts: false },
  );
  panel.onDidDispose(() => {
    panel = undefined;
    stop();
  });
  setPanel('<i style="color:#888">Move the cursor inside a proof tactic block…</i>');

  // Coalescing tracker: re-query on cursor move OR edit. Single in-flight; the
  // latest document+cursor state wins. Each query is a *splice* — the live
  // tactic body is sent, so editing the proof updates the goal (no rustc).
  let dirty = false;
  let inFlight = false;
  const pump = async () => {
    if (inFlight) return;
    inFlight = true;
    while (dirty) {
      dirty = false;
      const ed = vscode.window.visibleTextEditors.find((e) => e.document.fileName === rsFile);
      if (!ed) break;
      const cmd = spliceCommandAt(ed.document, ed.selection.active);
      if (!cmd) {
        setPanel(
          '<i style="color:var(--vscode-descriptionForeground,#888)">' +
            'Cursor is not inside a proof tactic block.</i>',
        );
        continue;
      }
      const res = await server!.send(cmd);
      if (!panel) break;
      setPanel(renderResult(res));
    }
    inFlight = false;
  };
  const trigger = () => {
    dirty = true;
    void pump();
  };

  selectionSub = vscode.window.onDidChangeTextEditorSelection((e) => {
    if (e.textEditor.document.fileName === rsFile) trigger();
  });
  documentSub = vscode.workspace.onDidChangeTextDocument((e) => {
    if (e.document.fileName === rsFile) trigger();
  });

  trigger(); // seed with the current cursor
}

/** A proof fn's `by { … }` tactic block in the live buffer. `open`/`close` are
 *  the byte offsets of the matching braces. */
interface TacticBlock {
  name: string;
  open: number;
  close: number;
}

/** Find every `proof fn NAME … by { … }` block in `text` by regex + brace
 *  matching. Robust to the body growing/shrinking; ignores strings/comments
 *  (rare to contain unbalanced braces in a tactic block). */
function findTacticBlocks(text: string): TacticBlock[] {
  const blocks: TacticBlock[] = [];
  const fnRe = /\bproof\s+fn\s+([A-Za-z_][A-Za-z0-9_]*)/g;
  let m: RegExpExecArray | null;
  while ((m = fnRe.exec(text)) !== null) {
    const byRe = /\bby\s*\{/g;
    byRe.lastIndex = m.index;
    const bm = byRe.exec(text);
    if (!bm) continue;
    const open = text.indexOf('{', bm.index);
    if (open < 0) continue;
    let depth = 0;
    let close = -1;
    for (let i = open; i < text.length; i++) {
      const c = text[i];
      if (c === '{') depth++;
      else if (c === '}') {
        depth--;
        if (depth === 0) {
          close = i;
          break;
        }
      }
    }
    if (close < 0) continue;
    blocks.push({ name: m[1], open, close });
    fnRe.lastIndex = close;
  }
  return blocks;
}

/** Build the splice command for the cursor, or `undefined` if it's not inside a
 *  proof tactic block. Sends the live body + the cursor's line text (tactus-lsp
 *  splices the body and content-anchors the query to that line). */
function spliceCommandAt(
  document: vscode.TextDocument,
  position: vscode.Position,
): object | undefined {
  const text = document.getText();
  const offset = document.offsetAt(position);
  const block = findTacticBlocks(text).find((b) => offset > b.open && offset < b.close);
  if (!block) return undefined;
  return {
    fn: block.name,
    body: text.slice(block.open + 1, block.close),
    cursor: document.lineAt(position.line).text,
  };
}

function stop() {
  selectionSub?.dispose();
  selectionSub = undefined;
  documentSub?.dispose();
  documentSub = undefined;
  server?.dispose();
  server = undefined;
}

function setPanel(bodyHtml: string) {
  if (!panel) return;
  panel.webview.html =
    `<!DOCTYPE html><html><head><meta charset="utf-8"></head>` +
    `<body style="font-family: var(--vscode-editor-font-family, monospace); ` +
    `font-size: var(--vscode-editor-font-size, 13px); white-space: pre-wrap; ` +
    `padding: 8px;">${bodyHtml}</body></html>`;
}

function renderResult(res: any): string {
  if (!res) return esc('(no response)');
  if (res.error) {
    return `<span style="color: var(--vscode-descriptionForeground, #888)">${esc(res.error)}</span>`;
  }
  const goalRaw: string | null = res.goal ?? null;
  const goal = goalRaw
    ? goalRaw.replace(/^```lean\r?\n?/, '').replace(/\r?\n?```$/, '')
    : '(no goals)';
  const tag = res.warm ? 'warm' : 'cold-open';
  const header =
    `<div style="color: var(--vscode-descriptionForeground, #888); margin-bottom: 6px;">` +
    `${esc(res.fn ?? '')} &nbsp;·&nbsp; ${tag} ${res.ms ?? '?'} ms</div>`;
  return header + esc(goal);
}

function esc(s: string): string {
  return s
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;');
}
