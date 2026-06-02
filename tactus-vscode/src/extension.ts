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

  query(line: number, col: number): Promise<any> {
    return new Promise((resolve) => {
      this.pending.push(resolve);
      try {
        this.proc.stdin.write(`${line} ${col}\n`);
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

  const env: NodeJS.ProcessEnv = { ...process.env };
  const leanProject = cfg.get<string>('leanProject', '').trim();
  if (leanProject) {
    env.TACTUS_LEAN_PROJECT = leanProject;
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

  // Coalescing cursor tracker: single in-flight query, latest position wins.
  let latest: { line: number; col: number } | undefined;
  let inFlight = false;
  const pump = async () => {
    if (inFlight) return;
    inFlight = true;
    while (latest) {
      const pos = latest;
      latest = undefined;
      const res = await server!.query(pos.line, pos.col);
      if (!panel) break;
      setPanel(renderResult(res));
    }
    inFlight = false;
  };
  const onMove = (line: number, col: number) => {
    latest = { line, col };
    void pump();
  };

  selectionSub = vscode.window.onDidChangeTextEditorSelection((e) => {
    if (e.textEditor.document.fileName !== rsFile) return;
    const p = e.selections[0].active;
    onMove(p.line, p.character);
  });

  // Seed with the current cursor.
  const p = editor.selection.active;
  onMove(p.line, p.character);
}

function stop() {
  selectionSub?.dispose();
  selectionSub = undefined;
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
