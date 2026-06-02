//! Sidecar source map for the Tactus server (see `tactus/SERVER.md`).
//!
//! Under `--emit-lean`, Tactus writes one `sourcemap.json` per crate next to
//! the generated `.lean` files. It maps each verified fn's `.rs` tactic
//! region to its generated `.lean` so an editor can translate a cursor
//! position into a Lean position (and back) *without* re-running rustc.
//!
//! Most of the data already exists: the [`LeanSourceMap`] that every
//! [`EmitOutput`] carries holds the per-fn `.lean` offsets. The one field
//! that lives outside codegen — the `.rs` `by { }` byte range — is supplied
//! by the verifier loop (it reads `tactic_span` there).

use serde::Serialize;

use crate::generate::EmitOutput;
use crate::sst_to_lean::kind_to_name;
use crate::to_lean_fn::LeanSourceMap;

/// The whole sidecar: the crate name + one entry per emitted fn.
#[derive(Serialize)]
pub struct Sidecar {
    pub crate_name: String,
    pub fns: Vec<SidecarFn>,
}

/// One fn's mapping. Proof fns carry a verbatim tactic-body offset
/// (`.rs` cursor ↔ `.lean` line is a constant add); exec fns carry
/// per-obligation span marks (coarser — obligation granularity).
#[derive(Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum SidecarFn {
    Proof {
        name: String,
        lean_file: String,
        /// `[start, end)` byte range of the `by { … }` block in the `.rs`.
        rs_tactic_byte_range: [usize; 2],
        /// 0-indexed `.lean` line where the verbatim tactic body starts.
        lean_tactic_start_line: usize,
        lean_tactic_line_count: usize,
    },
    Exec {
        name: String,
        lean_file: String,
        span_marks: Vec<SidecarSpanMark>,
    },
}

/// A single exec-fn obligation landmark: its `.lean` line and the `.rs`
/// location + semantic kind it came from.
#[derive(Serialize)]
pub struct SidecarSpanMark {
    pub lean_line: usize,
    pub rs_loc: String,
    pub kind: String,
}

impl SidecarFn {
    /// Build a sidecar entry from an [`EmitOutput`]. `rs_tactic_byte_range`
    /// is the `.rs` `by { }` byte span — used for proof fns; ignored for
    /// exec fns, whose locations live in the span marks.
    pub fn from_emit(out: &EmitOutput, rs_tactic_byte_range: Option<(usize, usize)>) -> SidecarFn {
        let lean_file = out.file_path.to_string_lossy().into_owned();
        match &out.source_map {
            LeanSourceMap::ProofFn { fn_name, tactic_start_line, tactic_line_count } => {
                let (s, e) = rs_tactic_byte_range.unwrap_or((0, 0));
                SidecarFn::Proof {
                    name: fn_name.clone(),
                    lean_file,
                    rs_tactic_byte_range: [s, e],
                    lean_tactic_start_line: *tactic_start_line,
                    lean_tactic_line_count: *tactic_line_count,
                }
            }
            LeanSourceMap::ExecFn { fn_name, span_marks } => SidecarFn::Exec {
                name: fn_name.clone(),
                lean_file,
                span_marks: span_marks
                    .iter()
                    .map(|m| SidecarSpanMark {
                        lean_line: m.line,
                        rs_loc: m.loc.clone(),
                        kind: kind_to_name(m.kind).to_string(),
                    })
                    .collect(),
            },
        }
    }
}

impl Sidecar {
    /// Serialize to pretty JSON and write to `path` (creating parent dirs).
    pub fn write(&self, path: &std::path::Path) -> Result<(), String> {
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent).map_err(|e| {
                format!("failed to create sidecar dir {}: {}", parent.display(), e)
            })?;
        }
        let json = serde_json::to_string_pretty(self)
            .map_err(|e| format!("failed to serialize sidecar: {}", e))?;
        std::fs::write(path, json)
            .map_err(|e| format!("failed to write sidecar {}: {}", path.display(), e))
    }
}
