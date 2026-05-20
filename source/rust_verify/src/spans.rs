use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::StableCrateId;
use rustc_span::source_map::SourceMap;
use rustc_span::{BytePos, ExternalSource, FileName, Span, SpanData};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use vir::ast::{SpannedTyped, Typ};
use vir::def::Spanned;

use crate::externs::VerusExterns;

pub(crate) fn to_raw_span(span: Span) -> vir::messages::RawSpan {
    Arc::new(span.data())
}

/// Parse a `"file:line:col"` string into its three components.
/// Splits from the right because file paths may legitimately
/// contain `:` (Windows drive letters, etc.) but `line:col` are
/// always the last two segments. Returns `None` for malformed
/// input (missing colons, non-numeric line/col, empty path).
///
/// Shared by `Reporter::report_as` (which reads `Span::start_loc`
/// to drive `swap_source_for_diagnostics`) and
/// `tactic_body_line_span` (which parses a fn's `start_loc` to
/// derive byte offsets for the per-tactic-line span).
pub(crate) fn parse_file_line_col(s: &str) -> Option<(&str, usize, usize)> {
    let last_colon = s.rfind(':')?;
    let col: usize = s[last_colon + 1..].parse().ok()?;
    let rest = &s[..last_colon];
    let second_colon = rest.rfind(':')?;
    let line: usize = rest[second_colon + 1..].parse().ok()?;
    let path = &rest[..second_colon];
    if path.is_empty() { return None; }
    Some((path, line, col))
}

/// Worker-thread-safe accessor for the `SpanData` stored inside a
/// `vir::messages::RawSpan`. Unlike `from_raw_span`, this does NOT
/// reconstruct the `Span` (which interns via rustc's thread-local
/// state and warns when called off-thread). Pure downcast + field
/// read; safe from any thread.
///
/// Used by `tactic_body_line_span` to read the parent span's
/// `BytePos`/`SyntaxContext` without violating the rustc-thread
/// invariant.
pub(crate) fn raw_span_data(raw_span: &vir::messages::RawSpan) -> Option<SpanData> {
    let x = (&(**raw_span)) as &(dyn std::any::Any + Sync + Send);
    x.downcast_ref::<SpanData>().copied()
}

/// Track files whose `SourceFile.src` has already been swapped to the
/// original (un-sanitized) content for diagnostic rendering.
/// Idempotent — once a file is swapped, subsequent emissions render
/// against the same original content without needing another swap.
static SWAPPED_FILES: std::sync::OnceLock<std::sync::Mutex<std::collections::HashSet<std::path::PathBuf>>> =
    std::sync::OnceLock::new();

/// Recompute `multibyte_chars` for a source string. Each non-ASCII char
/// in valid UTF-8 starts at a byte ≥ 128; its length determines the
/// `MultiByteChar` entry (which records `(pos, byte_length)` for visual
/// column accounting). Matches rustc's logic in
/// `rustc_span::analyze_source_file::analyze_source_file_short` —
/// reproduced here because rustc's helper is `pub(crate)`.
fn compute_multibyte_chars(s: &str) -> Vec<rustc_span::MultiByteChar> {
    use rustc_span::{MultiByteChar, RelativeBytePos};
    let mut out = Vec::new();
    let bytes = s.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        let b = bytes[i];
        let len: u8 = if b < 0x80 {
            1
        } else if b < 0xE0 {
            2
        } else if b < 0xF0 {
            3
        } else {
            4
        };
        if len > 1 {
            out.push(MultiByteChar {
                pos: RelativeBytePos(i as u32),
                bytes: len,
            });
        }
        i += len as usize;
    }
    out
}

/// Swap a `SourceFile`'s in-memory source from the FileLoader-sanitized
/// content (blank spaces inside tactic blocks) to the original content
/// (real tactic text), so rustc's diagnostic renderer shows what the
/// user wrote rather than the blank-space lexer view.
///
/// Idempotent per `file_path` — once a file is swapped, this is a
/// no-op for subsequent calls. Tracks swapped files in
/// [`SWAPPED_FILES`].
///
/// Returns `true` if a swap happened (or had already happened on a
/// prior call). Returns `false` if the file isn't in our cache (e.g.,
/// loaded outside `TactusFileLoader`) or no `SourceFile` matches.
///
/// ## Safety
///
/// This writes through a raw `*mut SourceFile` derived from
/// `Arc::as_ptr`. The write is safe under two invariants:
///
/// 1. **Single-threaded reader.** `Reporter::report_as` runs on the
///    main thread (the only thread that calls rustc's diagnostic
///    renderer, which is the only reader of `sf.src`). Workers
///    queue `Message` values over an mpsc channel — they hold vir
///    `Span`s with `BytePos` values, not `Arc<SourceFile>`, and
///    never read `sf.src`.
///
/// 2. **No concurrent mutation.** rustc creates `SourceFile`s during
///    file load and doesn't mutate them after. Our swap is the only
///    write to `sf.src` after construction, and it happens on the
///    main thread before any rendering (by virtue of being called
///    from `report_as` itself).
///
/// We also update `sf.multibyte_chars` because the sanitized content
/// contains no multi-byte chars (every byte was replaced with ASCII
/// space) while the original may. Without this update, rustc's visual
/// column accounting would treat each byte of a multi-byte char as a
/// column, drawing 3-wide carets under what visually displays as a
/// 1-column `≠`. `lines` and `normalized_pos` don't need updating —
/// the sanitizer preserves `\n` and `\r` byte-for-byte, so newline
/// positions and CRLF normalization match between sanitized and
/// original.
pub fn swap_source_for_diagnostics(
    source_map: &rustc_span::source_map::SourceMap,
    file_path: &str,
) -> bool {
    use rustc_span::FileName;

    let canonical = std::fs::canonicalize(file_path)
        .unwrap_or_else(|_| std::path::PathBuf::from(file_path));

    {
        let swapped = SWAPPED_FILES
            .get_or_init(|| std::sync::Mutex::new(std::collections::HashSet::new()))
            .lock()
            .unwrap();
        if swapped.contains(&canonical) {
            return true;
        }
    }

    let original = match crate::file_loader::original_for_path(&canonical) {
        Some(c) => c,
        None => return false,
    };

    let sf_arc = source_map.files().iter().find(|sf| match &sf.name {
        FileName::Real(real) => real
            .local_path()
            .and_then(|p| p.canonicalize().ok())
            .map(|p| p == canonical)
            .unwrap_or(false),
        _ => false,
    }).cloned();

    let sf = match sf_arc {
        Some(sf) => sf,
        None => return false,
    };

    let new_multibyte_chars = compute_multibyte_chars(&original);

    // SAFETY: See the doc-comment's safety section above. We take a
    // `*mut SourceFile` from the `Arc::as_ptr` and write `src` +
    // `multibyte_chars`. Single-threaded reader (`Reporter::report_as`
    // on main); no concurrent writes.
    unsafe {
        let sf_ptr = std::sync::Arc::as_ptr(&sf) as *mut rustc_span::SourceFile;
        (*sf_ptr).src = Some(original);
        (*sf_ptr).multibyte_chars = new_multibyte_chars;
    }

    SWAPPED_FILES
        .get_or_init(|| std::sync::Mutex::new(std::collections::HashSet::new()))
        .lock()
        .unwrap()
        .insert(canonical);
    true
}

// Note: this only returns Some for Spans in the local crate
// WARNING: this should only be called from rustc's thread, not from a Verus worker thread,
// because rustc may use its thread-local storage in .span().
pub(crate) fn from_raw_span(raw_span: &vir::messages::RawSpan) -> Option<Span> {
    if std::thread::current().name() != Some("rustc") {
        eprintln!(
            "warning: from_raw_span called from wrong thread; please report this as a Verus issue: {}",
            std::backtrace::Backtrace::force_capture(),
        );
    }
    let x = (&(**raw_span)) as &(dyn std::any::Any + Sync + Send); // rust subtyping limitaiton
    x.downcast_ref::<SpanData>().map(|data| data.span())
}

// Note: this produces a span suitable for reporting immediate errors;
// It should not be used to construct VIR AST node spans,
// and cannot be serialized an deserialized.
pub(crate) fn err_air_span(span: Span) -> vir::messages::Span {
    let raw_span = to_raw_span(span);
    let as_string = format!("{:?}", span);
    vir::messages::Span {
        raw_span, id: 0, data: vec![], as_string,
        // Diagnostic-only span used for error reporting; no
        // SourceMap available here. lean_verify's error formatter
        // falls back to as_string when start_loc is empty.
        start_loc: String::new(),
    }
}

/// Construct a `vir::messages::Span` pointing at the source line
/// that is `body_line_offset` lines past the `{` of a proof fn's
/// `by { ... }` tactic body.
///
/// Used by Tactus's proof-fn error reporter to attach each Lean
/// diagnostic to the corresponding line in the user's source — so
/// rustc's `-->` arrow points at the failing tactic line rather
/// than the enclosing fn signature.
///
/// `parent_span` is the rustc Span of the enclosing fn — we reuse
/// its `ctxt` and parent (so hygiene info matches) and adjust
/// `lo`/`hi` to the target line. `fn_start_loc` is the fn's
/// `Span::start_loc` (`file:line:col` of the fn's first byte),
/// used to derive `parent_span.lo()`'s file-relative position so
/// we can compute the target byte position globally. `start_byte`
/// is the file-relative byte offset of the `{` (from VIR's
/// `FunctionAttrsX.tactic_span`).
///
/// Returns `None` when `fn_start_loc` doesn't parse as
/// `file:line:col`, the source file can't be re-read from disk,
/// or the target line is past the file's end. Callers fall back
/// to `fn_span` in that case.
///
/// **No SourceMap needed.** We compute global BytePos arithmetic
/// relative to `parent_span.lo()`: positions in the same file
/// are contiguous in rustc's global address space, so the delta
/// between two file-relative offsets equals the delta between
/// their global positions. This lets the helper work from
/// worker threads (where `SourceMap` isn't `Sync`) the same as
/// from the main thread.
///
/// **Line correspondence**: `source_util::dedent` strips a
/// common left indent from non-empty lines but preserves blank
/// lines, so line N (0-indexed) in the dedented body always
/// corresponds to line N (0-indexed) of the raw content between
/// `{` and `}`. Raw content line 0 is on the same source-file
/// line as `{`; line N (N ≥ 1) is N source-file lines further
/// down.
pub(crate) fn tactic_body_line_span(
    parent_data: SpanData,
    fn_start_loc: &str,
    file_path: &str,
    start_byte: usize,
    body_line_offset: usize,
) -> Option<vir::messages::Span> {
    let (_, fn_line, fn_col) = parse_file_line_col(fn_start_loc)?;

    // Re-read the file. Costs one disk read per failing proof-fn
    // — negligible alongside the Lean check we just ran. Don't
    // depend on `SourceFile::src` because it's wrapped in
    // different ways across rustc versions and isn't always
    // available on worker threads.
    let src = std::fs::read_to_string(file_path).ok()?;
    let bytes = src.as_bytes();
    if start_byte >= bytes.len() { return None; }

    // Find the byte offset (in file) of the fn's first character.
    // Scan from start counting newlines until we reach `fn_line`,
    // then add `fn_col - 1` (cols are 1-indexed).
    let fn_first_byte = {
        let mut current_line = 1;
        let mut byte = 0;
        while current_line < fn_line && byte < bytes.len() {
            if bytes[byte] == b'\n' { current_line += 1; }
            byte += 1;
        }
        if current_line < fn_line { return None; }
        if fn_col == 0 { return None; }
        let pos = byte + fn_col - 1;
        if pos >= bytes.len() { return None; }
        pos
    };

    // Find the target line's byte range within the file. Body
    // line 0 starts at `start_byte + 1` (immediately after `{`).
    // Line N starts after the Nth newline.
    let mut byte = start_byte + 1;
    let mut newlines_seen = 0;
    while newlines_seen < body_line_offset && byte < bytes.len() {
        if bytes[byte] == b'\n' { newlines_seen += 1; }
        byte += 1;
    }
    if newlines_seen < body_line_offset { return None; }
    let line_lo_file = byte;
    let mut line_hi_file = line_lo_file;
    while line_hi_file < bytes.len() && bytes[line_hi_file] != b'\n' {
        line_hi_file += 1;
    }
    // Trim leading whitespace for prettier `^^^^` highlighting —
    // points the carets at the first non-whitespace token rather
    // than at indentation.
    let mut content_lo_file = line_lo_file;
    while content_lo_file < line_hi_file
        && matches!(bytes[content_lo_file], b' ' | b'\t')
    {
        content_lo_file += 1;
    }

    // Delta from the fn's first byte to the target line in the
    // file == delta in global BytePos space (file content is
    // contiguous in the global address space).
    let lo_delta = content_lo_file as i64 - fn_first_byte as i64;
    let hi_delta = line_hi_file as i64 - fn_first_byte as i64;
    let parent_lo_i = parent_data.lo.0 as i64;
    if parent_lo_i + lo_delta < 0 || parent_lo_i + hi_delta < 0 { return None; }
    let target_lo = BytePos((parent_lo_i + lo_delta) as u32);
    let target_hi = BytePos((parent_lo_i + hi_delta) as u32);

    // Construct a new `SpanData` directly — reusing the parent
    // span's `ctxt` and `parent` for hygiene continuity. We
    // deliberately avoid `Span::with_lo`/`with_hi` because those
    // round-trip through `Span::data()` which uses rustc's
    // thread-local interner and warns when called off the rustc
    // thread (verifier worker threads).
    let target_data = SpanData {
        lo: target_lo,
        hi: target_hi,
        ctxt: parent_data.ctxt,
        parent: parent_data.parent,
    };
    let raw_span: vir::messages::RawSpan = Arc::new(target_data);

    // Build a `start_loc` for lean_verify's `at <loc>:` fallback
    // formatting. We computed line/col ourselves; no SourceMap
    // lookup needed.
    let target_line = fn_line + count_newlines(bytes, fn_first_byte, content_lo_file);
    let target_col = content_lo_file - line_start_before(bytes, content_lo_file) + 1;
    let start_loc = format!("{}:{}:{}", file_path, target_line, target_col);

    Some(vir::messages::Span {
        raw_span,
        id: 0,
        data: vec![],
        as_string: format!("SpanData({:?}..{:?})", target_lo, target_hi),
        start_loc,
    })
}

fn count_newlines(bytes: &[u8], from: usize, to: usize) -> usize {
    bytes[from..to].iter().filter(|&&b| b == b'\n').count()
}

fn line_start_before(bytes: &[u8], pos: usize) -> usize {
    let mut p = pos;
    while p > 0 && bytes[p - 1] != b'\n' { p -= 1; }
    p
}

#[derive(Debug, Clone)]
enum ExternSourceInfo {
    Loaded { start_pos: BytePos, end_pos: BytePos },
    Delayed { filename: std::path::PathBuf, hash: Vec<u8> },
    None,
}

#[derive(Debug, Clone)]
struct ExternSourceFile {
    original_start_pos: BytePos,
    original_end_pos: BytePos,
    info: Arc<Mutex<ExternSourceInfo>>,
}

#[derive(Debug)]
struct CrateInfo {
    files: Vec<ExternSourceFile>,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub(crate) struct FileStartEndPos {
    // In case SourceMap doesn't load the file itself,
    // as a backup we can try to ask SourceMap to load from filename
    // (this is optional; it's ok if the filename is None):
    filename: Option<std::path::PathBuf>,
    // positions taken from BytePos:
    start_pos: u32,
    end_pos: u32,
}

pub(crate) type SpanContext = Arc<SpanContextX>;
pub(crate) struct SpanContextX {
    pub(crate) local_crate: StableCrateId,
    // Map StableCrateId.to_u64() to CrateInfo
    imported_crates: HashMap<u64, CrateInfo>,
    next_span_id: std::sync::atomic::AtomicU64,
    pub(crate) local_files: HashMap<Vec<u8>, FileStartEndPos>,
}

impl SpanContextX {
    pub(crate) fn new(
        tcx: TyCtxt,
        local_crate: StableCrateId,
        source_map: &SourceMap,
        original_crate_files: HashMap<u64, HashMap<Vec<u8>, FileStartEndPos>>,
        verus_externs: Option<&VerusExterns>,
    ) -> SpanContext {
        let mut imported_crates = HashMap::new();
        let mut local_files = HashMap::new();
        let mut remaining_crate_files = original_crate_files.clone();
        let path_mappings = verus_externs.map(|x| x.to_path_mappings());

        for source_file in source_map.files().iter() {
            match *source_file.external_src.borrow() {
                ExternalSource::Unneeded => {
                    let filename = match &source_file.name {
                        FileName::Real(real_file_name) => {
                            real_file_name.local_path().and_then(|path| path.canonicalize().ok())
                        }
                        _ => None,
                    };
                    let pos = FileStartEndPos {
                        filename,
                        start_pos: source_file.start_pos.0,
                        end_pos: source_file.start_pos.0 + source_file.normalized_source_len.0,
                    };
                    local_files.insert(source_file.src_hash.hash_bytes().to_vec(), pos);
                }
                ExternalSource::Foreign { .. } => {
                    let imported_crate = tcx.stable_crate_id(source_file.cnum).as_u64();
                    let start_pos = source_file.start_pos;
                    let end_pos =
                        BytePos(source_file.start_pos.0 + source_file.normalized_source_len.0);
                    let hash = source_file.src_hash.hash_bytes().to_vec();
                    if let Some(original) =
                        original_crate_files.get(&imported_crate).and_then(|x| x.get(&hash))
                    {
                        remaining_crate_files.get_mut(&imported_crate).unwrap().remove(&hash);
                        let info = if let FileName::Real(real_file_name) = &source_file.name {
                            // Ideally we'd change this into Remapped, but I don't know how to do that
                            if let (Some(path_mappings), Some(local_file_name)) =
                                (&path_mappings, real_file_name.local_path())
                            {
                                let mut found_match = None;
                                for (name, epath) in path_mappings.iter() {
                                    // search for source/<name> in local_file_path.components()
                                    let mut found = 0;
                                    let mut components = local_file_name.components();
                                    while let Some(c) = components.next() {
                                        if found == 0 {
                                            if c.as_os_str().to_str().unwrap() == "source" {
                                                found += 1;
                                            }
                                        } else if found == 1 {
                                            if c.as_os_str().to_str().unwrap() == name {
                                                found += 1;
                                                break;
                                            }
                                        }
                                    }
                                    let rest = components.as_path().to_path_buf();
                                    if found == 2 {
                                        found_match = Some((name, epath, rest));
                                        break;
                                    }
                                }
                                if let Some((_, base_path, file)) = found_match {
                                    let filename = base_path.join(file);
                                    ExternSourceInfo::Delayed { filename, hash }
                                } else {
                                    ExternSourceInfo::Loaded { start_pos, end_pos }
                                }
                            } else {
                                ExternSourceInfo::Loaded { start_pos, end_pos }
                            }
                        } else {
                            ExternSourceInfo::Loaded { start_pos, end_pos }
                        };
                        let file = ExternSourceFile {
                            original_start_pos: BytePos(original.start_pos),
                            original_end_pos: BytePos(original.end_pos),
                            info: Arc::new(Mutex::new(info)),
                        };

                        imported_crates
                            .entry(imported_crate)
                            .or_insert(CrateInfo { files: Vec::new() })
                            .files
                            .push(file);
                    }
                }
            }
        }
        for (imported_crate, files) in remaining_crate_files.iter() {
            if !imported_crates.contains_key(imported_crate) {
                imported_crates.insert(*imported_crate, CrateInfo { files: Vec::new() });
            }
            for (hash, original) in files.iter() {
                let info = if let Some(filename) = original.filename.clone() {
                    ExternSourceInfo::Delayed { filename, hash: hash.clone() }
                } else {
                    ExternSourceInfo::None
                };
                let file = ExternSourceFile {
                    original_start_pos: BytePos(original.start_pos),
                    original_end_pos: BytePos(original.end_pos),
                    info: Arc::new(Mutex::new(info)),
                };
                imported_crates.get_mut(&imported_crate).unwrap().files.push(file);
            }
        }

        for (_, info) in imported_crates.iter_mut() {
            info.files.sort_by_key(|f| f.original_start_pos);
        }

        let next_span_id = std::sync::atomic::AtomicU64::new(1);
        Arc::new(SpanContextX {
            local_crate, imported_crates, next_span_id, local_files,
        })
    }

    fn pos_to_extern_source_file(
        &self,
        imported_crate: u64,
        pos: BytePos,
    ) -> Option<ExternSourceFile> {
        if let Some(crate_info) = self.imported_crates.get(&imported_crate) {
            let i = crate_info.files.binary_search_by_key(&pos, |f| f.original_start_pos);
            let i = match i {
                Ok(i) => i,
                Err(i) if i == 0 => return None,
                Err(i) => i - 1,
            };
            let f = crate_info.files[i].clone();
            assert!(f.original_start_pos <= pos);
            if pos <= f.original_end_pos {
                return Some(f);
            }
        }
        None
    }

    fn pos_to_extern_source_file_resolve(
        &self,
        imported_crate: u64,
        pos: BytePos,
        source_map: Option<&SourceMap>,
    ) -> Option<(BytePos, BytePos, BytePos, BytePos)> {
        let ExternSourceFile { original_start_pos, original_end_pos, info } =
            self.pos_to_extern_source_file(imported_crate, pos)?;
        if let Some(source_map) = source_map {
            // If rustc didn't originally load the file into the source_map,
            // we can try to request that it load the file on demand.
            let mut info = info.lock().unwrap();
            let filename = if let ExternSourceInfo::Delayed { filename, hash } = &*info {
                Some((filename.clone(), hash.clone()))
            } else {
                None
            };
            if let Some((filename, hash)) = filename {
                *info = ExternSourceInfo::None;
                if let Ok(source_file) = source_map.load_file(&filename) {
                    if hash == source_file.src_hash.hash_bytes().to_vec() {
                        let start_pos = source_file.start_pos;
                        let end_pos =
                            BytePos(source_file.start_pos.0 + source_file.normalized_source_len.0);
                        *info = ExternSourceInfo::Loaded { start_pos, end_pos };
                    }
                }
            }
        }
        let locs = match &*info.lock().unwrap() {
            ExternSourceInfo::Loaded { start_pos, end_pos } => {
                Some((original_start_pos, original_end_pos, *start_pos, *end_pos))
            }
            _ => None,
        };
        locs
    }

    fn pack_span(&self, span: Span) -> Vec<u64> {
        // Encode as [StableCrateId, lo_hi]
        let span_data = span.data();
        let lo_hi = ((span_data.lo.0 as u64) << 32) | (span_data.hi.0 as u64);
        return vec![self.local_crate.as_u64(), lo_hi];
    }

    fn unpack_span(&self, packed: &Vec<u64>, source_map: Option<&SourceMap>) -> Option<Span> {
        // Encode as [StableCrateId, lo_hi]
        let crate_id = packed[0];
        let original_lo = BytePos((packed[1] >> 32) as u32);
        let original_hi = BytePos(packed[1] as u32);
        let locs = self.pos_to_extern_source_file_resolve(crate_id, original_lo, source_map);
        let (original_start_pos, original_end_pos, start_pos, end_pos) = if let Some(locs) = locs {
            locs
        } else {
            return None;
        };
        assert!(original_start_pos <= original_lo);
        assert!(original_hi <= original_end_pos);
        let lo = original_lo - original_start_pos + start_pos;
        let hi = original_hi - original_start_pos + start_pos;
        assert!(lo <= hi);
        assert!(hi <= end_pos);
        Some(SpanData { lo, hi, ctxt: rustc_span::SyntaxContext::root(), parent: None }.span())
    }

    pub(crate) fn get_next_span_id(&self) -> u64 {
        self.next_span_id.fetch_add(1, std::sync::atomic::Ordering::SeqCst)
    }

    /// Build a `vir::messages::Span` from a rustc `Span`, using
    /// `source_map` to pre-resolve the start position into a
    /// structured `file:line:col` (`start_loc` field) for
    /// `lean_verify`'s error formatter (#51).
    ///
    /// Takes `source_map` by reference because `SourceMap` isn't
    /// `Sync` — storing `Arc<SourceMap>` in `SpanContextX` would
    /// break `Send` for `Arc<SpanContextX>`. References are the
    /// right tool when the lifetime is bounded by the rustc
    /// session: callers fetch via `tcx.sess.source_map()` and
    /// the borrow is valid for the whole compilation.
    pub(crate) fn to_air_span(&self, span: Span, source_map: &SourceMap)
        -> vir::messages::Span
    {
        let raw_span = to_raw_span(span);
        let id = self.get_next_span_id();
        let data = self.pack_span(span);
        let as_string = format!("{:?}", span);
        // Direct SourceMap lookup — no string parsing. Format is
        // `<filename>:<line>:<col>` of the start position. The
        // file path comes from rustc's `FileName::prefer_local`
        // (which gives the user-visible Unix path on local
        // builds, matching what rustc itself reports). For
        // synthetic spans without a source position
        // (`span.is_dummy()`), leave `start_loc` empty so
        // `lean_verify` falls back to `as_string`.
        let start_loc = if span.is_dummy() {
            String::new()
        } else {
            let loc = source_map.lookup_char_pos(span.lo());
            // Render filename via the FileName::Real path (mirrors
            // `rust_to_vir_func.rs::tactic_span` handling). Other
            // FileName variants (synthetic, anon) fall back to
            // empty so lean_verify uses `as_string`.
            let filename = match &loc.file.name {
                FileName::Real(real) => real.local_path().and_then(|p| p.to_str().map(str::to_owned)),
                _ => None,
            };
            match filename {
                Some(f) => format!("{}:{}:{}", f, loc.line, loc.col.0 + 1),
                None => String::new(),
            }
        };
        vir::messages::Span { raw_span, id, data, as_string, start_loc }
    }

    pub(crate) fn from_air_span(
        &self,
        air_span: &vir::messages::Span,
        source_map: Option<&SourceMap>,
    ) -> Option<Span> {
        if let Some(span) = from_raw_span(&air_span.raw_span) {
            Some(span)
        } else {
            self.unpack_span(&air_span.data, source_map)
        }
    }

    pub(crate) fn spanned_new<X>(&self, span: Span, source_map: &SourceMap, x: X)
        -> Arc<Spanned<X>>
    {
        Spanned::new(self.to_air_span(span, source_map), x)
    }

    pub(crate) fn spanned_typed_new<X>(
        &self, span: Span, source_map: &SourceMap, typ: &Typ, x: X,
    ) -> Arc<SpannedTyped<X>> {
        SpannedTyped::new(&self.to_air_span(span, source_map), typ, x)
    }
}

impl<'tcx> crate::context::ContextX<'tcx> {
    /// Build an air span using the rustc session's `SourceMap`,
    /// available via `self.tcx`. Most callers use this rather
    /// than `self.spans.to_air_span(span, source_map)` directly
    /// — the `ContextX` already has rustc state, so threading
    /// the `&SourceMap` argument adds noise without value.
    pub(crate) fn to_air_span(&self, span: Span) -> vir::messages::Span {
        self.spans.to_air_span(span, self.tcx.sess.source_map())
    }

    pub(crate) fn spanned_new<X>(&self, span: Span, x: X) -> Arc<Spanned<X>> {
        self.spans.spanned_new(span, self.tcx.sess.source_map(), x)
    }

    pub(crate) fn spanned_typed_new<X>(&self, span: Span, typ: &Typ, x: X) -> Arc<SpannedTyped<X>> {
        self.spans.spanned_typed_new(span, self.tcx.sess.source_map(), typ, x)
    }

    pub(crate) fn spanned_typed_new_vir<X>(
        &self,
        span: &vir::messages::Span,
        typ: &Typ,
        x: X,
    ) -> Arc<SpannedTyped<X>> {
        let mut span = span.clone();
        span.id = self.spans.get_next_span_id();
        SpannedTyped::new(&span, typ, x)
    }
}

impl<'tcx> crate::context::BodyCtxt<'tcx> {
    pub(crate) fn to_air_span(&self, span: Span) -> vir::messages::Span {
        self.ctxt.to_air_span(span)
    }

    pub(crate) fn spanned_new<X>(&self, span: Span, x: X) -> Arc<Spanned<X>> {
        self.ctxt.spanned_new(span, x)
    }

    pub(crate) fn spanned_typed_new<X>(&self, span: Span, typ: &Typ, x: X) -> Arc<SpannedTyped<X>> {
        self.ctxt.spanned_typed_new(span, typ, x)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ── parse_file_line_col ──────────────────────────────────────

    #[test]
    fn parse_file_line_col_basic() {
        assert_eq!(
            parse_file_line_col("test.rs:18:5"),
            Some(("test.rs", 18, 5)),
        );
    }

    #[test]
    fn parse_file_line_col_path_with_colons() {
        // Windows-style path with drive letter — leading `:` must
        // stay in the path, only the trailing line:col gets split.
        assert_eq!(
            parse_file_line_col("C:\\foo\\bar.rs:18:5"),
            Some(("C:\\foo\\bar.rs", 18, 5)),
        );
    }

    #[test]
    fn parse_file_line_col_deep_path() {
        assert_eq!(
            parse_file_line_col("/home/user/proj/src/lib.rs:42:13"),
            Some(("/home/user/proj/src/lib.rs", 42, 13)),
        );
    }

    #[test]
    fn parse_file_line_col_rejects_empty_path() {
        // `:18:5` — would split to ("", 18, 5) but empty path is
        // never useful, so we reject.
        assert_eq!(parse_file_line_col(":18:5"), None);
    }

    #[test]
    fn parse_file_line_col_rejects_non_numeric() {
        assert_eq!(parse_file_line_col("test.rs:eighteen:5"), None);
        assert_eq!(parse_file_line_col("test.rs:18:five"), None);
    }

    #[test]
    fn parse_file_line_col_rejects_no_colons() {
        assert_eq!(parse_file_line_col("test.rs"), None);
        assert_eq!(parse_file_line_col(""), None);
    }

    #[test]
    fn parse_file_line_col_rejects_single_colon() {
        // Only one colon — `test.rs:5` doesn't have a line/col
        // split; reject rather than guess.
        assert_eq!(parse_file_line_col("test.rs:5"), None);
    }

    // ── compute_multibyte_chars ──────────────────────────────────

    #[test]
    fn multibyte_chars_pure_ascii() {
        assert!(compute_multibyte_chars("omega; simp_all").is_empty());
        assert!(compute_multibyte_chars("").is_empty());
        assert!(compute_multibyte_chars("hello\nworld").is_empty());
    }

    #[test]
    fn multibyte_chars_two_byte() {
        // `é` is U+00E9 = 2 bytes in UTF-8 (C3 A9).
        let v = compute_multibyte_chars("aéb");
        assert_eq!(v.len(), 1);
        assert_eq!(v[0].pos.0, 1);
        assert_eq!(v[0].bytes, 2);
    }

    #[test]
    fn multibyte_chars_three_byte() {
        // `≠` is U+2260 = 3 bytes (E2 89 A0).
        let v = compute_multibyte_chars("a ≠ b");
        assert_eq!(v.len(), 1);
        assert_eq!(v[0].pos.0, 2);
        assert_eq!(v[0].bytes, 3);
    }

    #[test]
    fn multibyte_chars_four_byte() {
        // `𝟙` is U+1D7D9 = 4 bytes (F0 9D 9F 99). 4-byte chars
        // are rare in tactic bodies but the helper handles them
        // for correctness.
        let v = compute_multibyte_chars("a𝟙b");
        assert_eq!(v.len(), 1);
        assert_eq!(v[0].pos.0, 1);
        assert_eq!(v[0].bytes, 4);
    }

    #[test]
    fn multibyte_chars_mixed() {
        // `a ≠ b ↑ c`: `≠` at byte 2 (3 bytes), `↑` at byte 8
        // (U+2191, 3 bytes — `b ↑` = `b` + space + `↑` starting
        // 4 bytes after `≠`'s start).
        let s = "a ≠ b ↑ c";
        let v = compute_multibyte_chars(s);
        assert_eq!(v.len(), 2);
        assert_eq!(v[0].bytes, 3);
        assert_eq!(v[1].bytes, 3);
        // Both positions correspond to the start byte of each
        // multi-byte sequence in the UTF-8 encoding.
        let bytes = s.as_bytes();
        assert!(bytes[v[0].pos.0 as usize] >= 0x80);
        assert!(bytes[v[1].pos.0 as usize] >= 0x80);
    }

    // Note: a shape-drift test comparing `compute_multibyte_chars`
    // against rustc's actual `SourceFile.multibyte_chars` would
    // be the highest-value guard against rustc-version drift,
    // but constructing a `SourceMap` requires
    // `create_session_globals_then` + `SourceMapInputs` which
    // have inconsistent privacy across rustc versions. The unit
    // tests above pin the behaviour we depend on at the
    // byte-level instead. If rustc ever widens what it considers
    // a multi-byte char (e.g., new Unicode categories), e2e
    // tests with the corresponding char in a tactic body would
    // fail with mis-aligned carets — the visible failure mode.
}
