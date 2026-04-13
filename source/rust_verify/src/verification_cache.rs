use sha2::{Digest, Sha256};
use std::collections::{HashMap, HashSet, VecDeque};
use std::path::PathBuf;
use vir::ast::Fun;
use vir::ast_util::fun_as_friendly_rust_name;

use crate::commands::{QueryOp, Style};

/// Incremental SHA-256 hasher.
#[derive(Clone)]
pub struct ContextHasher {
    hasher: Sha256,
}

impl ContextHasher {
    pub fn new() -> Self {
        ContextHasher { hasher: Sha256::new() }
    }

    pub fn update_tag(&mut self, tag: &str) {
        self.hasher.update(tag.as_bytes());
        self.hasher.update(b"\n");
    }

    pub fn update_debug(&mut self, val: &impl std::fmt::Debug) {
        self.hasher.update(format!("{:?}\n", val).as_bytes());
    }

    pub fn finalize(self) -> String {
        hex::encode(self.hasher.finalize())
    }
}

/// Caching state for one verification bucket. Tracks a base context hash
/// (datatypes, traits) and per-function SST hashes, uses the call graph
/// to build keys that include only relevant dependencies.
pub struct BucketCache {
    cache_dir: PathBuf,
    base: ContextHasher,
    fn_hashes: HashMap<Fun, String>,
}

impl BucketCache {
    pub fn new(base: ContextHasher) -> Self {
        let cache_dir = PathBuf::from("target/verus-cache");
        let _ = std::fs::create_dir_all(&cache_dir);
        BucketCache { cache_dir, base, fn_hashes: HashMap::new() }
    }

    /// Record a function's SST hash (deterministic, source-level).
    pub fn record_function(&mut self, function: &vir::sst::FunctionSst) {
        let mut h = ContextHasher::new();
        h.update_debug(&function.x);
        self.fn_hashes.insert(function.x.name.clone(), h.finalize());
    }

    pub fn lookup(&self, key: &str) -> bool {
        self.cache_dir.join(format!("{}.cache", key)).exists()
    }

    pub fn store(&self, key: &str) {
        let _ = std::fs::write(self.cache_dir.join(format!("{}.cache", key)), b"");
    }

    /// Compute a cache key for a cacheable query type, or None otherwise.
    /// BFS over the call graph ensures only transitive dependencies are in the key.
    pub fn try_key(
        &self,
        bucket_id: &crate::buckets::BucketId,
        global_ctx: &vir::context::GlobalCtx,
        query_op: &QueryOp,
        function: &vir::sst::FunctionSst,
    ) -> Option<String> {
        match query_op {
            QueryOp::SpecTermination
            | QueryOp::Body(Style::Normal)
            | QueryOp::Body(Style::CheckApiSafety) => {}
            _ => return None,
        }
        // BFS for transitive function dependencies (including self)
        let mut deps: HashSet<Fun> = HashSet::new();
        let mut queue: VecDeque<vir::recursion::Node> = VecDeque::new();
        deps.insert(function.x.name.clone());
        queue.push_back(vir::recursion::Node::Fun(function.x.name.clone()));
        while let Some(node) = queue.pop_front() {
            for edge in global_ctx.func_call_graph.get_edges_from(&node) {
                match edge {
                    vir::recursion::Node::Fun(f) => {
                        if deps.insert(f.clone()) {
                            queue.push_back(edge.clone());
                        }
                    }
                    vir::recursion::Node::SpanInfo { .. } => queue.push_back(edge.clone()),
                    _ => {}
                }
            }
        }
        // Key = function name + bucket + base context + sorted dep hashes + query op
        let mut h = self.base.clone();
        h.update_tag(&fun_as_friendly_rust_name(&function.x.name));
        h.update_debug(bucket_id);
        let mut sorted: Vec<&Fun> = deps.iter().collect();
        sorted.sort_by_key(|f| fun_as_friendly_rust_name(f));
        for f in sorted {
            if let Some(fh) = self.fn_hashes.get(f) {
                h.update_tag(&format!("fn:{}:{}", fun_as_friendly_rust_name(f), fh));
            }
        }
        h.update_tag(&format!("{:?}", query_op));
        Some(h.finalize())
    }
}
