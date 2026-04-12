/// The minimal Tactus prelude for Lean.
///
/// Prepended to every generated .lean file. As the prelude grows (Seq, Set, etc.),
/// edit TactusPrelude.lean directly — it's a real .lean file that can be
/// syntax-highlighted and tested independently.
pub const TACTUS_PRELUDE: &str = include_str!("../TactusPrelude.lean");
