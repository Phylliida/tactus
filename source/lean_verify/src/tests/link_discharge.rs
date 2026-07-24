//! Link-discharge composer pins for the two premise classes added by
//! the endgame milestone C (DESIGN-bootstrap-endgame §2): N1 HoistEq
//! equation hyps (let-replay + rfl) and the fn's own requires clause
//! (carried hypothesis binder). Shapes are trimmed from the real
//! tactus-core sidecars (lib__seq_assume_gates, lib__wp_sound_bites_
//! assert) — the live pins are the gate's discharge census reaching
//! 0-pending.

use super::*;

/// Empty resolution tables shared by every pin (no wf machinery in
/// these shapes).
struct Tables {
    sidecars: HashMap<String, FnSidecar>,
    closed: HashMap<String, ClosedMeta>,
    variants: HashMap<String, Vec<(String, Vec<String>)>>,
    wf: HashMap<String, WfInfo>,
    wf_lemmas: HashMap<String, crate::wf_synth::FnWfSig>,
    wf_specs: HashMap<String, crate::wf_synth::DtWfSpec>,
}

impl Tables {
    fn new() -> Self {
        Tables {
            sidecars: HashMap::new(),
            closed: HashMap::new(),
            variants: HashMap::new(),
            wf: HashMap::new(),
            wf_lemmas: HashMap::new(),
            wf_specs: HashMap::new(),
        }
    }
    fn ctx(&self) -> Ctx<'_> {
        Ctx {
            sidecars: &self.sidecars,
            closed: &self.closed,
            variants: &self.variants,
            wf: &self.wf,
            wf_lemmas: &self.wf_lemmas,
            wf_specs: &self.wf_specs,
            ns: "lib",
        }
    }
}

/// Trimmed seq_assume_gates: params, a hoisted FrameList let pair, a
/// hoisted tmp pair, and one call whose args reference both binders.
const HOIST_SIDECAR: &str = r#"{"fn":"lib__hoist_pin","vcs":[{
  "name":"_tactus_postcondition_hoist_pin_at_lib_1_1_1",
  "leaf":"/- @rust:lib.rs:1:1 -/ lib.wp_stm lib.FrameList.FNil (lib.StmData.Assume 0 q 0) = lib.GoalList.Nil",
  "spine":[
    {"k":"all","name":"q","ty":"Int"},
    {"k":"all","name":"h_q_bound","ty":"0 ≤ q ∧ q < 18446744073709551616"},
    {"k":"all","name":"fh","ty":"lib.FrameList"},
    {"k":"all","name":"_h_fh_hoist1","ty":"fh = lib.FrameList.FHyp 0 q 0 (Tactus.Box.mk lib.FrameList.FNil)","p":"hoist","binder":"fh"},
    {"k":"all","name":"tmp__1","ty":"lib.StmData"},
    {"k":"all","name":"_h_tmp__1_hoist1","ty":"tmp__1 = lib.StmData.Assume 0 q 0","p":"hoist","binder":"tmp__1"},
    {"k":"all","name":"_tactus_ret_1","ty":"Unit"},
    {"k":"imp","p":"call","callee":"u_wp_assume","self":false,
     "args":[{"text":"fh","tag":"expr"},{"text":"Tactus.Box.mk tmp__1","tag":"expr"}]}
  ]}]}"#;

/// Trimmed wp_sound_bites_assert: params, a named requires hyp, a
/// referenced plain let, and one call.
const REQ_SIDECAR: &str = r#"{"fn":"lib__req_pin","vcs":[{
  "name":"_tactus_postcondition_req_pin_at_lib_2_1_1",
  "leaf":"/- @rust:lib.rs:2:1 -/ he (lib.render_exp o) st",
  "spine":[
    {"k":"all","name":"he","ty":"lib.ExprData → (Int → Int) → Prop"},
    {"k":"all","name":"o","ty":"lib.RawExp"},
    {"k":"all","name":"st","ty":"Int → Int"},
    {"k":"all","name":"h_req0","ty":"lib.holds_all he (lib.wp_stm lib.FrameList.FNil (lib.StmData.Assert o 0 0 0)) st","p":"requires","i":0},
    {"k":"let","name":"tmp__1","v":"lib.FrameList.FNil"},
    {"k":"all","name":"_tactus_ret_1","ty":"Unit"},
    {"k":"imp","p":"call","callee":"u_esf_assert","self":false,
     "args":[{"text":"he","tag":"param:he"},{"text":"tmp__1","tag":"expr"},{"text":"o","tag":"param:o"}]}
  ]}]}"#;

/// A zero-spine callee sidecar (so callee_lead resolves).
const CALLEE_SIDECAR: &str = r#"{"fn":"lib__callee","vcs":[{
  "name":"_tactus_postcondition_callee_at_lib_3_1_1",
  "leaf":"True",
  "spine":[]}]}"#;

fn close_one(sidecar: &str, rel: &str, callees: &[&str]) -> Outcome {
    let mut t = Tables::new();
    t.sidecars.insert(rel.to_string(), parse_sidecar(sidecar).expect("sidecar parses"));
    for c in callees {
        t.sidecars.insert(c.to_string(), parse_sidecar(CALLEE_SIDECAR).unwrap());
        t.closed.insert(c.to_string(), ClosedMeta::default());
    }
    try_close(rel, &t.sidecars[rel], &t.ctx())
}

#[test]
fn hoist_eq_parses_binder_and_rhs() {
    let sc = parse_sidecar(HOIST_SIDECAR).unwrap();
    let hoists: Vec<_> = sc.vcs[0]
        .spine
        .iter()
        .filter_map(|n| match n {
            Node::HoistEq { binder, v } => Some((binder.clone(), v.clone())),
            _ => None,
        })
        .collect();
    assert_eq!(hoists.len(), 2);
    assert_eq!(hoists[0].0, "fh");
    assert_eq!(hoists[0].1, "lib.FrameList.FHyp 0 q 0 (Tactus.Box.mk lib.FrameList.FNil)");
    assert_eq!(hoists[1], ("tmp__1".into(), "lib.StmData.Assume 0 q 0".into()));
    // The hoist value binders are NOT leading params.
    let (lead, _) = leading_alls(&sc.vcs[0].spine);
    let names: Vec<_> = lead
        .iter()
        .map(|n| match n {
            Node::All { name, .. } => name.as_str(),
            _ => "",
        })
        .collect();
    assert_eq!(names, vec!["q", "h_q_bound"]);
}

#[test]
fn hoist_close_replays_lets_and_rfl() {
    let o = close_one(HOIST_SIDECAR, "hoist_pin", &["u_wp_assume"]);
    let Outcome::Closed { text, kind, .. } = o else {
        panic!("expected close, got pend");
    };
    assert_eq!(kind, "straight-line");
    // Both hoisted lets replay, in spine order.
    let i_fh = text.find("let fh := lib.FrameList.FHyp 0 q 0").expect("fh let");
    let i_tmp = text.find("let tmp__1 := lib.StmData.Assume 0 q 0;").expect("tmp let");
    assert!(i_fh < i_tmp);
    // The application instantiates the binders by name and closes each
    // equation premise with rfl, in telescope order.
    assert!(text.contains("q h_q_bound fh rfl tmp__1 rfl ()"), "app order: {}", text);
    // The theorem binders are the true params only.
    assert!(text.contains("theorem hoist_pin_closed (q : Int)"), "binders: {}", text);
    assert!(!text.contains("(fh : "), "hoist binder leaked into signature: {}", text);
}

#[test]
fn requires_close_carries_hypothesis_binder() {
    let o = close_one(REQ_SIDECAR, "req_pin", &["u_esf_assert"]);
    let Outcome::Closed { text, kind, .. } = o else {
        panic!("expected close, got pend");
    };
    assert_eq!(kind, "straight-line");
    // The requires is a binder of the closed theorem…
    assert!(
        text.contains("(h_req0 : lib.holds_all he (lib.wp_stm"),
        "requires binder: {}",
        text
    );
    // …and is fed back positionally at its telescope slot.
    assert!(text.contains("st h_req0"), "requires fed: {}", text);
    // The referenced plain let still replays.
    assert!(text.contains("let tmp__1 := lib.FrameList.FNil;"), "let replay: {}", text);
}

#[test]
fn requires_carrying_callee_pends_loudly() {
    // A caller whose call premise targets the requires-carrying fn.
    let caller = r#"{"fn":"lib__caller","vcs":[{
      "name":"_tactus_postcondition_caller_at_lib_4_1_1",
      "leaf":"True",
      "spine":[
        {"k":"all","name":"x","ty":"Int"},
        {"k":"all","name":"_tactus_ret_1","ty":"Unit"},
        {"k":"imp","p":"call","callee":"req_pin","self":false,
         "args":[{"text":"x","tag":"param:x"}]}
      ]}]}"#;
    let mut t = Tables::new();
    t.sidecars.insert("caller".to_string(), parse_sidecar(caller).unwrap());
    t.sidecars.insert("req_pin".to_string(), parse_sidecar(REQ_SIDECAR).unwrap());
    t.closed.insert("req_pin".to_string(), ClosedMeta::default());
    match try_close("caller", &t.sidecars["caller"], &t.ctx()) {
        Outcome::Pending(r) => {
            assert!(r.contains("carries requires"), "reason: {}", r)
        }
        Outcome::Closed { text, .. } => panic!("should pend, closed: {}", text),
    }
}

#[test]
fn malformed_hoist_stays_other_and_pends() {
    // ty does not start with "{binder} = " — must NOT silently
    // misparse; the fn pends with the pre-existing reason.
    let bad = r#"{"fn":"lib__bad","vcs":[{
      "name":"_tactus_postcondition_bad_at_lib_5_1_1",
      "leaf":"True",
      "spine":[
        {"k":"all","name":"x","ty":"Int"},
        {"k":"all","name":"_h_y_hoist1","ty":"z = 3","p":"hoist","binder":"y"}
      ]}]}"#;
    let sc = parse_sidecar(bad).unwrap();
    assert!(sc.vcs[0].spine.iter().any(|n| matches!(n, Node::Other)));
    let t = Tables::new();
    match try_close("bad", &sc, &t.ctx()) {
        Outcome::Pending(r) => assert!(r.contains("other-hyp"), "reason: {}", r),
        Outcome::Closed { text, .. } => panic!("should pend, closed: {}", text),
    }
}

#[test]
fn hoisted_binder_in_leaf_pends_precisely() {
    let bad = r#"{"fn":"lib__leafref","vcs":[{
      "name":"_tactus_postcondition_leafref_at_lib_6_1_1",
      "leaf":"lib.f fh = lib.GoalList.Nil",
      "spine":[
        {"k":"all","name":"q","ty":"Int"},
        {"k":"all","name":"fh","ty":"lib.FrameList"},
        {"k":"all","name":"_h_fh_hoist1","ty":"fh = lib.FrameList.FNil","p":"hoist","binder":"fh"}
      ]}]}"#;
    let sc = parse_sidecar(bad).unwrap();
    let t = Tables::new();
    match try_close("leafref", &sc, &t.ctx()) {
        Outcome::Pending(r) => {
            assert!(r.contains("hoisted binder fh in postcondition leaf"), "reason: {}", r)
        }
        Outcome::Closed { text, .. } => panic!("should pend, closed: {}", text),
    }
}
