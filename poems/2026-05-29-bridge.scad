// coerce_lexpr bridge — typed substitution session, 2026-05-29
//
// "Bidirectional wrapper-kind-and-depth coercion. Bridge `value`
//  (currently at `from_typ`) to `to_typ` by inserting `.deref` chain
//  and/or `.mk` chain to match wrapper sequences. Common-suffix
//  wraps stay untouched."
//
// — lean_verify/src/expr_shared.rs, coerce_lexpr
//
// The function spans a gap between two typings while preserving the
// inner that doesn't need to change. The sculpture is shaped the
// same way: two pillars separated by an arched opening you can see
// through, with the inner space preserved.
//
// Print orientation: stand on the bottom (the flat base of the two
// pillars). The arch is self-supporting because it's circular at the
// top — no overhangs steeper than ~45°. ~0.2mm layer height,
// ~20% infill.

$fn = 120;

// ── Dimensions (mm) ──
width = 70;             // total width across both pillars
total_height = 50;      // peak of the arch above the ground
pillar_width = 10;      // outer leg thickness
opening_width_top = 30; // arch opening width at its widest
wall_thickness = 8;     // distance from outer arch to inner arch
depth = 15;             // extrude depth (becomes thickness)

// ── Bridge silhouette ──
//
// OUTER: a horseshoe — two rectangles for the pillars, hulled with a
// circle at the top to form a rounded arch.
// INNER: a smaller horseshoe subtracted, leaving the bridge's
// characteristic gap-with-arched-top.

linear_extrude(height = depth) {
    difference() {
        // OUTER horseshoe
        hull() {
            // Pillar bottoms
            translate([-width/2, 0]) square([pillar_width, 1]);
            translate([width/2 - pillar_width, 0]) square([pillar_width, 1]);
            // Pillar tops (anchored slightly below where arch begins)
            translate([-width/2, total_height/2]) square([1, 1]);
            translate([width/2 - 1, total_height/2]) square([1, 1]);
            // Arch peak
            translate([0, total_height - 4]) circle(r = 4);
        }

        // INNER horseshoe (the bridge opening, reaching down to ground)
        translate([0, -1])  // -1 so the opening punches through the bottom
            hull() {
                // Opening bottom (full opening width)
                translate([-opening_width_top/2, 0])
                    square([opening_width_top, 1]);
                // Opening sides
                translate([-opening_width_top/2, total_height/2 - wall_thickness])
                    square([1, 1]);
                translate([opening_width_top/2 - 1, total_height/2 - wall_thickness])
                    square([1, 1]);
                // Opening peak (smaller circle, below the outer peak)
                translate([0, total_height - wall_thickness - 4])
                    circle(r = 3);
            }
    }
}
