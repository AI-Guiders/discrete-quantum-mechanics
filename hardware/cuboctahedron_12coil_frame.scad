// ============================================================================
// hardware/cuboctahedron_12coil_frame.scad
// Parametric 3D-Printable PLA/PETG Cuboctahedron O_2(3) Frame for 12 Coils
// around a standard 90 mm Quartz/Borosilicate Glass Petri Dish (Z(SiO2) = 30).
//
// Geometry derived directly from the 12 integer vertices of O_2(3):
//   (|e_k|^2 = 2, 4 neighbors at 60 deg, 2 at 90 deg, 4 at 120 deg, 1 at 180 deg)
//   - Petri dish outer diameter: 90.0 mm (+1.0 mm clearance = 91.0 mm cradle)
//   - Cuboctahedron vertex radius R_oct = 52.0 mm (radial distance = 52 * sqrt(2) = 73.54 mm)
//   - 12 cylindrical coil bobbins (OD = 22 mm, ID = 14 mm, M3 nylon mount hole)
//   - 4 = d_in(square) silicone vibration-damping foot sockets on bottom ring
// ============================================================================

$fn = 64;

petri_od_mm      = 91.0;
petri_height_mm  = 18.0;
scale_step_mm    = 52.0;   // Integer lattice step (+/-1, +/-1, 0) * 52 mm -> R = 73.54 mm
coil_holder_od   = 22.0;
coil_holder_id   = 14.0;
coil_holder_len  = 16.0;
strut_radius_mm  = 3.5;

// Exact 12 vertices of the Cuboctahedron O_2(3):
cuboct_vertices = [
    [ 0,  1,  1], [ 0,  1, -1], [ 0, -1,  1], [ 0, -1, -1],
    [ 1,  0,  1], [ 1,  0, -1], [-1,  0,  1], [-1,  0, -1],
    [ 1,  1,  0], [ 1, -1,  0], [-1,  1,  0], [-1, -1,  0]
];

// 24 edges of O_2(3) (pairs (j, k) with dot product e_j . e_k == +1, i.e. 60-degree neighbors):
cuboct_edges = [
    [0, 4], [0, 6], [0, 8], [0, 10],
    [1, 5], [1, 7], [1, 8], [1, 10],
    [2, 4], [2, 6], [2, 9], [2, 11],
    [3, 5], [3, 7], [3, 9], [3, 11],
    [4, 8], [4, 9], [5, 8], [5, 9],
    [6, 10], [6, 11], [7, 10], [7, 11]
];

module strut_between(p1, p2, r) {
    v = p2 - p1;
    L = norm(v);
    hull() {
        translate(p1) sphere(r = r);
        translate(p2) sphere(r = r);
    }
}

module coil_socket_at(v_unit) {
    p = v_unit * scale_step_mm;
    L = norm(p);
    // Orient coil axis pointing directly toward the Petri dish center (0, 0, 0):
    ang_z = atan2(p[1], p[0]);
    ang_y = acos(p[2] / L);
    translate(p)
    rotate([0, ang_y, ang_z])
    difference() {
        cylinder(h = coil_holder_len, d = coil_holder_od, center = true);
        cylinder(h = coil_holder_len + 2, d = coil_holder_id, center = true);
    }
}

module petri_dish_cradle() {
    difference() {
        union() {
            // Equatorial support ring for 90 mm quartz glass Petri dish:
            cylinder(h = 8.0, d = petri_od_mm + 8.0, center = true);
            // 4 radial bridges to the 4 equatorial O_2(3) vertices (+/-1, +/-1, 0):
            for (k = [8, 9, 10, 11]) {
                strut_between(
                    cuboct_vertices[k] * (petri_od_mm / (2 * sqrt(2))),
                    cuboct_vertices[k] * scale_step_mm,
                    strut_radius_mm
                );
            }
        }
        // Inner seat for 90 mm Petri dish:
        translate([0, 0, -1.0])
            cylinder(h = petri_height_mm, d = petri_od_mm, center = true);
        // Central optical window (d = 82 mm) for bottom photodiode / webcam feedback:
        cylinder(h = 20.0, d = petri_od_mm - 8.0, center = true);
    }
}

// Assemble full 3D-printable O_2(3) dielectric PLA/PETG frame:
union() {
    // 1. All 24 cuboctahedron structural edges:
    for (e = cuboct_edges) {
        strut_between(
            cuboct_vertices[e[0]] * scale_step_mm,
            cuboct_vertices[e[1]] * scale_step_mm,
            strut_radius_mm
        );
    }
    // 2. All 12 inward-pointing coil bobbin sockets:
    for (v = cuboct_vertices) {
        coil_socket_at(v);
    }
    // 3. Central 90 mm Petri dish equatorial cradle:
    petri_dish_cradle();
}
