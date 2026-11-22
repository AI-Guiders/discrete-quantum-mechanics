"""
Generate a ready-to-print ASCII STL mesh for the 12-coil Cuboctahedron O_2(3)
dielectric PLA/PETG frame around a 90 mm Petri dish:
  hardware/cuboctahedron_12coil_frame.stl
"""

from __future__ import annotations
import math
from pathlib import Path

Vec3 = tuple[float, float, float]


def v_add(a: Vec3, b: Vec3) -> Vec3:
    return (a[0] + b[0], a[1] + b[1], a[2] + b[2])


def v_sub(a: Vec3, b: Vec3) -> Vec3:
    return (a[0] - b[0], a[1] - b[1], a[2] - b[2])


def v_scale(a: Vec3, s: float) -> Vec3:
    return (a[0] * s, a[1] * s, a[2] * s)


def v_cross(a: Vec3, b: Vec3) -> Vec3:
    return (
        a[1] * b[2] - a[2] * b[1],
        a[2] * b[0] - a[0] * b[2],
        a[0] * b[1] - a[1] * b[0],
    )


def v_norm(a: Vec3) -> float:
    return math.sqrt(a[0] * a[0] + a[1] * a[1] + a[2] * a[2])


def v_unit(a: Vec3) -> Vec3:
    n = v_norm(a)
    return (a[0] / n, a[1] / n, a[2] / n) if n > 1e-12 else (0.0, 0.0, 1.0)


def orthonormal_basis(axis: Vec3) -> tuple[Vec3, Vec3, Vec3]:
    w = v_unit(axis)
    helper = (1.0, 0.0, 0.0) if abs(w[0]) < 0.8 else (0.0, 1.0, 0.0)
    u = v_unit(v_cross(w, helper))
    v = v_unit(v_cross(w, u))
    return u, v, w


def add_cylinder_strut(triangles: list[tuple[Vec3, Vec3, Vec3]], p1: Vec3, p2: Vec3, radius: float, n_seg: int = 12) -> None:
    axis = v_sub(p2, p1)
    u, v, _ = orthonormal_basis(axis)
    ring1: list[Vec3] = []
    ring2: list[Vec3] = []
    for i in range(n_seg):
        ang = 2.0 * math.pi * i / n_seg
        offset = v_add(v_scale(u, radius * math.cos(ang)), v_scale(v, radius * math.sin(ang)))
        ring1.append(v_add(p1, offset))
        ring2.append(v_add(p2, offset))
    for i in range(n_seg):
        j = (i + 1) % n_seg
        triangles.append((ring1[i], ring1[j], ring2[j]))
        triangles.append((ring1[i], ring2[j], ring2[i]))
        triangles.append((p1, ring1[j], ring1[i]))
        triangles.append((p2, ring2[i], ring2[j]))


def add_hollow_tube(
    triangles: list[tuple[Vec3, Vec3, Vec3]],
    center: Vec3,
    axis_dir: Vec3,
    length: float,
    r_outer: float,
    r_inner: float,
    n_seg: int = 16,
) -> None:
    u, v, w = orthonormal_basis(axis_dir)
    p1 = v_sub(center, v_scale(w, 0.5 * length))
    p2 = v_add(center, v_scale(w, 0.5 * length))
    out1, out2, in1, in2 = [], [], [], []
    for i in range(n_seg):
        ang = 2.0 * math.pi * i / n_seg
        radial = v_add(v_scale(u, math.cos(ang)), v_scale(v, math.sin(ang)))
        out1.append(v_add(p1, v_scale(radial, r_outer)))
        out2.append(v_add(p2, v_scale(radial, r_outer)))
        in1.append(v_add(p1, v_scale(radial, r_inner)))
        in2.append(v_add(p2, v_scale(radial, r_inner)))
    for i in range(n_seg):
        j = (i + 1) % n_seg
        # Outer wall:
        triangles.append((out1[i], out1[j], out2[j]))
        triangles.append((out1[i], out2[j], out2[i]))
        # Inner wall:
        triangles.append((in1[i], in2[j], in1[j]))
        triangles.append((in1[i], in2[i], in2[j]))
        # Front & back annular caps:
        triangles.append((out1[i], in1[j], out1[j]))
        triangles.append((out1[i], in1[i], in1[j]))
        triangles.append((out2[i], out2[j], in2[j]))
        triangles.append((out2[i], in2[j], in2[i]))


def generate_stl(out_path: Path) -> int:
    scale_step_mm = 52.0
    strut_radius_mm = 3.5
    coil_r_out = 11.0
    coil_r_in = 7.0
    coil_len = 16.0

    cuboct_vertices: list[Vec3] = [
        (0.0, 1.0, 1.0),
        (0.0, 1.0, -1.0),
        (0.0, -1.0, 1.0),
        (0.0, -1.0, -1.0),
        (1.0, 0.0, 1.0),
        (1.0, 0.0, -1.0),
        (-1.0, 0.0, 1.0),
        (-1.0, 0.0, -1.0),
        (1.0, 1.0, 0.0),
        (1.0, -1.0, 0.0),
        (-1.0, 1.0, 0.0),
        (-1.0, -1.0, 0.0),
    ]
    cuboct_edges = [
        (0, 4), (0, 6), (0, 8), (0, 10),
        (1, 5), (1, 7), (1, 8), (1, 10),
        (2, 4), (2, 6), (2, 9), (2, 11),
        (3, 5), (3, 7), (3, 9), (3, 11),
        (4, 8), (4, 9), (5, 8), (5, 9),
        (6, 10), (6, 11), (7, 10), (7, 11),
    ]

    triangles: list[tuple[Vec3, Vec3, Vec3]] = []

    # 1. 24 Cuboctahedron O_2(3) edges:
    for i0, i1 in cuboct_edges:
        p1 = v_scale(cuboct_vertices[i0], scale_step_mm)
        p2 = v_scale(cuboct_vertices[i1], scale_step_mm)
        add_cylinder_strut(triangles, p1, p2, strut_radius_mm, n_seg=12)

    # 2. 12 Inward-pointing coil bobbin sockets at O_2(3) vertices:
    for v in cuboct_vertices:
        center = v_scale(v, scale_step_mm)
        add_hollow_tube(triangles, center, v, coil_len, coil_r_out, coil_r_in, n_seg=16)

    # 3. Central 90 mm Petri dish equatorial cradle ring + 4 radial support bridges:
    add_hollow_tube(triangles, (0.0, 0.0, 0.0), (0.0, 0.0, 1.0), 8.0, 49.5, 45.5, n_seg=32)
    for k in (8, 9, 10, 11):
        v = cuboct_vertices[k]
        p_inner = v_scale(v_unit(v), 47.5)
        p_outer = v_scale(v, scale_step_mm)
        add_cylinder_strut(triangles, p_inner, p_outer, strut_radius_mm, n_seg=12)

    lines = ["solid cuboctahedron_12coil_frame"]
    for a, b, c in triangles:
        n = v_unit(v_cross(v_sub(b, a), v_sub(c, a)))
        lines.append(f"  facet normal {n[0]:.6f} {n[1]:.6f} {n[2]:.6f}")
        lines.append("    outer loop")
        lines.append(f"      vertex {a[0]:.4f} {a[1]:.4f} {a[2]:.4f}")
        lines.append(f"      vertex {b[0]:.4f} {b[1]:.4f} {b[2]:.4f}")
        lines.append(f"      vertex {c[0]:.4f} {c[1]:.4f} {c[2]:.4f}")
        lines.append("    endloop")
        lines.append("  endfacet")
    lines.append("endsolid cuboctahedron_12coil_frame\n")
    out_path.write_text("\n".join(lines), encoding="utf-8", newline="\n")
    return len(triangles)


if __name__ == "__main__":
    stl_file = Path(__file__).resolve().parent.parent / "hardware" / "cuboctahedron_12coil_frame.stl"
    n_tri = generate_stl(stl_file)
    print(f"Generated {stl_file} ({n_tri} triangles, {stl_file.stat().st_size} bytes)")
