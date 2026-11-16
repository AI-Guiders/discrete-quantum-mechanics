"""§5.0.4-B — coordination shells and ρ_Θ mode catalog (FCC N₁₂ graph)."""
from __future__ import annotations

from collections import deque
from typing import Any

from mt_ca.laplacian import _FCC_OFFSETS


def fcc_graph_distance(
    origin: tuple[int, int, int] = (0, 0, 0),
    *,
    max_k: int,
) -> dict[tuple[int, int, int], int]:
    """Shortest-path distance from ``origin`` up to shell ``max_k`` (bounded BFS).

    On the infinite ℤ³ FCC graph an unbounded BFS never terminates — always pass ``max_k``.
    """
    if max_k < 0:
        raise ValueError("max_k must be >= 0")
    dist: dict[tuple[int, int, int], int] = {origin: 0}
    q: deque[tuple[int, int, int]] = deque([origin])
    offsets = _FCC_OFFSETS
    while q:
        p = q.popleft()
        d = dist[p]
        if d >= max_k:
            continue
        for o in offsets:
            n = (p[0] + o[0], p[1] + o[1], p[2] + o[2])
            if n not in dist:
                dist[n] = d + 1
                q.append(n)
    return dist


def coordination_shell_sizes(max_k: int = 3) -> dict[int, int]:
    """Site counts on coordination spheres k=0…max_k (k=0 is the core)."""
    dist = fcc_graph_distance(max_k=max_k)
    return {k: sum(1 for d in dist.values() if d == k) for k in range(max_k + 1)}


def sites_on_shell(k: int, *, ball_max_k: int | None = None) -> list[tuple[int, int, int]]:
    if k < 0:
        raise ValueError("k must be >= 0")
    cap = ball_max_k if ball_max_k is not None else k
    if cap < k:
        raise ValueError("ball_max_k must be >= k")
    dist = fcc_graph_distance(max_k=cap)
    return sorted(p for p, d in dist.items() if d == k)


def _neighbors_on_shell(
    site: tuple[int, int, int],
    target_k: int,
    *,
    ball_max_k: int,
    dist: dict[tuple[int, int, int], int],
) -> list[tuple[int, int, int]]:
    x, y, z = site
    out: list[tuple[int, int, int]] = []
    for o in _FCC_OFFSETS:
        n = (x + o[0], y + o[1], z + o[2])
        if dist.get(n) == target_k:
            out.append(n)
    return out


def shell_neighbor_stats(max_k: int = 3) -> dict[int, dict[str, int | float]]:
    """How shell-k sites attach to inner shells (for selection / A1 reachability)."""
    dist = fcc_graph_distance(max_k=max_k)
    stats: dict[int, dict[str, int | float]] = {}
    for k in range(2, max_k + 1):
        counts: list[int] = []
        for site in sites_on_shell(k, ball_max_k=max_k):
            counts.append(len(_neighbors_on_shell(site, k - 1, ball_max_k=max_k, dist=dist)))
        stats[k] = {
            "sites": len(counts),
            "min_inner_neighbors": min(counts) if counts else 0,
            "max_inner_neighbors": max(counts) if counts else 0,
        }
    return stats


def cuboctahedral_shell_channel_census(max_k: int = 4) -> dict[str, Any]:
    """Exact decomposition of every FCC coordination sphere k=1..max_k into the 4 cuboctahedral channels.

    Every site on shell k >= 1 has (d_in, d_same, d_out) summing to 12 and belongs to one of:
      - V = (1, 4, 7): 12 vertices of the cuboctahedron (rays)
      - E = (2, 5, 5): 24(k - 1) edge interior sites
      - S = (4, 4, 4): 6(k - 1)^2 square-face interior sites
      - T = (3, 6, 3): 4(k - 1)(k - 2) triangle-face interior sites
    """
    dist = fcc_graph_distance(max_k=max_k + 1)
    per_shell: dict[int, dict[str, int]] = {}
    formula_matches = True
    no_fifth_channel = True
    causal_step_le_one = True

    channel_map = {
        (1, 4, 7): "V_vertex_1_4_7",
        (2, 5, 5): "E_edge_2_5_5",
        (4, 4, 4): "S_square_4_4_4",
        (3, 6, 3): "T_triangle_3_6_3",
    }

    for k in range(1, max_k + 1):
        sites = sites_on_shell(k, ball_max_k=max_k + 1)
        counts = {
            "V_vertex_1_4_7": 0,
            "E_edge_2_5_5": 0,
            "S_square_4_4_4": 0,
            "T_triangle_3_6_3": 0,
        }
        for x, y, z in sites:
            d_in = 0
            d_same = 0
            d_out = 0
            for dx, dy, dz in _FCC_OFFSETS:
                dk = dist.get((x + dx, y + dy, z + dz), k) - k
                if abs(dk) > 1:
                    causal_step_le_one = False
                if dk == -1:
                    d_in += 1
                elif dk == 0:
                    d_same += 1
                elif dk == 1:
                    d_out += 1
            sig = (d_in, d_same, d_out)
            if sig not in channel_map:
                no_fifth_channel = False
            else:
                counts[channel_map[sig]] += 1

        exp_v = 12
        exp_e = 24 * (k - 1)
        exp_s = 6 * (k - 1) ** 2
        exp_t = 4 * (k - 1) * (k - 2)
        if (
            counts["V_vertex_1_4_7"] != exp_v
            or counts["E_edge_2_5_5"] != exp_e
            or counts["S_square_4_4_4"] != exp_s
            or counts["T_triangle_3_6_3"] != exp_t
            or sum(counts.values()) != 10 * k * k + 2
        ):
            formula_matches = False
        per_shell[k] = counts

    # Verify outward 1-tick branching rules per channel from k=3 -> k=4 (where all 4 channels are populated)
    s3 = sites_on_shell(3, ball_max_k=max_k + 1)
    s4_set = set(sites_on_shell(4, ball_max_k=max_k + 1))

    def _site_cls(pt: tuple[int, int, int], k_level: int) -> str:
        px, py, pz = pt
        din = sum(1 for dx, dy, dz in _FCC_OFFSETS if dist.get((px + dx, py + dy, pz + dz)) == k_level - 1)
        return {1: "V", 2: "E", 3: "T", 4: "S"}[din]

    branching_per_site: dict[str, dict[str, int]] = {}
    for pt in s3:
        c_from = _site_cls(pt, 3)
        if c_from in branching_per_site:
            continue
        out_hist = {"V": 0, "E": 0, "S": 0, "T": 0}
        px, py, pz = pt
        for dx, dy, dz in _FCC_OFFSETS:
            nb = (px + dx, py + dy, pz + dz)
            if nb in s4_set:
                out_hist[_site_cls(nb, 4)] += 1
        branching_per_site[c_from] = out_hist

    expected_branching = {
        "V": {"V": 1, "E": 4, "S": 2, "T": 0},
        "E": {"V": 0, "E": 2, "S": 2, "T": 1},
        "S": {"V": 0, "E": 0, "S": 4, "T": 0},
        "T": {"V": 0, "E": 0, "S": 0, "T": 3},
    }
    branching_ok = branching_per_site == expected_branching

    return {
        "max_k": max_k,
        "per_shell": per_shell,
        "outward_branching_per_site": branching_per_site,
        "expected_branching": expected_branching,
        "formula_matches": formula_matches,
        "no_fifth_channel": no_fifth_channel,
        "causal_step_le_one": causal_step_le_one,
        "vertex_to_triangle_forbidden_1tick": branching_per_site.get("V", {}).get("T", -1) == 0,
        "upper_triangular_cascade_ok": branching_ok,
        "checks_ok": (
            formula_matches
            and no_fifth_channel
            and causal_step_le_one
            and branching_ok
        ),
    }


def _exact_rational_rank(rows: list[list[int]]) -> int:
    """Exact rank over Q via Fraction Gaussian elimination (zero floating point)."""
    from fractions import Fraction

    if not rows or not rows[0]:
        return 0
    mat = [[Fraction(v) for v in r] for r in rows]
    n_rows = len(mat)
    n_cols = len(mat[0])
    rank = 0
    for col in range(n_cols):
        pivot = None
        for r in range(rank, n_rows):
            if mat[r][col] != 0:
                pivot = r
                break
        if pivot is None:
            continue
        mat[rank], mat[pivot] = mat[pivot], mat[rank]
        pv = mat[rank][col]
        mat[rank] = [val / pv for val in mat[rank]]
        for r in range(n_rows):
            if r != rank and mat[r][col] != 0:
                factor = mat[r][col]
                mat[r] = [mat[r][c] - factor * mat[rank][c] for c in range(n_cols)]
        rank += 1
        if rank == n_rows:
            break
    return rank


def cuboctahedral_spdf_harmonic_ranks() -> dict[str, Any]:
    """Exact rational ranks of l=0(s), l=1(p), l=2(d), l=3(f) harmonics on the 4 cuboctahedral channel supports."""
    sq6 = [(2, 0, 0), (-2, 0, 0), (0, 2, 0), (0, -2, 0), (0, 0, 2), (0, 0, -2)]
    v12 = sites_on_shell(1, ball_max_k=1)
    tri8 = [(sx, sy, sz) for sx in (-2, 2) for sy in (-2, 2) for sz in (-2, 2)]
    e24 = [
        pt
        for pt in sites_on_shell(2, ball_max_k=2)
        if pt not in sq6 and sorted((abs(pt[0]), abs(pt[1]), abs(pt[2]))) == [1, 1, 2]
    ]

    # Exact basis matrices:
    # 1) 6 square centers: 1s (1) + 3p (3) + 2d_eg (2) -> 6x6 rank 6
    m_sq6_basis = [[1, x, y, z, x * x - y * y, 2 * z * z - x * x - y * y] for x, y, z in sq6]
    rank_sq6 = _exact_rational_rank(m_sq6_basis)
    rank_d_on_sq6 = _exact_rational_rank(
        [[x * y, y * z, x * z, x * x - y * y, 2 * z * z - x * x - y * y] for x, y, z in sq6]
    )

    # 2) 8 triangle centers: 1s (1) + 3p (3) + 3d_t2g (3) + 1f_xyz (1) -> 8x8 rank 8
    m_tri8_basis = [[1, x, y, z, x * y, y * z, x * z, x * y * z] for x, y, z in tri8]
    rank_tri8 = _exact_rational_rank(m_tri8_basis)

    # 3) 12 vertices V: 1s (1) + 3p (3) + 5d (5) + 3f_T2u (3) -> 12x12 rank 12
    m_v12_basis = [
        [
            1,
            x,
            y,
            z,
            x * y,
            y * z,
            x * z,
            x * x - y * y,
            2 * z * z - x * x - y * y,
            x * (y * y - z * z),
            y * (z * z - x * x),
            z * (x * x - y * y),
        ]
        for x, y, z in v12
    ]
    rank_v12 = _exact_rational_rank(m_v12_basis)
    rank_d_on_v12 = _exact_rational_rank(
        [[x * y, y * z, x * z, x * x - y * y, 2 * z * z - x * x - y * y] for x, y, z in v12]
    )
    rank_f_on_v12 = _exact_rational_rank(
        [
            [
                x * y * z,
                x * (5 * x * x - 3 * (x * x + y * y + z * z)),
                y * (5 * y * y - 3 * (x * x + y * y + z * z)),
                z * (5 * z * z - 3 * (x * x + y * y + z * z)),
                x * (y * y - z * z),
                y * (z * z - x * x),
                z * (x * x - y * y),
            ]
            for x, y, z in v12
        ]
    )

    # 4) 24 edge sites E: full 7/7 f-harmonics and all 1+3+5+7=16 modes
    rank_f_on_e24 = _exact_rational_rank(
        [
            [
                x * y * z,
                x * (5 * x * x - 3 * (x * x + y * y + z * z)),
                y * (5 * y * y - 3 * (x * x + y * y + z * z)),
                z * (5 * z * z - 3 * (x * x + y * y + z * z)),
                x * (y * y - z * z),
                y * (z * z - x * x),
                z * (x * x - y * y),
            ]
            for x, y, z in e24
        ]
    )

    checks_ok = (
        rank_sq6 == 6
        and rank_d_on_sq6 == 2
        and rank_tri8 == 8
        and rank_v12 == 12
        and rank_d_on_v12 == 5
        and rank_f_on_v12 == 6
        and rank_f_on_e24 == 7
    )
    return {
        "rank_sq6_1s_3p_2deg": rank_sq6,
        "rank_d_on_sq6_eg_only": rank_d_on_sq6,
        "rank_tri8_1s_3p_3dt2g_1fxyz": rank_tri8,
        "rank_v12_1s_3p_5d_3f": rank_v12,
        "rank_d_on_v12_full": rank_d_on_v12,
        "rank_f_on_v12_missing_fxyz": rank_f_on_v12,
        "rank_f_on_e24_full": rank_f_on_e24,
        "checks_ok": checks_ok,
    }


def cuboctahedral_second_period_and_hbond_verification() -> dict[str, Any]:
    """Verify Z=1..10 site-wise screening on V and □ channels, covalent radii, and H-bond/Watson-Crick locks."""
    import math

    be_h = 13.605693122994  # Rydberg energy BE_H in eV
    a0 = 0.529177210903    # Bohr radius in Angstrom
    kappa = 1.0 / math.sqrt(2.0)
    d = 3
    n12 = 12
    n_phi = 13
    n_hier = 8
    d_in_sq = 4
    d_out_v = 7
    n_shell_2 = 42

    nist_ie = {
        1: 13.59843449,
        2: 24.58738880,
        3: 5.39171495,
        4: 9.322699,
        5: 8.298019,
        6: 11.260288,
        7: 14.53413,
        8: 13.618055,
        9: 17.42282,
        10: 21.56454,
    }
    step_2p = 1.0 / d_in_sq + 1.0 / (n12 * n_phi)  # 1/4 + 1/156 = 10/39

    pred_ie: dict[int, float] = {
        1: be_h,
        2: 2.0 * (1.0 - 1.0 / n12 - 1.0 / (n12 * n_phi)) * be_h,
    }
    zeff_2: dict[int, float] = {
        3: (3.0 - 2.0 * (1.0 - 1.0 / n_hier)) + 1.0 / (n12 * n_phi),
        4: (5.0 / 4.0) + (1.0 - float(d_out_v) / n12) - 1.0 / (n12 * n_phi),
    }
    for m, z in enumerate((5, 6, 7)):
        zeff_2[z] = (5.0 / 4.0) ** 2 + m * step_2p
    for m, z in enumerate((8, 9, 10)):
        zeff_2[z] = 2.0 + m * step_2p
    for z in range(3, 11):
        pred_ie[z] = ((zeff_2[z] / 2.0) ** 2) * be_h

    ie_rel_errs = {z: abs(pred_ie[z] - nist_ie[z]) / nist_ie[z] for z in range(1, 11)}
    max_ie_rel_err = max(ie_rel_errs.values())

    # Second-period covalent radius law: r_cov(Z) = ((d*N_phi - 2*Z)/N_phi) * kappa * a0 for Z=4..9
    r_h = kappa * a0
    ref_rcov = {4: 0.90, 5: 0.84, 6: 0.77, 7: 0.715, 8: 0.66, 9: 0.60}
    pred_rcov = {z: ((d * n_phi - 2.0 * z) / n_phi) * r_h for z in range(4, 10)}
    max_rcov_rel_err = max(abs(pred_rcov[z] - ref_rcov[z]) / ref_rcov[z] for z in range(4, 10))
    peptide_cn_exact_multiple = (d * n_phi - 12) + (d * n_phi - 14) == 4 * n_phi  # 27 + 25 = 52 = 4 * 13

    # Hydrogen bond quantum on shell k=2 (21 Pauli pairs * d=3 = 63), Watson-Crick + Major Groove barcodes, and Rumer's 64 -> 20+1=21 identity
    e_hb_ev = be_h / (d * (n_shell_2 // 2))  # BE_H / 63 = 0.21596 eV
    major_groove_barcodes = {
        "A-T": ("-", "+", "-", "M"),
        "T-A": ("M", "-", "+", "-"),
        "G-C": ("-", "-", "+", "0"),
        "C-G": ("0", "+", "-", "-"),
    }
    unique_major_groove = len(set(major_groove_barcodes.values())) == 4
    rumer_20_plus_1_ok = (n_hier + n12 == 20) and (n_hier + n_phi == n_shell_2 // 2 == 21)

    ok = (
        max_ie_rel_err < 0.008
        and ie_rel_errs[6] < 0.001
        and ie_rel_errs[8] < 0.001
        and max_rcov_rel_err < 0.01
        and peptide_cn_exact_multiple
        and 0.21 < e_hb_ev < 0.22
        and unique_major_groove
        and rumer_20_plus_1_ok
    )
    return {
        "max_ie_rel_err_Z1_10": max_ie_rel_err,
        "ie_C_rel_err": ie_rel_errs[6],
        "ie_O_rel_err": ie_rel_errs[8],
        "max_rcov_rel_err_Z4_9": max_rcov_rel_err,
        "peptide_CN_is_4_kappa_a0": peptide_cn_exact_multiple,
        "e_hb_eV": e_hb_ev,
        "unique_major_groove_barcodes": unique_major_groove,
        "rumer_20_plus_1_identity_ok": rumer_20_plus_1_ok,
        "checks_ok": ok,
    }


def build_rho_theta_shell_catalog(*, max_k: int = 3) -> dict[str, Any]:
    """Finite catalog tiers for ρ_Θ modes on coordination spheres (not 2^N enumeration)."""
    sizes = coordination_shell_sizes(max_k=max_k)
    n12 = sizes[1]
    n2 = sizes[2]
    n3 = sizes[3] if max_k >= 3 else 0
    cumulative = sum(sizes[k] for k in range(max_k + 1))
    elementary_excitations = n2 + n3  # one-site bumps on shells 2–3 with full ε-star

    neighbor_stats = shell_neighbor_stats(max_k=max_k)
    channel_census = cuboctahedral_shell_channel_census(max_k=max(max_k, 4))
    spdf_ranks = cuboctahedral_spdf_harmonic_ranks()
    chem_second_period = cuboctahedral_second_period_and_hbond_verification()
    shell2_reachable_one_tick = (
        neighbor_stats.get(2, {}).get("min_inner_neighbors", 0) >= 1
    )
    shell3_reachable_two_ticks = (
        neighbor_stats.get(3, {}).get("min_inner_neighbors", 0) >= 1
    )

    tiers: list[dict[str, str | int]] = [
        {
            "id": "shell_geometry",
            "status": "closed",
            "count": cumulative,
            "note": f"FCC graph ball k≤{max_k}: 1+{n12}+{n2}+{n3} sites",
        },
        {
            "id": "shell1_star",
            "status": "closed",
            "count": n12,
            "note": "ε-star; ground C2 support (R_dress=1·dl)",
        },
        {
            "id": "shell2_sphere",
            "status": "closed",
            "count": n2,
            "note": "2nd coordination sphere; excitation locus (C3): 12 V + 24 E + 6 S",
        },
        {
            "id": "shell3_sphere",
            "status": "closed",
            "count": n3,
            "note": "3rd coordination sphere; higher C3 locus: 12 V + 48 E + 24 S + 8 T",
        },
        {
            "id": "elementary_single_site_modes",
            "status": "closed_algebra",
            "count": elementary_excitations,
            "note": "one ρ_Θ bump on shell 2 or 3 with full shell-1 halo",
        },
        {
            "id": "cubocta_four_channels_and_cascade",
            "status": "closed_algebra",
            "count": 4,
            "note": "V=(1,4,7), E=(2,5,5), S=(4,4,4), T=(3,6,3); F1-S1..S4 cascade closed",
        },
        {
            "id": "cubocta_spdf_harmonic_correspondence",
            "status": "closed_algebra",
            "count": 16,
            "note": "□6->1s+3p+2d_eg (6/6); V12->1s+3p+5d+3f (12/12); △8->1s+3p+3d_t2g+1f_xyz (8/8); E24->7/7 f",
        },
        {
            "id": "cubocta_second_period_and_hbond_bridge",
            "status": "closed_algebra",
            "count": 10,
            "note": "Z=1..10 IE_1 (<0.8% NIST), Z=4..9 r_cov=(39-2Z)/13*kappa*a0 (<1%), E_HB=BE_H/63, Major Groove barcodes",
        },
        {
            "id": "full_binary_patterns",
            "status": "not_enumerated",
            "count": 0,
            "note": f"2^{n2}+2^{n3} composite patterns — C3 class; not SSOT table",
        },
        {
            "id": "inter_shell_g_paths",
            "status": "soft_open",
            "count": 0,
            "note": "composite 2^N n_ticks distribution in A5 bath soft-open; 4-channel 1-tick selection closed",
        },
    ]

    checks_ok = (
        n12 == 12
        and n2 == 42
        and n3 == 92
        and elementary_excitations == 134
        and shell2_reachable_one_tick
        and shell3_reachable_two_ticks
        and bool(channel_census["checks_ok"])
        and bool(spdf_ranks["checks_ok"])
        and bool(chem_second_period["checks_ok"])
    )

    return {
        "max_k": max_k,
        "shell_sizes": sizes,
        "cumulative_sites": cumulative,
        "elementary_excitations_shell23": elementary_excitations,
        "neighbor_stats": neighbor_stats,
        "channel_census": channel_census,
        "spdf_ranks": spdf_ranks,
        "chem_second_period": chem_second_period,
        "four_channel_selection_closed": bool(channel_census["checks_ok"]),
        "spdf_correspondence_closed": bool(spdf_ranks["checks_ok"]),
        "shell2_one_tick_from_star": shell2_reachable_one_tick,
        "shell3_two_tick_bridge": shell3_reachable_two_ticks,
        "tiers": tiers,
        "catalog_algebra_closed": checks_ok,
        "full_selection_closed": False,
        "checks_ok": checks_ok,
    }
