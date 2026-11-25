#!/usr/bin/env python3
"""Verify M-layer axioms after first-principles rebuild.

Check bodies: verify_checks/*.py · grouping: verify_checks/suites.py (SSOT).
"""

import os
import subprocess
import sys

if sys.version_info[0] < 3:
    os.execvp("python3", ["python3", os.path.abspath(__file__)] + sys.argv[1:])

import argparse
import json
from pathlib import Path

_REPO = Path(__file__).resolve().parent

try:
    import torch
except ImportError:
    if os.environ.get("DQM_VENV_BOOTSTRAPPED") != "1":
        venv_dir = _REPO / ".venv"
        venv_py = (
            venv_dir / "Scripts" / "python.exe"
            if os.name == "nt"
            else venv_dir / "bin" / "python3"
        )
        req_file = _REPO / "requirements.txt"
        if not venv_py.is_file():
            print("[dqm] Creating virtual environment in {} ...".format(venv_dir), file=sys.stderr)
            subprocess.check_call([sys.executable, "-m", "venv", str(venv_dir)])
        if subprocess.call([str(venv_py), "-c", "import torch"], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL) != 0:
            print("[dqm] Installing dependencies from {} into .venv ...".format(req_file.name), file=sys.stderr)
            subprocess.check_call([str(venv_py), "-m", "pip", "install", "--upgrade", "pip"])
            subprocess.check_call([str(venv_py), "-m", "pip", "install", "-r", str(req_file)])
        env = os.environ.copy()
        env["DQM_VENV_BOOTSTRAPPED"] = "1"
        raise SystemExit(subprocess.call([str(venv_py), os.path.abspath(__file__)] + sys.argv[1:], env=env))
    raise

from mt_ca.app.scenario import get_scenario
from mt_ca.app.scenario_verify import (
    list_scenarios_with_verify,
    verify_suite_ids_for_scenarios,
)
from verify_checks.suites import (
    SHIP_SUITE_IDS,
    SUITE_ORDER,
    VERIFY_SUITES,
    failed_rows,
    get_suite,
    order_suite_ids,
    run_suites,
)


def cmd_list(_):
    print("{:<22}  {:<4}  description".format("suite", "ship"))
    print("-" * 88)
    for sid in SUITE_ORDER:
        spec = VERIFY_SUITES[sid]
        ship = "yes" if spec.ship else "no"
        print("{:<22}  {:<4}  {}".format(sid, ship, spec.description))
    print("\nScenarios (same ids as `python3 -m mt_ca.app.cli run <id>`):")
    print("{:<26}  verify_suites".format("scenario"))
    print("-" * 88)
    for spec in list_scenarios_with_verify():
        suites = ",".join(spec.verify_suites)
        print("{:<26}  {}".format(spec.id, suites))
    print("\nRun: python3 verify_principles.py --scenario floor0_planckon")
    print("     python3 verify_principles.py [--ship | --suite t_macro ...]")
    return 0


def _print_results(device, rows, by_suite=False):
    print("device={}".format(device))
    print("-" * 60)
    if not by_suite:
        for row in rows:
            _print_row(row)
        return

    current = None
    for row in rows:
        sid = row.get("suite", "?")
        if sid != current:
            current = sid
            spec = VERIFY_SUITES.get(sid)
            desc = spec.description if spec else ""
            print("\n=== {} ===  {}".format(sid, desc))
        _print_row(row)


def _print_row(row):
    status = "PASS" if row["ok"] else "FAIL"
    payload = {k: v for k, v in row.items() if k not in ("id", "ok", "suite")}
    print("{:<22}  {}  {}".format(row["id"], status, payload))


def main():
    has_cuda = bool(torch is not None and torch.cuda.is_available())
    parser = argparse.ArgumentParser(description="First-principles verification (suites)")
    parser.add_argument("--device", default="cuda" if has_cuda else "cpu")
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--list", action="store_true", help="List verify suites (like sim scenario list).")
    parser.add_argument(
        "--ship",
        action="store_true",
        help="Ship profile: {} (excludes m_evolution_open, cosmology).".format(", ".join(SHIP_SUITE_IDS)),
    )
    parser.add_argument(
        "--suite",
        action="append",
        dest="suites",
        metavar="ID",
        help="Run one suite; repeat for several. Default: all suites in SSOT order.",
    )
    parser.add_argument(
        "--scenario",
        action="append",
        dest="scenarios",
        metavar="ID",
        help="Run verify profile for sim scenario (SSOT: mt_ca.app.scenario.SCENARIOS).",
    )
    args = parser.parse_args()

    if args.list:
        return cmd_list(args)

    if args.ship and (args.suites or args.scenarios):
        parser.error("--ship cannot be combined with --suite or --scenario")

    scenario_ids = []
    if args.scenarios:
        for raw in args.scenarios:
            for part in raw.split(","):
                part = part.strip()
                if part:
                    get_scenario(part)
                    scenario_ids.append(part)

    if args.ship:
        suite_ids = list(SHIP_SUITE_IDS)
    elif scenario_ids:
        suite_ids = list(order_suite_ids(verify_suite_ids_for_scenarios(scenario_ids)))
        if args.suites:
            extra = []
            for raw in args.suites:
                for part in raw.split(","):
                    part = part.strip()
                    if part:
                        get_suite(part)
                        extra.append(part)
            suite_ids = list(order_suite_ids(list(suite_ids) + extra))
    elif args.suites:
        suite_ids = []
        for raw in args.suites:
            for part in raw.split(","):
                part = part.strip()
                if part:
                    get_suite(part)
                    suite_ids.append(part)
        suite_ids = list(order_suite_ids(suite_ids))
    else:
        suite_ids = list(SUITE_ORDER)

    if args.device == "cuda" and (torch is None or not torch.cuda.is_available()):
        args.device = "cpu"

    rows = run_suites(args.device, suite_ids)
    failed = failed_rows(rows)

    if args.json:
        print(
            json.dumps(
                {
                    "device": args.device,
                    "scenarios": scenario_ids or None,
                    "suites": suite_ids,
                    "failed_count": len(failed),
                    "results": rows,
                },
                indent=2,
                default=float,
            )
        )
    else:
        _print_results(args.device, rows, by_suite=True)
        print("-" * 60)
        if scenario_ids:
            print(f"scenarios={','.join(scenario_ids)}")
        print(f"suites={len(suite_ids)}  checks={len(rows)}  failed={len(failed)}")
        if failed:
            print("failed:", ", ".join(r["id"] for r in failed))

    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
