"""Phase 4 (README §11), part 1: candidate generation. Every Pareto front is saved.

    python experiments/phase4.py --grid breadth --shard 0 --of 3   # also: nscale, nomax, cf
    python experiments/phase4_analysis.py                          # selection rules and metrics (pure Python)
    python experiments/phase4_report.py                            # tables and figures

Generators (each gives a set of candidate formulas):
- plain:   PySR with squared-error loss on (X, y)
- onestep: PySR with the moment-criterion loss (symbolic IV's search)
- distill: sieve 2SLS curve, then PySR on (X, curve) at up to 5000 points (the curve is noise-free)
- cf:      control-function SR (grid "cf" only; a baseline, its own selection)

Grids:
- breadth: 5 laws x designs D1-D5 (no D3 for the two-regressor law), n = 2000, 12 seeds
- nscale:  power and log laws, D1 strong setting, n = 1000 ... 50000, 12 seeds; one-step up to 5000, plain up to 10000
- nomax:   D1 default and strong, power and log laws, operators without `max`, 12 seeds
- cf:      D2 with gamma = 0.45 and 0.6, power and log laws, 12 seeds

Each finished run is appended to experiments/phase4/runs-<grid>-<shard>.jsonl; rerunning skips finished runs.
"""

from __future__ import annotations

import argparse
import json
import time
import traceback
import warnings
from pathlib import Path

import numpy as np

from symiv.baselines import fit_sieve_iv
from symiv.criteria import gmm_criterion
from symiv.dgp import simulate
from symiv.metrics import extrapolation_grid

OUT_DIR = Path(__file__).parent / "phase4"
SEARCH = dict(niterations=40, maxsize=15, temp_equation_file=True)  # as in Phases 2-3
NOMAX_OPS = ["+", "-", "*", "/", "^"]
DISTILL_POINTS = 5000
SEEDS = 12  # 20 planned; cut for compute (PySR already uses all cores, so sharding does not add throughput)
STRONG = dict(pi=0.7, rho=1.2)


def default_criterion(s):
    """Spline instruments (K ~ n^(1/3)) for one regressor; polynomial degree 4 for several (interactions)."""
    return gmm_criterion(s.Z) if s.X.shape[1] == 1 else gmm_criterion(s.Z, basis="poly", degree=4)


def units(grid: str):
    def unit(design, law, n, seed, setting="default", params=None, ops="default", gens=("plain", "onestep", "distill")):
        return dict(grid=grid, design=design, law=law, n=n, seed=seed, setting=setting,
                    params=params or {}, ops=ops, gens=list(gens))

    if grid == "breadth":
        for design in ("D1", "D2", "D3", "D4", "D5"):
            for law in ("log", "power", "kink", "saturation", "cobb_douglas"):
                if design == "D3" and law == "cobb_douglas":
                    continue
                for seed in range(SEEDS):
                    yield unit(design, law, 2000, seed)
    elif grid == "nscale":
        for law in ("power", "log"):
            for n in (1000, 2000, 5000, 10000, 20000, 50000):
                gens = ["distill"] + (["onestep"] if n <= 5000 else []) + (["plain"] if n <= 10000 else [])
                for seed in range(SEEDS):
                    yield unit("D1", law, n, seed, "strong", STRONG, gens=gens)
    elif grid == "nomax":
        for setting, params in (("default", {}), ("strong", STRONG)):
            for law in ("power", "log"):
                for seed in range(SEEDS):
                    yield unit("D1", law, 2000, seed, setting, params, ops="nomax", gens=("onestep", "distill"))
    elif grid == "cf":
        for gamma in (0.45, 0.6):
            for law in ("power", "log"):
                for seed in range(SEEDS):
                    yield unit("D2", law, 2000, seed, f"gamma{gamma}", {"gamma": gamma}, gens=("distill", "cf"))
    else:
        raise ValueError(grid)


def key(u: dict) -> tuple:
    return (u["grid"], u["design"], u["law"], u["n"], u["seed"], u["setting"], u["ops"])


def front(model) -> dict:
    from symiv.search import pareto_front

    exprs, cx = pareto_front(model)
    return dict(exprs=[str(e) for e in exprs], complexity=cx, pick=str(model.sympy()))


def run(u: dict) -> dict:
    from symiv.search import fit_symbolic_iv, plain_regressor

    s = simulate(u["design"], u["law"], n=u["n"], seed=u["seed"], **u["params"])
    crit = default_criterion(s)
    X, y = s.X, s.y
    search = dict(SEARCH, **({"binary_operators": NOMAX_OPS} if u["ops"] == "nomax" else {}))
    out = dict(u, K=crit.K, fronts={}, times={}, errors={})

    def attempt(name, fn):
        t = time.time()
        try:
            fn()
        except Exception:
            out["errors"][name] = traceback.format_exc()
        out["times"][name] = time.time() - t

    if "plain" in u["gens"]:
        def plain():
            model = plain_regressor(**search)
            model.fit(X, y)
            out["fronts"]["plain"] = front(model)

        attempt("plain", plain)

    if "onestep" in u["gens"]:
        attempt("onestep", lambda: out["fronts"].__setitem__("onestep", front(fit_symbolic_iv(X, y, crit, **search))))

    if "distill" in u["gens"]:
        def distill():
            curve = fit_sieve_iv(X, y, crit)
            sd, G = s.f0.std(), extrapolation_grid(X)
            out["sieve"] = dict(J=curve.J, rel_error=float(np.sqrt(np.mean((curve(X) - s.f0) ** 2)) / sd),
                                extrap_error=float(np.sqrt(np.mean((curve(G) - s.law(G)) ** 2)) / sd))
            idx = np.random.default_rng(u["seed"]).choice(len(y), size=min(len(y), DISTILL_POINTS), replace=False)
            model = plain_regressor(**search)
            model.fit(X[idx], curve(X[idx]))
            out["fronts"]["distill"] = front(model)

        attempt("distill", distill)

    if "cf" in u["gens"]:
        def cf():
            from symiv.baselines.control_function import fit_control_function_sr

            out["cf"] = dict(expr=str(fit_control_function_sr(X, y, crit, **search).f_expr))

        attempt("cf", cf)
    return out


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--grid", required=True, nargs="+", choices=["breadth", "nscale", "nomax", "cf"],
                        help="one or more grids, run in order in this process")
    parser.add_argument("--shard", type=int, default=0)
    parser.add_argument("--of", type=int, default=1)
    parser.add_argument("--limit", type=int, default=None)
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR)
    args = parser.parse_args()
    warnings.filterwarnings("ignore")
    args.out_dir.mkdir(parents=True, exist_ok=True)

    for grid in args.grid:
        done = {key(json.loads(line)) for f in args.out_dir.glob("runs-*.jsonl") for line in f.read_text().splitlines() if line.strip()}
        out_file = args.out_dir / f"runs-{grid}-{args.shard}.jsonl"
        todo = [u for i, u in enumerate(units(grid)) if i % args.of == args.shard and key(u) not in done][: args.limit]
        print(f"{grid} shard {args.shard}/{args.of}: {len(todo)} runs to do", flush=True)

        for i, u in enumerate(todo, 1):
            t = time.time()
            rec = run(u)
            with out_file.open("a") as f:
                f.write(json.dumps(rec) + "\n")
            errs = f" errors: {sorted(rec['errors'])}" if rec["errors"] else ""
            sizes = " ".join(f"{g}={len(fr['exprs'])}" for g, fr in rec["fronts"].items())
            print(f"[{i}/{len(todo)}] {u['design']} {u['setting']:9s} {u['law']:12s} n={u['n']:<6d} seed={u['seed']:2d} ops={u['ops']:7s} "
                  f"{time.time() - t:5.0f}s  fronts: {sizes}{errs}", flush=True)
    print("all grids done", flush=True)


if __name__ == "__main__":
    main()
