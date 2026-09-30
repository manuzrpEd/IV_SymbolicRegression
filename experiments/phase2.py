"""Phase 2 Monte Carlo (README §11): plain PySR vs. symbolic IV on design D1.

    python experiments/phase2.py --part main          # power and log laws x 2 settings x 50 seeds
    python experiments/phase2.py --part sensitivity   # K and C, power law, strong setting, 20 seeds
    python experiments/phase2_report.py               # tables -> experiments/phase2/summary.md

Each finished run is appended to experiments/phase2/runs.jsonl; rerunning skips
runs already there (and retries runs that errored), so an interrupted job can be restarted.
"""

from __future__ import annotations

import argparse
import json
import time
import traceback
import warnings
from pathlib import Path

import numpy as np
from scipy.optimize import least_squares

from symiv.criteria import gmm_criterion
from symiv.diagnostics import diagnose
from symiv.dgp import Law, simulate
from symiv.gmm import fit_gmm
from symiv.metrics import elasticity, extrapolation_error, implied_constants, relative_error
from symiv.recovery import form_recovered
from symiv.selection import PENALTIES, rerank, select_ls, select_mmsc

OUT = Path(__file__).parent / "phase2" / "runs.jsonl"
N = 2000
SETTINGS = {
    "default": dict(pi=1.0, rho=0.8),  # E[y|X] - f0 = 0.40 log X
    "strong": dict(pi=0.7, rho=1.2),  # E[y|X] - f0 = 0.81 log X, weaker first stage
}
SEARCH = dict(niterations=40, maxsize=15, temp_equation_file=True)


def units(part: str, n_seeds: int):
    if part == "main":
        for law in ("power", "log"):
            for setting in SETTINGS:
                for seed in range(n_seeds):
                    yield dict(part=part, law=law, setting=setting, seed=seed, K=None, C=10.0)
    elif part == "sensitivity":
        for K, C in [(8, 10.0), (25, 10.0), (None, 3.0), (None, 100.0)]:
            for seed in range(n_seeds):
                yield dict(part=part, law="power", setting="strong", seed=seed, K=K, C=C)
    else:
        raise ValueError(part)


def key(u: dict) -> tuple:
    return (u["part"], u["law"], u["setting"], u["seed"], u["K"], u["C"])


def describe(expr, law: Law, X: np.ndarray) -> dict:
    """Accuracy of one formula against the truth."""
    rec = form_recovered(expr, law, X)
    return dict(
        expr=str(expr),
        p=rec.n_constants,
        recovered=rec.recovered,
        rel_error=relative_error(expr, law, X),
        extrap_error=extrapolation_error(expr, law, X),
        elasticity=elasticity(expr, float(np.median(X[:, 0]))),
        implied=implied_constants(expr, law, X).tolist(),
    )


def run(u: dict) -> dict:
    from symiv.search import fit_symbolic_iv, pareto_front, plain_regressor

    s = simulate("D1", u["law"], n=N, seed=u["seed"], **SETTINGS[u["setting"]])
    crit = gmm_criterion(s.Z, K=u["K"])
    out = dict(u, n=N, K_used=crit.K, **SETTINGS[u["setting"]], elasticity_true=describe(s.law.expr, s.law, s.X)["elasticity"])

    if u["part"] == "main":
        t = time.time()
        plain = plain_regressor(**SEARCH)
        plain.fit(s.X, s.y)
        exprs, cx = pareto_front(plain)
        out["time_plain"] = time.time() - t
        out["plain"] = {"pysr_pick": describe(plain.sympy(), s.law, s.X)}
        for pen in PENALTIES:
            out["plain"][pen] = describe(select_ls(exprs, s.X, s.y, cx, penalty=pen).best.fitted_expr, s.law, s.X)

        form = s.law.parametric
        oracle_iv = fit_gmm(form, s.X, s.y, crit, bound=u["C"], theta0=np.array(s.law.values))
        oracle_ls = least_squares(lambda t: s.y - form(s.X, t), np.array(s.law.values)).x  # smooth true form: safe
        out["oracle_iv"] = describe(form.expr(oracle_iv.theta), s.law, s.X)
        out["oracle_ls"] = describe(form.expr(oracle_ls), s.law, s.X)

    t = time.time()
    model = fit_symbolic_iv(s.X, s.y, crit, bound=u["C"], **SEARCH)
    exprs, cx = pareto_front(model)
    out["time_iv"] = time.time() - t
    out["front_size"] = len(exprs)
    by_bic = select_mmsc(exprs, s.X, s.y, crit, complexities=cx, bound=u["C"])
    out["iv"] = {}
    for pen in PENALTIES:
        sel = by_bic if pen == "bic" else rerank(by_bic, N, pen)
        d = diagnose(sel.best, s.law, s.X, s.y, crit, penalty=pen, bound=u["C"])
        out["iv"][pen] = dict(
            describe(sel.best.fitted_expr, s.law, s.X),
            outcome=d.outcome,
            mmsc=d.mmsc_selected,
            mmsc_true=d.mmsc_true,
            gap=(sel.candidates[1].mmsc - sel.best.mmsc) if len(sel.candidates) > 1 else None,
        )
    return out


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--part", choices=["main", "sensitivity"], default="main")
    parser.add_argument("--seeds", type=int, default=None, help="default: 50 (main), 20 (sensitivity)")
    args = parser.parse_args()
    n_seeds = args.seeds or (50 if args.part == "main" else 20)
    warnings.filterwarnings("ignore")

    OUT.parent.mkdir(parents=True, exist_ok=True)
    done = set()
    if OUT.exists():
        records = [json.loads(line) for line in OUT.read_text().splitlines() if line.strip()]
        done = {key(r) for r in records if "error" not in r}
    todo = [u for u in units(args.part, n_seeds) if key(u) not in done]
    print(f"{args.part}: {len(todo)} runs to do ({len(done)} lines already in {OUT.name})", flush=True)

    for i, u in enumerate(todo, 1):
        t = time.time()
        try:
            rec = run(u)
            status = f"IV/bic {rec['iv']['bic']['outcome']:<19s} {rec['iv']['bic']['expr'][:60]}"
        except Exception:
            rec = dict(u, error=traceback.format_exc())
            status = "ERROR " + rec["error"].strip().splitlines()[-1]
        with OUT.open("a") as f:
            f.write(json.dumps(rec) + "\n")
        print(f"[{i}/{len(todo)}] {u['law']:5s} {u['setting']:7s} K={u['K']} C={u['C']} seed={u['seed']:2d} "
              f"{time.time() - t:5.0f}s  {status}", flush=True)


if __name__ == "__main__":
    main()
