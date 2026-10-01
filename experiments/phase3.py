"""Phase 3 (README §11): baselines on the Phase 2 cells of design D1, and on design D2.

    python experiments/phase3.py                   # everything, one process
    python experiments/phase3.py --shard 0 --of 2  # or split across processes
    python experiments/phase3_report.py            # tables -> experiments/phase3/summary.md

On D1, symbolic IV and plain PySR come from Phase 2 (same seeds, hence the same
data); on D2 they are run here. Each finished run is appended to
experiments/phase3/runs-<shard>.jsonl (one file per process, so parallel shards never
share a file); rerunning skips runs finished in any of them.
"""

from __future__ import annotations

import argparse
import json
import time
import traceback
import warnings
from pathlib import Path

import numpy as np

from symiv.baselines import fit_kiv, fit_library_iv, fit_sieve_iv, fixed_form_iv, oracle_iv, wrong_forms
from symiv.criteria import gmm_criterion
from symiv.diagnostics import diagnose
from symiv.dgp import simulate
from symiv.metrics import elasticity, extrapolation_error, extrapolation_grid, implied_constants, relative_error
from symiv.recovery import form_recovered
from symiv.selection import select_ls, select_mmsc

OUT_DIR = Path(__file__).parent / "phase3"  # one runs-<shard>.jsonl per process
N = 2000
CELLS = {  # (design, setting): design parameters
    ("D1", "default"): dict(pi=1.0, rho=0.8),
    ("D1", "strong"): dict(pi=0.7, rho=1.2),
    ("D2", "default"): dict(),  # pi = 1, rho = 0.8, gamma = 0.3
}
SEEDS, DEEP_SEEDS = 50, 20  # DeepIV only on the first 20 seeds (training cost)
SEARCH = dict(niterations=40, maxsize=15, temp_equation_file=True)  # as in Phase 2


def units():
    for design, setting in CELLS:
        for law in ("power", "log"):
            for seed in range(SEEDS):
                yield dict(design=design, setting=setting, law=law, seed=seed)


def key(u: dict) -> tuple:
    return (u["design"], u["setting"], u["law"], u["seed"])


def describe_formula(expr, law, X) -> dict:
    rec = form_recovered(expr, law, X)
    return dict(
        kind="formula",
        expr=str(expr),
        p=rec.n_constants,
        recovered=rec.recovered,
        rel_error=relative_error(expr, law, X),
        extrap_error=extrapolation_error(expr, law, X),
        elasticity=elasticity(expr, float(np.median(X[:, 0]))),
        implied=implied_constants(expr, law, X).tolist(),
    )


def describe_curve(f_hat, law, X) -> dict:
    """The same accuracy measures for a black-box estimate."""
    sd = law(X).std()
    G = extrapolation_grid(X)
    x = float(np.median(X[:, 0]))
    lo, mid, hi = f_hat(np.array([[x * (1 - 1e-4)], [x], [x * (1 + 1e-4)]]))
    return dict(
        kind="curve",
        rel_error=float(np.sqrt(np.mean((f_hat(X) - law(X)) ** 2)) / sd),
        extrap_error=float(np.sqrt(np.mean((f_hat(G) - law(G)) ** 2)) / sd),
        elasticity=float((hi - lo) / (2e-4 * mid)),
    )


def run(u: dict, deep_threads: int) -> dict:
    from symiv.baselines.control_function import fit_control_function_sr
    from symiv.baselines.distill import distill
    from symiv.baselines.srit import fit_srit_style
    from symiv.search import fit_symbolic_iv, pareto_front, plain_regressor

    s = simulate(u["design"], u["law"], n=N, seed=u["seed"], **CELLS[(u["design"], u["setting"])])
    crit = gmm_criterion(s.Z)
    law, X, y = s.law, s.X, s.y
    out = dict(u, n=N, K_used=crit.K, params=s.params, methods={}, errors={})
    methods = out["methods"]

    def attempt(name, fn):
        t = time.time()
        try:
            rec = fn()
            if rec is not None:
                methods[name] = dict(rec, time=time.time() - t)
        except Exception:
            out["errors"][name] = traceback.format_exc()

    attempt("oracle_iv", lambda: describe_formula(oracle_iv(law, X, y, crit).fitted_expr, law, X))
    for name, form in wrong_forms(law).items():
        attempt(f"wrong_{name}_iv", lambda form=form: describe_formula(fixed_form_iv(form, X, y, crit).fitted_expr, law, X))

    def library():
        fit = fit_library_iv(X, y, crit)
        return dict(describe_formula(fit.candidate.fitted_expr, law, X), terms=fit.terms)

    attempt("library_iv", library)

    npiv = {}

    def curve(name, fit_fn):
        def go():
            npiv[name] = fit_fn()
            return describe_curve(npiv[name], law, X)

        attempt(name, go)

    curve("sieve_iv", lambda: fit_sieve_iv(X, y, crit))
    curve("kiv", lambda: fit_kiv(X, y, s.Z, seed=u["seed"]))
    if u["seed"] < DEEP_SEEDS:
        from symiv.baselines.deepiv import fit_deepiv

        curve("deepiv", lambda: fit_deepiv(X, y, s.Z, seed=u["seed"], threads=deep_threads))

    for name, f_hat in npiv.items():
        holder = {}

        def run_distill(f_hat=f_hat):
            holder["d"] = distill(f_hat, X, y, crit, **SEARCH)
            return describe_formula(holder["d"].pick, law, X)

        attempt(f"distill_{name}_pick", run_distill)
        if "d" in holder:
            attempt(f"distill_{name}_mmsc", lambda: describe_formula(holder["d"].by_mmsc.best.fitted_expr, law, X))

    def control_function():
        fit = fit_control_function_sr(X, y, crit, **SEARCH)
        return dict(describe_formula(fit.f_expr, law, X), g=str(fit.g_expr))

    attempt("control_function_sr", control_function)

    def srit():
        fit = fit_srit_style(X, s.Z, y, seed=u["seed"], **SEARCH)
        return dict(describe_formula(fit.structural_expr, law, X), retained=fit.retained, full_expr=str(fit.expr))

    attempt("srit_style", srit)

    if u["design"] != "D1":  # D1 has these from Phase 2
        def plain():
            t = time.time()
            model = plain_regressor(**SEARCH)
            model.fit(X, y)
            exprs, cx = pareto_front(model)
            bic = describe_formula(select_ls(exprs, X, y, cx).best.fitted_expr, law, X)
            methods["plain_bic"] = dict(bic, time=time.time() - t)  # same search as PySR's pick
            return describe_formula(model.sympy(), law, X)

        def symbolic_iv():
            model = fit_symbolic_iv(X, y, crit, **SEARCH)
            exprs, cx = pareto_front(model)
            sel = select_mmsc(exprs, X, y, crit, complexities=cx)
            d = diagnose(sel.best, law, X, y, crit)
            return dict(describe_formula(sel.best.fitted_expr, law, X), outcome=d.outcome)

        attempt("plain_pick", plain)
        attempt("symbolic_iv_bic", symbolic_iv)
    return out


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--shard", type=int, default=0)
    parser.add_argument("--of", type=int, default=1)
    parser.add_argument("--deep-threads", type=int, default=4)
    parser.add_argument("--limit", type=int, default=None, help="stop after this many runs (for timing)")
    args = parser.parse_args()
    warnings.filterwarnings("ignore")

    OUT_DIR.mkdir(parents=True, exist_ok=True)
    done = {key(json.loads(line)) for f in OUT_DIR.glob("runs-*.jsonl") for line in f.read_text().splitlines() if line.strip()}
    out_file = OUT_DIR / f"runs-{args.shard}.jsonl"
    todo = [u for i, u in enumerate(units()) if i % args.of == args.shard and key(u) not in done][: args.limit]
    print(f"shard {args.shard}/{args.of}: {len(todo)} runs to do", flush=True)

    for i, u in enumerate(todo, 1):
        t = time.time()
        rec = run(u, args.deep_threads)
        with out_file.open("a") as f:
            f.write(json.dumps(rec) + "\n")
        errs = f" errors: {sorted(rec['errors'])}" if rec["errors"] else ""
        print(f"[{i}/{len(todo)}] {u['design']} {u['setting']:7s} {u['law']:5s} seed={u['seed']:2d} {time.time() - t:5.0f}s  "
              + " ".join(f"{k}={v['time']:.0f}s" for k, v in rec["methods"].items() if v.get("time", 0) >= 2) + errs, flush=True)


if __name__ == "__main__":
    main()
