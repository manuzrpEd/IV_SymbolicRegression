"""Phase 5, simulation of Theorem 1 (iii): inference after selection on an independent sample.

    python experiments/phase5_inference.py --workers 8     -> experiments/phase5/inference.jsonl

For every Phase 4 breadth run (n = 2000, 12 seeds, five laws, D1-D5), two trees:
- oracle:   the law's own form (inference without selection; the law's constants are the truth);
- selected: the formula chosen on the Phase 4 sample A from the pooled candidates by BIC + structure,
            when it has the true form. Its truth is the constants that reproduce f0 (refit, noise-free).
Each tree is estimated by two-step efficient GMM on R fresh samples B (independent of A; same n and
design) and, for comparison, on A itself (same-sample inference after selection). Recorded per fit:
Wald 95% intervals for every constant and, by the delta method, for f(x) at the median and the 90th
percentile of X and for the elasticity at the median; Hansen's J test at 5%; the Anderson-Rubin
statistic at the true constants against the chi^2_K critical value (no rank condition needed).
"""

from __future__ import annotations

import os

for _v in ("OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "OMP_NUM_THREADS"):
    os.environ.setdefault(_v, "1")

import argparse  # noqa: E402
import json  # noqa: E402
import sys  # noqa: E402
import traceback  # noqa: E402
import warnings  # noqa: E402
from concurrent.futures import ProcessPoolExecutor, as_completed  # noqa: E402
from pathlib import Path  # noqa: E402

import numpy as np  # noqa: E402
from scipy.stats import chi2  # noqa: E402

sys.path.insert(0, str(Path(__file__).parent))
from phase4 import default_criterion  # noqa: E402

from symiv._lsq import robust_least_squares  # noqa: E402
from symiv.dgp import simulate  # noqa: E402
from symiv.expressions import ParametricForm, parametrize  # noqa: E402
from symiv.gmm import efficient_weight_sqrt, fit_gmm, hansen_j  # noqa: E402

OUT_DIR = Path(__file__).parent / "phase5"
P4 = Path(__file__).parent / "phase4"
R = 10  # fresh samples per Phase 4 run
SET, RULE = "pooled", "bic_s05"  # the selection whose pick is examined
Z95 = 1.959964


def true_constants(form: ParametricForm, X, f0, seed=0, n_starts=8):
    """Constants of `form` that reproduce the noise-free f0 on X (relative error < 1e-4), or None.

    Also reports whether every start that reaches f0 ends at the same point: a point zero set, (A5)(a).
    """
    scale = f0.std()

    def res(theta):
        r = (form(X, theta) - f0) / scale
        return np.where(np.isfinite(r), r, 1e6)

    rng = np.random.default_rng(seed)
    p = form.n_constants
    starts = [form.values] + [form.values * (1 + 0.5 * rng.standard_normal(p)) + 0.5 * rng.standard_normal(p)
                              for _ in range(n_starts - 1)]
    fits = [f for f in (robust_least_squares(res, s) for s in starts) if f is not None]
    good = [f for f in fits if np.sqrt(np.mean(f.fun**2)) < 1e-4]
    if not good:
        return None, False
    best = min(good, key=lambda f: f.cost)
    unique = all(np.max(np.abs(f.x - best.x)) < 1e-3 * (1 + np.max(np.abs(best.x))) for f in good)
    return best.x, unique


def _grad(fun, theta, rel=1e-6):
    g = np.empty(len(theta))
    for j in range(len(theta)):
        h = rel * max(1.0, abs(theta[j]))
        e = np.zeros(len(theta))
        e[j] = h
        g[j] = (fun(theta + e) - fun(theta - e)) / (2 * h)
    return g


def _jacobian(form, X, theta, rel=1e-6):
    D = np.empty((len(X), len(theta)))
    for j in range(len(theta)):
        h = rel * max(1.0, abs(theta[j]))
        e = np.zeros(len(theta))
        e[j] = h
        D[:, j] = (form(X, theta + e) - form(X, theta - e)) / (2 * h)
    return D


def _elasticity(form, x, theta, h=1e-4):
    lo, mid, hi = form(np.array([[x * (1 - h)], [x], [x * (1 + h)]]), theta)
    return float((hi - lo) / (2 * h * mid))


def inference(form: ParametricForm, s, theta0, theta_start) -> dict | None:
    """Two-step efficient GMM of `form` on sample s, with the instruments of the Phase 4 selection.

    Instruments a_i = sqrt(n) A_i (A'A = I), g = mean a_i r_i, Omega = mean a_i a_i' r_i^2,
    G = mean a_i df_i', V = (G' Omega^{-1} G)^{-1} / n.
    """
    X, y, n = s.X, s.y, s.n
    crit = default_criterion(s)
    fit = fit_gmm(form, X, y, crit, theta0=theta_start, n_starts=4)
    th = fit.theta
    r = y - form(X, th)
    if not np.all(np.isfinite(r)) or not np.isfinite(fit.J):
        return None
    A = crit.A
    Omega = (A * r[:, None] ** 2).T @ A
    G = A.T @ _jacobian(form, X, th) / np.sqrt(n)
    V = np.linalg.pinv(G.T @ np.linalg.pinv(Omega) @ G) / n
    se = np.sqrt(np.clip(np.diag(V), 0.0, None))
    d = X.shape[1]
    xq = {q: np.quantile(X, q, axis=0) for q in (0.5, 0.9)}
    funs = {"f_med": lambda t: float(form(xq[0.5][None, :], t)[0]), "f_q90": lambda t: float(form(xq[0.9][None, :], t)[0])}
    if d == 1:
        funs["elas_med"] = lambda t: _elasticity(form, float(xq[0.5][0]), t)
    targets = {}
    for name, fun in funs.items():
        g = _grad(fun, th)
        sd = float(np.sqrt(max(g @ V @ g, 0.0)))
        est, truth = fun(th), fun(theta0)
        targets[name] = dict(est=est, truth=truth, se=sd, cover=bool(abs(est - truth) <= Z95 * sd))
    df = crit.K - form.n_constants
    r0 = y - form(X, theta0)
    AR = hansen_j(crit, r0, efficient_weight_sqrt(crit, r0)) if np.all(np.isfinite(r0)) else np.inf
    return dict(theta=th.tolist(), se=se.tolist(), cover=(np.abs(th - theta0) <= Z95 * se).tolist(),
                J=fit.J, df=df, J_reject=bool(fit.J > chi2.ppf(0.95, df)) if df > 0 else None,
                AR=float(AR), AR_cover=bool(AR <= chi2.ppf(0.95, crit.K)), K=crit.K, targets=targets)


def work(rec: dict) -> list[dict]:
    warnings.filterwarnings("ignore")
    sA = simulate(rec["design"], rec["law"], n=rec["n"], seed=rec["seed"], **rec["params"])
    law, d = sA.law, sA.X.shape[1]
    trees = {"oracle": (law.parametric, np.array(law.values, dtype=float), True)}
    sel = rec["select"].get(SET, {}).get(RULE)
    if sel and sel["recovered"]:
        form = parametrize(sel["expr"], d)
        th0, unique = true_constants(form, sA.X, sA.f0, seed=rec["seed"])
        if th0 is not None:
            trees["selected"] = (form, th0, unique)
    out = []
    for name, (form, th0, unique) in trees.items():
        base = {k: rec[k] for k in ("design", "law", "seed", "n", "params")}
        base.update(tree=name, p=form.n_constants, unique=bool(unique), expr=str(form.form), theta0=th0.tolist())
        # On A: the oracle starts at the truth; the selected tree starts at its own (A-fitted) constants.
        resA = inference(form, sA, th0, th0 if name == "oracle" else form.values)
        if resA is None:
            continue
        out.append(base | dict(sample="A") | resA)
        start = np.array(resA["theta"])
        for k in range(R):
            sB = simulate(rec["design"], rec["law"], n=rec["n"], seed=100_000 + 100 * rec["seed"] + k, **rec["params"])
            resB = inference(form, sB, th0, start)
            if resB is not None:
                out.append(base | dict(sample=f"B{k}") | resB)
    return out


def _safe(rec):
    try:
        return work(rec)
    except Exception:
        return [{k: rec[k] for k in ("design", "law", "seed")} | {"error": traceback.format_exc()}]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--workers", type=int, default=8)
    parser.add_argument("--limit", type=int, default=None)
    args = parser.parse_args()
    OUT_DIR.mkdir(exist_ok=True)
    recs = [json.loads(line) for line in (P4 / "analysis.jsonl").read_text().splitlines() if line.strip()]
    recs = [r for r in recs if "error" not in r and r["grid"] == "breadth"][: args.limit]
    out_file = OUT_DIR / "inference.jsonl"
    print(f"inference: {len(recs)} Phase 4 runs, {R} fresh samples each", flush=True)
    n_err = 0
    with ProcessPoolExecutor(args.workers) as pool, out_file.open("w") as f:
        futures = [pool.submit(_safe, r) for r in recs]
        for i, fut in enumerate(as_completed(futures), 1):
            for row in fut.result():
                n_err += "error" in row
                f.write(json.dumps(row) + "\n")
            if i % 25 == 0:
                print(f"[{i}/{len(recs)}]", flush=True)
    print(f"done; {n_err} errors", flush=True)


if __name__ == "__main__":
    main()
