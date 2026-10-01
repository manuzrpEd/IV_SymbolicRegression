"""Phase 6, Engel curves (README §8.3): the pipeline, ready for the Family Expenditure Survey data.

    python experiments/phase6_engel.py --data data/fes.csv [--share share_food --logexp logexp --instrument logearn]
    python experiments/phase6_engel.py --synthetic        # a self-test on FES-like simulated data

Blundell, Chen & Kristensen (2007) estimate Engel curves, budget shares against log total expenditure, by
nonparametric IV with the household head's log gross earnings as the instrument (expenditure is endogenous
through measurement error and infrequent purchases). Known answers: the food share is close to linear in log
expenditure (Working–Leser); other goods are quadratic (Banks, Blundell & Lewbel 1997).

The real data need a UK Data Service registration, so this script takes a CSV with one row per household and
columns for the share, log expenditure and the instrument. `--synthetic` draws FES-like data from a Working–Leser
food share with measurement error in expenditure, to check the pipeline end to end; its output is not evidence.

Output: the selected formula (pooled candidates, BIC + structure), the S tests of the Working–Leser and quadratic
forms, the sieve-2SLS curve, plain PySR's pick, and the identification report, in experiments/phase6/engel.md.
"""

from __future__ import annotations

import argparse
import sys
import warnings
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).parent))
from phase4 import SEARCH  # noqa: E402
from phase4_analysis import N_SYMBOLS, nodes  # noqa: E402

from symiv.baselines import fit_sieve_iv  # noqa: E402
from symiv.baselines.library_iv import library_path_candidates  # noqa: E402
from symiv.criteria import gmm_criterion  # noqa: E402
from symiv.expressions import parametrize  # noqa: E402
from symiv.gmm import fit_gmm  # noqa: E402
from symiv.identification import identification_report, s_statistic  # noqa: E402
from symiv.selection import mmsc  # noqa: E402

OUT_DIR = Path(__file__).parent / "phase6"


def synthetic(n: int = 1500, seed: int = 0):
    """FES-like data: log earnings -> true log expenditure; the observed expenditure has measurement error, which also
    enters the observed share (share = food / expenditure), so the regressor is endogenous and earnings is valid."""
    rng = np.random.default_rng(seed)
    logearn = rng.normal(5.5, 0.4, n)
    x_true = 1.0 + 0.8 * logearn + rng.normal(0.0, 0.25, n)
    share_true = 0.45 - 0.06 * x_true + rng.normal(0.0, 0.03, n)  # Working–Leser food share
    m = rng.normal(0.0, 0.15, n)  # measurement error in log expenditure
    x_obs = x_true + m
    share_obs = share_true * np.exp(-m)
    return share_obs, x_obs[:, None], logearn[:, None], "0.45 - 0.06*x0"


def load_csv(path, share, logexp, instrument):
    import pandas as pd

    df = pd.read_csv(path).dropna(subset=[share, logexp, instrument])
    return df[share].to_numpy(float), df[[logexp]].to_numpy(float), df[[instrument]].to_numpy(float), None


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--data", type=Path)
    parser.add_argument("--share", default="share_food")
    parser.add_argument("--logexp", default="logexp")
    parser.add_argument("--instrument", default="logearn")
    parser.add_argument("--synthetic", action="store_true")
    args = parser.parse_args()
    warnings.filterwarnings("ignore")
    sys.stdout.reconfigure(encoding="utf-8")
    if args.synthetic:
        y, X, Z, truth = synthetic()
        source = "synthetic FES-like data (pipeline test, not evidence)"
    elif args.data:
        y, X, Z, truth = load_csv(args.data, args.share, args.logexp, args.instrument)
        source = str(args.data)
    else:
        parser.error("give --data or --synthetic")

    from symiv.search import pareto_front, plain_regressor

    n = len(y)
    crit = gmm_criterion(Z)
    plain = plain_regressor(**SEARCH)
    plain.fit(X, y)
    plain_exprs, _ = pareto_front(plain)
    curve = fit_sieve_iv(X, y, crit)
    dist = plain_regressor(**SEARCH)
    dist.fit(X, curve(X))
    dist_exprs, _ = pareto_front(dist)
    lib = library_path_candidates(X, y, crit)
    pool = {str(parametrize(e, 1).expr()): str(e) for e in [*plain_exprs, *dist_exprs, *lib]}
    kappa_s = np.log(N_SYMBOLS["default"] + 1)
    scored = []
    for e in pool.values():
        form = parametrize(e, 1)
        fit = fit_gmm(form, X, y, crit, n_starts=2)
        if np.isfinite(fit.J):
            bic = mmsc(fit, n, "bic")
            scored.append(dict(expr=str(form.expr(fit.theta)), p=form.n_constants, nodes=nodes(form.expr()), bic=bic,
                               s05=bic + 0.5 * nodes(form.expr()) * kappa_s))
    best = {rule: min(scored, key=lambda c: (c[rule], c["p"], c["nodes"])) for rule in ("bic", "s05")}
    rep = identification_report(best["s05"]["expr"], [c["expr"] for c in scored], X, y, crit)
    envelope = 3 * float(np.max(np.abs(y)))
    tests = {}
    for label, e in (("Working–Leser a + b log x", "0.4 - 0.05*x0"), ("quadratic a + b log x + c (log x)^2", "0.4 - 0.05*x0 + 0.001*x0**2")):
        form = parametrize(e, 1)
        fit = fit_gmm(form, X, y, crit, n_starts=4)
        S, _ = s_statistic(form, X, y, crit, fit.theta, envelope=envelope)
        tests[label] = dict(expr=str(form.expr(fit.theta)), J=fit.J, df=fit.df, S=S, critical=rep.critical, rejected=bool(S > rep.critical))

    L = [f"# Phase 6: Engel curves\n", f"Source: {source}; n = {n}; K = {crit.K} spline instruments in the head's log earnings."
         + (f" True curve: `{truth}`." if truth else "") + "\n",
         f"- Plain PySR's own pick: `{plain.sympy()}`.",
         f"- Sieve-2SLS curve: J = {curve.J}.",
         f"- Pooled + MMSC-BIC: `{best['bic']['expr']}`.",
         f"- **Pooled + BIC + structure: `{best['s05']['expr']}`**.",
         f"- **Identification report: {rep.verdict}**; first-stage F = {rep.first_stage.F[0]:.1f}; {len(rep.formula_set) - 1} of "
         f"{len(rep.candidates)} other candidates not rejected, farthest {rep.max_distance:.2f} sd away."]
    L += [f"  - {r[:140]}" for r in rep.reasons[:4]]
    L.append("- Parametric forms, with their S tests (chi^2 with K degrees of freedom; valid without a rank condition):")
    for label, t in tests.items():
        L.append(f"  - {label}: `{t['expr']}`; J = {t['J']:.1f} on {t['df']} df; S = {t['S']:.1f} vs {t['critical']:.1f}: "
                 + ("rejected" if t["rejected"] else "not rejected") + ".")
    OUT_DIR.mkdir(exist_ok=True)
    (OUT_DIR / "engel.md").write_text("\n".join(L) + "\n", encoding="utf-8")
    print("\n".join(L))


if __name__ == "__main__":
    main()
