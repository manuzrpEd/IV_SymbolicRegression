"""Phase 6, the Angrist–Krueger (1991) stress test (README §8.3).

    python experiments/phase6_ak.py      -> experiments/phase6/ak.json, experiments/phase6/ak.md

Data: the 1980 census extract of men born 1930-39 used by Angrist & Krueger (1991), as distributed with
Angrist & Pischke's Mastering 'Metrics (data/ak91.dta from masteringmetrics.com: 329,509 men; log weekly wage,
years of schooling, year, quarter and state of birth). The file is downloaded by hand and kept out of git.

Model: log wage = f0(schooling) + cohort effect + u, with quarter of birth as the instrument: compulsory-
schooling laws move schooling only near the leaving age. The cohort effect is removed by demeaning log wage
within year of birth; the instruments are the within-cohort quarter-of-birth contrasts (30, AK's Table V
specification) plus the constant, which is exactly valid for the demeaned model because the cohort constants
are orthogonal to within-cohort contrasts. A second set uses the three overall contrasts (K = 4).

Known answer: none for the functional form. AK report a linear return of about 0.07 (OLS) and 0.09 (2SLS).
The instruments cannot identify a shape over the whole range of schooling, so the right output is a report
of weak identification of the formula, not a confident formula. Schooling enters as x = years + 1, so that
log x and 1/x exist at zero years.
"""

from __future__ import annotations

import json
import sys
import time
import warnings
from pathlib import Path

import numpy as np
import pandas as pd
import sympy as sp

sys.path.insert(0, str(Path(__file__).parent))
from phase4 import SEARCH  # noqa: E402
from phase4_analysis import N_SYMBOLS, nodes  # noqa: E402

from symiv.baselines import fit_sieve_iv  # noqa: E402
from symiv.baselines.library_iv import library_path_candidates  # noqa: E402
from symiv.criteria import MomentCriterion  # noqa: E402
from symiv.criteria.instruments import orthonormalize  # noqa: E402
from symiv.expressions import parametrize, variables  # noqa: E402
from symiv.gmm import fit_gmm  # noqa: E402
from symiv.identification import ar_interval, identification_report, s_statistic, wald_se  # noqa: E402
from symiv.selection import PENALTIES, mmsc  # noqa: E402

HERE = Path(__file__).parent
DATA = HERE.parent / "data" / "ak91.dta"
OUT_DIR = HERE / "phase6"
SEARCH_POINTS = 30_000  # PySR subsample; selection and the sieve use all observations
DIAG_POINTS = 50_000  # the identification report (thousands of AR evaluations) runs on a subsample


def load():
    df = pd.read_stata(DATA)
    y = (df["lnw"] - df.groupby("yob")["lnw"].transform("mean")).to_numpy(dtype=float)
    X = (df["s"].to_numpy(dtype=float) + 1.0)[:, None]
    return y, X, df["qob"].to_numpy(dtype=int), df["yob"].to_numpy(dtype=int)


def instrument_matrix(qob, yob, within_cohort: bool) -> np.ndarray:
    """Constant plus quarter-of-birth contrasts: within each birth year (30 columns) or overall (3)."""
    cols = [np.ones(len(qob))]
    for k in (2, 3, 4):
        d = (qob == k).astype(float)
        if within_cohort:
            for j in np.unique(yob):
                m = yob == j
                cols.append((d - d[m].mean()) * m)
        else:
            cols.append(d - d.mean())
    return np.column_stack(cols)


def first_stage_F(x, B):
    """F statistic of the excluded instruments (all columns of B except the constant) in the regression of x on B."""
    n, K = B.shape
    beta, *_ = np.linalg.lstsq(B, x, rcond=None)
    rss1 = float(np.sum((x - B @ beta) ** 2))
    rss0 = float(np.sum((x - x.mean()) ** 2))
    return ((rss0 - rss1) / (K - 1)) / (rss1 / (n - K))


def classic(x, y, B):
    """OLS and 2SLS slopes of the linear specification, for comparison with AK's tables."""
    ols = np.polyfit(x, y, 1)[0]
    xhat = B @ np.linalg.lstsq(B, x, rcond=None)[0]
    tsls = np.polyfit(xhat, y, 1)[0]
    return float(ols), float(tsls)


def candidates(X, y, crit, seed=0):
    from symiv.search import pareto_front, plain_regressor

    rng = np.random.default_rng(seed)
    idx = rng.choice(len(y), size=SEARCH_POINTS, replace=False)
    plain = plain_regressor(**SEARCH)
    plain.fit(X[idx], y[idx])
    plain_exprs, _ = pareto_front(plain)
    curve = fit_sieve_iv(X, y, crit)
    idx2 = rng.choice(len(y), size=5000, replace=False)
    dist = plain_regressor(**SEARCH)
    dist.fit(X[idx2], curve(X[idx2]))
    dist_exprs, _ = pareto_front(dist)
    lib = library_path_candidates(X, y, crit)
    return dict(plain=[str(e) for e in plain_exprs], distill=[str(e) for e in dist_exprs], library=[str(e) for e in lib],
                plain_pick=str(plain.sympy()), sieve=curve)


def select(cands, X, y, crit):
    n = len(y)
    kappa_s = np.log(N_SYMBOLS["default"] + 1)
    scored = []
    for e in {str(parametrize(e, 1).expr()): e for g in ("plain", "distill", "library") for e in cands[g]}.values():
        form = parametrize(e, 1)
        fit = fit_gmm(form, X, y, crit, n_starts=2)
        if not np.isfinite(fit.J):
            continue
        bic = mmsc(fit, n, "bic")
        scored.append(dict(expr=str(form.expr(fit.theta)), p=form.n_constants, nodes=nodes(form.expr()), J=fit.J,
                           bic=bic, s05=bic + 0.5 * nodes(form.expr()) * kappa_s))
    best = {rule: min(scored, key=lambda c: (c[rule], c["p"], c["nodes"])) for rule in ("bic", "s05")}
    return scored, best


def returns(expr, at=(9.0, 13.0, 17.0)):
    """Slope d log wage / d years at given years of schooling (x = years + 1), by central differences."""
    f = parametrize(expr, 1)
    return {int(s): float((f(np.array([[s + 1.5]]))[0] - f(np.array([[s + 0.5]]))[0])) for s in at}


def main() -> None:
    warnings.filterwarnings("ignore")
    sys.stdout.reconfigure(encoding="utf-8")
    y, X, qob, yob = load()
    n = len(y)
    out = dict(n=int(n), sets={})
    L = ["# Phase 6: the Angrist–Krueger (1991) stress test\n",
         f"{n:,} men born 1930–39 (1980 census, the Mastering 'Metrics extract). Log weekly wage demeaned within year of "
         "birth; x = years of schooling + 1; instruments: quarter-of-birth contrasts. Candidates: plain PySR on a "
         f"{SEARCH_POINTS:,}-observation subsample, PySR distilled from the sieve-2SLS curve, the library path; selection on all "
         f"observations; the identification report on a {DIAG_POINTS:,}-observation subsample.\n"]
    for name, within in (("30 within-cohort QOB contrasts (AK Table V)", True), ("3 overall QOB contrasts", False)):
        t = time.time()
        B = instrument_matrix(qob, yob, within)
        crit = MomentCriterion(orthonormalize(B), "gmm")
        F = first_stage_F(X[:, 0], B)
        ols, tsls = classic(X[:, 0], y, B)
        cands = candidates(X, y, crit)
        scored, best = select(cands, X, y, crit)
        sieve = cands["sieve"]
        rng = np.random.default_rng(1)
        idx = rng.choice(n, size=DIAG_POINTS, replace=False)
        crit_sub = MomentCriterion(orthonormalize(B[idx]), "gmm")
        rep = identification_report(best["s05"]["expr"], [c["expr"] for c in scored], X[idx], y[idx], crit_sub)
        # The linear form's return, with Wald and AR intervals (robust to weak identification), on the same subsample.
        # (A literal 0.0 would be dropped by SymPy, so both constants start away from zero.)
        lin = parametrize("0.5 + 0.07*x0", 1)
        slope = next(j for j, c in enumerate(lin.params) if sp.diff(lin.form, c).has(variables(1)[0]))
        lin_fit = fit_gmm(lin, X[idx], y[idx], crit_sub)
        se = wald_se(lin, X[idx], y[idx], crit_sub, lin_fit.theta)
        envelope = 3 * float(np.max(np.abs(y[idx])))
        _, th_s = s_statistic(lin, X[idx], y[idx], crit_sub, lin_fit.theta, envelope=envelope)
        ar_lo, ar_hi, lb, hb = ar_interval(lin, X[idx], y[idx], crit_sub, th_s, slope, float(se[slope]), envelope=envelope)
        res = dict(K=crit.K, first_stage_F=F, ols=ols, tsls=tsls, n_candidates=len(scored),
                   pick_bic=best["bic"]["expr"], pick_structure=best["s05"]["expr"], plain_pick=cands["plain_pick"],
                   returns_structure=returns(best["s05"]["expr"]), returns_plain=returns(cands["plain_pick"]),
                   sieve_J=sieve.J, sieve_values={int(s): float(sieve(np.array([[s + 1.0]]))[0]) for s in (8, 12, 16)},
                   verdict=rep.verdict, reasons=rep.reasons[:5], n_in_set=len(rep.formula_set) - 1, max_distance=rep.max_distance,
                   width_ratio=rep.width_ratio, ar_bounded=rep.ar_bounded,
                   linear_return=dict(estimate=float(lin_fit.theta[slope]),
                                      wald=[float(lin_fit.theta[slope] - 1.96 * se[slope]), float(lin_fit.theta[slope] + 1.96 * se[slope])],
                                      ar=[float(ar_lo), float(ar_hi)], ar_bounded=bool(lb and hb)),
                   seconds=time.time() - t)
        out["sets"][name] = res
        L.append(f"## {name}: K = {crit.K}\n")
        L.append(f"- First-stage F = {F:.1f}. Linear return: OLS {ols:.3f}, 2SLS {tsls:.3f} (AK: about 0.07 and 0.09).")
        L.append(f"- Sieve-2SLS curve (J = {sieve.J}): f(8) = {res['sieve_values'][8]:.2f}, f(12) = {res['sieve_values'][12]:.2f}, f(16) = {res['sieve_values'][16]:.2f}.")
        L.append(f"- Plain PySR's own pick: `{cands['plain_pick']}`; implied return per year at 9 / 13 / 17 years: "
                 + " / ".join(f"{v:.3f}" for v in res["returns_plain"].values()) + ".")
        L.append(f"- Pooled + MMSC-BIC: `{best['bic']['expr']}`. Pooled + BIC + structure: `{best['s05']['expr']}`; return at 9 / 13 / 17 years: "
                 + " / ".join(f"{v:.3f}" for v in res["returns_structure"].values()) + ".")
        L.append(f"- Linear form, return per year: {res['linear_return']['estimate']:.3f}; Wald 95% [{res['linear_return']['wald'][0]:.3f}, {res['linear_return']['wald'][1]:.3f}]; "
                 f"AR 95% [{ar_lo:.3f}, {ar_hi:.3f}]" + ("" if lb and hb else " (reaches the bound)") + ".")
        L.append(f"- **Identification report: {rep.verdict}.** {len(rep.formula_set) - 1} of {len(rep.candidates)} other candidates are not rejected; "
                 f"the farthest is {rep.max_distance:.2f} sd from the selected formula. AR/Wald width ratios: "
                 + ", ".join(f"{r:.1f}" if np.isfinite(r) else "∞" for r in rep.width_ratio) + ".")
        for r in rep.reasons[:4]:
            L.append(f"  - {r[:140]}")
        L.append("")
        print("\n".join(L[-8:]), flush=True)
    OUT_DIR.mkdir(exist_ok=True)
    (OUT_DIR / "ak.json").write_text(json.dumps(out, indent=1, default=float))
    (OUT_DIR / "ak.md").write_text("\n".join(L) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
