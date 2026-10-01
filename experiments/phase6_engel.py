"""Phase 6, Engel curves (README §8.3) on the 1995 Family Expenditure Survey extract of Blundell, Chen & Kristensen (2007).

    python experiments/phase6_engel.py --data data/engel95.csv                 # 7 shares x {all, no children, children}
    python experiments/phase6_engel.py --data data/engel95.csv --shares food leisure --subsamples nokids
    python experiments/phase6_engel.py --synthetic                              # pipeline self-test on FES-like data

Data. `Engel95`, the data frame shipped with the R package `np` (Hayfield & Racine; CRAN, GPL): a random sample of
the 1995 British FES, 1655 married couples with an employed head aged 25-55, with the budget shares of food,
catering, alcohol, fuel, motor, fares and leisure, log total expenditure (`logexp`), the head's log earnings
(`logwages`, the instrument) and a children indicator (628 couples without, 1027 with). It is the sample of BCK
2007 and needs no registration or affiliation: download np_<version>.tar.gz from CRAN, extract np/data/Engel95.rda
and read it with `pyreadr` (see README §8.3). Kept in data/, which is git-ignored.

Model. share = f0(log expenditure) + u, E[u | log earnings] = 0: expenditure is endogenous through measurement
error and infrequent purchases (BCK 2007). Known answers: the food share is close to linear in log expenditure
(Working-Leser); other goods need a quadratic term (Banks, Blundell & Lewbel 1997).

Per share and subsample: candidates from plain PySR, PySR distilled from the sieve-2SLS curve, the library path and
the template library (symiv.templates), pooled; selection by MMSC-BIC and BIC + structure (also without the
templates); the identification report of Proposition 5; the S tests of the Working-Leser and quadratic-in-logs
forms, and an identification-robust (AR) interval for the quadratic coefficient. Output: experiments/phase6/engel.md
and engel.json (resumable: finished share x subsample pairs are kept).
"""

from __future__ import annotations

import argparse
import json
import sys
import time
import warnings
from pathlib import Path

import numpy as np
import sympy as sp

sys.path.insert(0, str(Path(__file__).parent))
from phase4 import SEARCH  # noqa: E402
from phase4_analysis import N_SYMBOLS, nodes  # noqa: E402

from symiv.baselines import fit_sieve_iv  # noqa: E402
from symiv.baselines.library_iv import library_path_candidates  # noqa: E402
from symiv.criteria import gmm_criterion  # noqa: E402
from symiv.expressions import parametrize, variables  # noqa: E402
from symiv.gmm import fit_gmm  # noqa: E402
from symiv.identification import ar_interval, identification_report, s_statistic, wald_se  # noqa: E402
from symiv.selection import mmsc  # noqa: E402
from symiv.templates import template_candidates  # noqa: E402

OUT_DIR = Path(__file__).parent / "phase6"
SHARES = ("food", "catering", "alcohol", "fuel", "motor", "fares", "leisure")
SUBSAMPLES = {"all": "all couples", "nokids": "no children", "kids": "with children"}
FORMS = {"wl": ("Working–Leser a + b log x", "0.4 - 0.05*x0"),
         "quad": ("quadratic a + b log x + c (log x)²", "0.4 - 0.05*x0 + 0.001*x0**2")}


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
    return share_obs, x_obs[:, None], logearn[:, None]


def searches(y: np.ndarray, X: np.ndarray, Z: np.ndarray, seed: int = 0) -> dict:
    """The candidate generators that need PySR: plain PySR's front, and PySR distilled from the sieve-2SLS curve."""
    from symiv.search import pareto_front, plain_regressor

    crit = gmm_criterion(Z)
    plain = plain_regressor(**SEARCH, random_state=seed)
    plain.fit(X, y)
    plain_exprs, _ = pareto_front(plain)
    curve = fit_sieve_iv(X, y, crit)
    dist = plain_regressor(**SEARCH, random_state=seed)
    dist.fit(X, curve(X))
    dist_exprs, _ = pareto_front(dist)
    return dict(plain=[str(e) for e in plain_exprs], distill=[str(e) for e in dist_exprs], plain_pick=str(plain.sympy()), sieve_J=curve.J)


def run_one(y: np.ndarray, X: np.ndarray, Z: np.ndarray, seed: int = 0, searched: dict | None = None) -> dict:
    """`searched`: the output of `searches` from an earlier run, to redo the analysis without the PySR searches."""
    t0 = time.time()
    n = len(y)
    crit = gmm_criterion(Z)
    searched = searched or searches(y, X, Z, seed)
    sources = {"plain": searched["plain"], "distill": searched["distill"],
               "library": library_path_candidates(X, y, crit), "templates": template_candidates()}

    # One scored candidate per distinct form; a candidate remembers every source that proposed it.
    kappa_s = np.log(N_SYMBOLS["default"] + 1)
    scored: dict[str, dict] = {}
    for src, exprs in sources.items():
        for e in exprs:
            form = parametrize(e, 1)
            k = str(form.form)
            if k in scored:
                scored[k]["sources"].append(src)
                continue
            fit = fit_gmm(form, X, y, crit, n_starts=2)
            if not np.isfinite(fit.J):
                continue
            bic = mmsc(fit, n, "bic")
            scored[k] = dict(expr=str(form.expr(fit.theta)), form=k, p=form.n_constants, nodes=nodes(form.expr()), J=fit.J,
                             bic=bic, s05=bic + 0.5 * nodes(form.expr()) * kappa_s, sources=[src])
    cands = list(scored.values())
    pick = lambda rule, pool: min(pool, key=lambda c: (c[rule], c["p"], c["nodes"]))  # noqa: E731
    best = {"bic": pick("bic", cands), "s05": pick("s05", cands),
            "s05_search": pick("s05", [c for c in cands if c["sources"] != ["templates"]])}
    rep = identification_report(best["s05"]["expr"], [c["expr"] for c in cands], X, y, crit, seed=seed)
    # The same selection restricted to the formula confidence set (the selected formula, if not rejected, and
    # every candidate whose S test passes): what to report when the pick itself fails the moment conditions.
    S_of = {ch.expr: ch.S for ch in rep.candidates} | {best["s05"]["expr"]: rep.S_selected}
    in_set = [c for c in cands if S_of.get(c["expr"], np.inf) <= rep.critical]
    best["s05_in_set"] = pick("s05", in_set) if in_set else None
    envelope = 3 * float(np.max(np.abs(y)))
    x0 = variables(1)[0]

    tests = {}
    for key, (label, e) in FORMS.items():
        form = parametrize(e, 1)
        fit = fit_gmm(form, X, y, crit, n_starts=4)
        S, theta_s = s_statistic(form, X, y, crit, fit.theta, envelope=envelope)
        t = dict(label=label, expr=str(form.expr(fit.theta)), J=fit.J, df=fit.df, S=S, critical=rep.critical, rejected=bool(S > rep.critical))
        if key == "quad":  # the quadratic coefficient at the S minimizer (CUE), its Wald s.e., and its projection AR interval
            j = next(j for j, c in enumerate(form.params) if sp.diff(form.form, c) == x0**2)
            se = wald_se(form, X, y, crit, fit.theta)
            lo, hi, lo_b, hi_b = ar_interval(form, X, y, crit, theta_s, j, step=max(float(se[j]), 1e-4), envelope=envelope)
            t["quadratic_term"] = dict(estimate=float(theta_s[j]), two_step=float(fit.theta[j]), se=float(se[j]), ar=[float(lo), float(hi)],
                                       bounded=bool(lo_b and hi_b), includes_zero=bool(np.isnan(lo) or lo <= 0 <= hi))
        tests[key] = t

    q = np.quantile(X[:, 0], [0.1, 0.5, 0.9])
    f_sel = parametrize(best["s05"]["expr"], 1)
    return dict(n=n, K=crit.K, first_stage_F=float(rep.first_stage.F[0]), plain_pick=searched["plain_pick"], sieve_J=searched["sieve_J"],
                searched={k: searched[k] for k in ("plain", "distill", "plain_pick", "sieve_J")},
                selected={k: (dict(expr=v["expr"], sources=v["sources"], p=v["p"]) if v else None) for k, v in best.items()},
                shape=dict(quantiles=q.tolist(), values=f_sel(q[:, None]).tolist()),
                verdict=rep.verdict, reasons=rep.reasons[:4], S_selected=rep.S_selected, critical=rep.critical,
                n_in_set=len(rep.formula_set) - 1, n_candidates=len(rep.candidates), max_distance=rep.max_distance,
                ar_intervals=rep.ar_intervals, ar_bounded=rep.ar_bounded, wald_se=rep.se, tests=tests, seconds=time.time() - t0)


def load(path: Path, logexp: str, instrument: str, kids: str):
    import pandas as pd

    df = pd.read_csv(path)
    return df, df[logexp].to_numpy(float)[:, None], df[instrument].to_numpy(float)[:, None], df[kids].to_numpy(float)


def shape_word(vals: list[float]) -> str:
    a, b, c = vals
    if max(vals) - min(vals) < 1e-9:
        return "flat"
    if a > b > c:
        return "decreasing"
    if a < b < c:
        return "increasing"
    return "hump" if b > max(a, c) else "U-shaped"


def write_report(results: dict, source: str, path: Path) -> str:
    L = ["# Phase 6: Engel curves on the FES 1995 extract of Blundell, Chen & Kristensen (2007)\n",
         f"Source: {source}. Candidates: plain PySR, PySR distilled from the sieve-2SLS curve, the library path and the template "
         "library, pooled; selection by BIC + structure (w = 0.5); K spline instruments in the head's log earnings. "
         "'Search only' is the same selection without the templates. The S tests are Proposition 5's (χ² with K degrees of "
         "freedom, valid without a rank condition); the AR interval for the quadratic term is the projection interval around "
         "the S minimizer. Shape: the selected curve at the 10th, 50th and 90th percentiles of log expenditure.\n"]
    for sub, label in SUBSAMPLES.items():
        rows = [(share, results[f"{share}|{sub}"]) for share in SHARES if f"{share}|{sub}" in results]
        if not rows:
            continue
        L.append(f"## {label.capitalize()} (n = {rows[0][1]['n']}, K = {rows[0][1]['K']})\n")
        L.append("| Share | First-stage F | Selected: pooled + BIC + structure | Search only | Within the confidence set | Shape | Identification | "
                 "Working–Leser: S | Quadratic: S | Quadratic term c: estimate, AR 95% interval |")
        L.append("|---|---|---|---|---|---|---|---|---|---|")
        for share, r in rows:
            wl, qd = r["tests"]["wl"], r["tests"]["quad"]
            qt = qd["quadratic_term"]
            ar = f"[{qt['ar'][0]:.3f}, {qt['ar'][1]:.3f}]" + ("" if qt["bounded"] else " (unbounded)")
            sel = r["selected"]
            same = sel["s05_search"]["expr"] == sel["s05"]["expr"]
            in_set = sel.get("s05_in_set")
            in_set_cell = "same" if in_set and in_set["expr"] == sel["s05"]["expr"] else (f"`{in_set['expr']}`" if in_set else "none")
            L.append(f"| {share} | {r['first_stage_F']:.0f} | `{sel['s05']['expr']}` ({'+'.join(sel['s05']['sources'])}) | "
                     f"{'same' if same else '`' + sel['s05_search']['expr'] + '`'} | {in_set_cell} | {shape_word(r['shape']['values'])} | "
                     f"{r['verdict']} ({r['n_in_set']}/{r['n_candidates']} not rejected, farthest {r['max_distance']:.2f} sd) | "
                     f"{wl['S']:.1f} vs {wl['critical']:.1f}: {'**rejected**' if wl['rejected'] else 'not rejected'} | "
                     f"{qd['S']:.1f} vs {qd['critical']:.1f}: {'**rejected**' if qd['rejected'] else 'not rejected'} | "
                     f"{qt['estimate']:.3f}, {ar}{'' if qt['includes_zero'] else ' **excludes 0**'} |")
        L.append("")
        L.append("Details: plain PySR's own pick (the shape of E[share | log expenditure]); the sieve-2SLS curve's J; the AR "
                 "intervals of the selected formula's constants; the reasons of the identification report.\n")
        for share, r in rows:
            ars = "; ".join(f"[{lo:.3g}, {hi:.3g}]" + ("" if b else " unbounded") for (lo, hi), b in zip(r["ar_intervals"], r["ar_bounded"]))
            L.append(f"- **{share}**: plain PySR picks `{r['plain_pick']}`; sieve J = {r['sieve_J']}; MMSC-BIC alone picks "
                     f"`{r['selected']['bic']['expr']}`; AR intervals of the constants: {ars}; S of the selection {r['S_selected']:.1f} "
                     f"vs {r['critical']:.1f}; {r['seconds']:.0f} s.")
            for reason in r["reasons"][:2]:
                L.append(f"  - {reason[:150]}")
        L.append("")
    text = "\n".join(L) + "\n"
    path.write_text(text, encoding="utf-8")
    return text


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--data", type=Path)
    parser.add_argument("--shares", nargs="+", default=list(SHARES))
    parser.add_argument("--subsamples", nargs="+", default=list(SUBSAMPLES), choices=list(SUBSAMPLES))
    parser.add_argument("--logexp", default="logexp")
    parser.add_argument("--instrument", default="logwages")
    parser.add_argument("--kids", default="nkids")
    parser.add_argument("--synthetic", action="store_true")
    parser.add_argument("--reanalyze", action="store_true", help="redo the selection, tests and report from the saved searches")
    parser.add_argument("--out", type=Path, default=None, help="report path (default phase6/engel.md; engel_synthetic.md for --synthetic)")
    args = parser.parse_args()
    warnings.filterwarnings("ignore")
    sys.stdout.reconfigure(encoding="utf-8")
    OUT_DIR.mkdir(exist_ok=True)

    if args.synthetic:
        y, X, Z = synthetic()
        r = run_one(y, X, Z)
        text = write_report({"food|all": r}, "synthetic FES-like data with the planted food share 0.45 − 0.06 log x (a pipeline test, not evidence)",
                            args.out or OUT_DIR / "engel_synthetic.md")
        print(text)
        return
    if not args.data:
        parser.error("give --data or --synthetic")

    df, X_all, Z_all, kids = load(args.data, args.logexp, args.instrument, args.kids)
    masks = {"all": np.ones(len(df), bool), "nokids": kids == 0, "kids": kids > 0}
    json_path = OUT_DIR / "engel.json"
    results = json.loads(json_path.read_text()) if json_path.exists() else {}
    for sub in args.subsamples:
        for share in args.shares:
            k = f"{share}|{sub}"
            if k in results and not args.reanalyze:
                continue
            m = masks[sub]
            t = time.time()
            searched = results[k].get("searched") if k in results else None
            results[k] = run_one(df[share].to_numpy(float)[m], X_all[m], Z_all[m], searched=searched)
            json_path.write_text(json.dumps(results, indent=1))
            r = results[k]
            print(f"{k:16s} n={r['n']:4d} F={r['first_stage_F']:5.0f} {r['verdict']:18s} pick={r['selected']['s05']['expr'][:60]:60s} "
                  f"WL {'rej' if r['tests']['wl']['rejected'] else 'ok '}  quad {'rej' if r['tests']['quad']['rejected'] else 'ok '}  {time.time() - t:4.0f}s", flush=True)
    source = (f"`{args.data}`: the `Engel95` data of the R package `np` (FES 1995; BCK 2007), {len(df)} couples, "
              f"{int((kids == 0).sum())} without children and {int((kids > 0).sum())} with; instrument `{args.instrument}`")
    print(write_report(results, source, args.out or OUT_DIR / "engel.md"))


if __name__ == "__main__":
    main()
