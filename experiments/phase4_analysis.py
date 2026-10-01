"""Phase 4, part 2: selection rules and metrics on the saved fronts. Pure Python, parallel.

    python experiments/phase4_analysis.py              # per-run analysis -> phase4/analysis.jsonl (resumable)
    python experiments/phase4_analysis.py --separation # delta_hat per cell -> phase4/separation.json

Per run: re-simulate the data (seeded, as in the search), build the candidate sets,
refit every candidate once per criterion, apply every selection rule to every set.

Candidate sets: each generator's front (plain, onestep, distill), "library" (one
formula per term set on the projected Lasso path; one regressor only), "iv" (onestep
and distill pooled), "pooled" (everything).

Selection rules (lower is better; ties go to fewer constants, then fewer nodes):
  bic, hqic, aic   MMSC = J - (K - p) kappa_n with the default instruments (README §6.3)
  bic_s05, bic_s1  BIC plus w * nodes * ln(m): a structure term, log of the number of trees
                   of that size over m symbols (Theorem 2's log|S|), with w = 0.5 or 1
  bic_K2           BIC with twice as many instruments (selection only; searches used the default)
  bic_mmr          BIC with kernel (Nystrom) instruments instead of splines
  cv               two-fold cross-fitted moment criterion (README §6.3)
At n >= 20000 only the default-instrument rules are computed (cost).
"""

from __future__ import annotations

import os

for _v in ("OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "OMP_NUM_THREADS"):
    os.environ.setdefault(_v, "1")  # one BLAS thread per worker process

import argparse  # noqa: E402
import json  # noqa: E402
import sys  # noqa: E402
import traceback  # noqa: E402
import warnings  # noqa: E402
from concurrent.futures import ProcessPoolExecutor, as_completed  # noqa: E402
from pathlib import Path  # noqa: E402

import numpy as np  # noqa: E402
import sympy as sp  # noqa: E402

sys.path.insert(0, str(Path(__file__).parent))
from phase4 import OUT_DIR, default_criterion, key  # noqa: E402

from symiv.baselines.library_iv import library_path_candidates  # noqa: E402
from symiv.criteria import MomentCriterion, gmm_criterion, mmr_criterion  # noqa: E402
from symiv.dgp import simulate  # noqa: E402
from symiv.dgp.laws import LAWS  # noqa: E402
from symiv.expressions import parametrize  # noqa: E402
from symiv.gmm import fit_gmm  # noqa: E402
from symiv.metrics import elasticity, extrapolation_error, implied_constants, relative_error  # noqa: E402
from symiv.recovery import form_recovered  # noqa: E402
from symiv.selection import PENALTIES, mmsc  # noqa: E402

BIG_N = 20000
RULES = ("bic", "hqic", "aic", "bic_s05", "bic_s1", "bic_K2", "bic_mmr", "cv")
DEFAULT_RULES = ("bic", "hqic", "aic", "bic_s05", "bic_s1")
N_SYMBOLS = {"default": 6 + 2 + 1, "nomax": 5 + 2 + 1}  # binary + unary operators + constant (+ d variables)


def nodes(expr: sp.Expr) -> int:
    return sum(1 for _ in sp.preorder_traversal(expr))


def cross_fitted_q(form, X, y, A, seed) -> float:
    """Sum over two folds of the held-out criterion, constants fitted on the other fold."""
    fold = np.random.default_rng(seed).permutation(len(y)) % 2
    total = 0.0
    for k in (0, 1):
        tr, va = fold != k, fold == k
        fit = fit_gmm(form, X[tr], y[tr], MomentCriterion(A[tr], "gmm"), n_starts=2)
        r = y[va] - form(X[va], fit.theta)
        if not np.all(np.isfinite(r)):
            return np.inf
        g = A[va].T @ r
        total += g @ g / va.sum()
    return float(total)


def describe(expr, law, X, recovered: bool) -> dict:
    d = X.shape[1]
    return dict(
        expr=str(expr),
        recovered=bool(recovered),
        rel_error=relative_error(expr, law, X),
        extrap_error=extrapolation_error(expr, law, X),
        elasticity=elasticity(expr, float(np.median(X[:, 0]))) if d == 1 else None,
        implied=implied_constants(expr, law, X).tolist(),
    )


def analyze(rec: dict, extra_sets: dict[str, list[str]] | None = None) -> dict:
    """`extra_sets`: further named candidate sets (expression strings), e.g. the template library; they join the pool."""
    warnings.filterwarnings("ignore")
    s = simulate(rec["design"], rec["law"], n=rec["n"], seed=rec["seed"], **rec["params"])
    X, y, law, n, d = s.X, s.y, s.law, s.n, s.X.shape[1]
    big = n >= BIG_N
    rules = DEFAULT_RULES if big else RULES
    crits = {"default": default_criterion(s)}
    if not big:
        crits["K2"] = gmm_criterion(s.Z, K=2 * crits["default"].K) if d == 1 else gmm_criterion(s.Z, basis="poly", degree=5)
        crits["mmr"] = mmr_criterion(s.Z, m=100, seed=rec["seed"])

    # Candidate sets.
    sets = {g: list(fr["exprs"]) for g, fr in rec["fronts"].items()}
    if d == 1:
        sets["library"] = library_path_candidates(X, y, crits["default"])
    for name, exprs in (extra_sets or {}).items():
        sets[name] = list(exprs)
    if "onestep" in sets and "distill" in sets:
        sets["iv"] = sets["onestep"] + sets["distill"]
    sets["pooled"] = [e for name in list(sets) if name not in ("iv", "pooled") for e in sets[name]]

    # Each distinct candidate is refitted once per criterion.
    canon, cands = {}, []
    for name, exprs in sets.items():
        ids = []
        for e in exprs:
            c = str(sp.sympify(e))
            if c not in canon:
                canon[c] = len(cands)
                cands.append(dict(expr=c, sets=[]))
            ids.append(canon[c])
        sets[name] = sorted(set(ids))
        for i in sets[name]:
            cands[i]["sets"].append(name)

    kappa_s = np.log(N_SYMBOLS[rec["ops"]] + d)
    for c in cands:
        form = parametrize(c["expr"], d)
        c["form"], c["p"], c["nodes"] = str(form.form), form.n_constants, nodes(sp.sympify(c["expr"]))
        rr = form_recovered(c["expr"], law, X)
        c["recovered"], c["rel_error_form"] = rr.recovered, rr.rel_error
        c["fits"] = {}
        for cname, crit in crits.items():
            fit = fit_gmm(form, X, y, crit, n_starts=4 if cname == "default" else 2, seed=rec["seed"])
            c["fits"][cname] = (fit.theta, fit.J, fit.K, fit.p)
        if not big:
            c["cv"] = cross_fitted_q(form, X, y, crits["default"].A, rec["seed"])
        c["_form"] = form

    def score(c, rule):
        def mm(cname, pen):
            theta, J, K, p = c["fits"][cname]
            return J - (K - p) * PENALTIES[pen](n) if np.isfinite(J) else np.inf

        if rule in ("bic", "hqic", "aic"):
            return mm("default", rule)
        if rule == "bic_s05":
            return mm("default", "bic") + 0.5 * c["nodes"] * kappa_s
        if rule == "bic_s1":
            return mm("default", "bic") + 1.0 * c["nodes"] * kappa_s
        if rule == "bic_K2":
            return mm("K2", "bic")
        if rule == "bic_mmr":
            return mm("mmr", "bic")
        return c["cv"]

    crit_of = {"bic_K2": "K2", "bic_mmr": "mmr"}
    true_fits = {cname: fit_gmm(law.parametric, X, y, crit, theta0=np.array(law.values)) for cname, crit in crits.items()}
    true_bic = mmsc(true_fits["default"], n, "bic")

    out = {k: rec[k] for k in ("grid", "design", "law", "n", "seed", "setting", "params", "ops")}
    out.update(K=crits["default"].K, n_candidates={}, coverage={}, beaters={}, select={}, sieve=rec.get("sieve"))
    cache = {}
    for name, ids in sets.items():
        if not ids:
            continue
        pool = [cands[i] for i in ids]
        out["n_candidates"][name] = len(pool)
        out["coverage"][name] = any(c["recovered"] for c in pool)
        # Wrong candidates (cannot represent f0 at all) that outscore the true form under BIC.
        out["beaters"][name] = int(sum(c["rel_error_form"] > 1e-3 and score(c, "bic") < true_bic for c in pool))
        out["select"][name] = {}
        for rule in rules:
            best = min(pool, key=lambda c: (score(c, rule), c["p"], c["nodes"]))
            cname = crit_of.get(rule, "default")
            k = (canon[best["expr"]], cname)
            if k not in cache:
                fitted = best["_form"].expr(best["fits"][cname][0])
                cache[k] = describe(fitted, law, X, best["recovered"])
            out["select"][name][rule] = cache[k]

    out["pysr_pick"] = {g: describe(fr["pick"], law, X, form_recovered(fr["pick"], law, X).recovered) for g, fr in rec["fronts"].items()}
    if rec.get("cf"):
        e = rec["cf"]["expr"]
        out["cf"] = describe(e, law, X, form_recovered(e, law, X).recovered)
    out["candidates"] = [dict(expr=c["expr"], form=c["form"], p=c["p"], nodes=c["nodes"], recovered=c["recovered"],
                              rel_error_form=c["rel_error_form"], sets=c["sets"]) for c in cands]
    out["sigma_u2"] = float(np.var(s.hidden["u"]))
    return out


def _safe(rec):
    try:
        return analyze(rec)
    except Exception:
        return {k: rec[k] for k in ("grid", "design", "law", "n", "seed", "setting", "params", "ops")} | {"error": traceback.format_exc()}


# ------------------------------------------------------------------ separation


def cell_key(r: dict) -> str:
    """Runs with the same design, law and parameters share one population; delta depends on n only through K."""
    return json.dumps([r["design"], r["law"], r["params"]], sort_keys=True)


def separation(cell: str, forms: list[tuple[str, int]], ns: list[int]) -> dict:
    """Theorem 2's separation, restricted to the wrong formulas that the penalty cannot exclude.

    A wrong formula s with p_s <= p0 constants beats the truth under MMSC-BIC when its J statistic falls below the
    penalty it saves, (p0 - p_s) ln n. Its population J is about lambda_s = n delta_s / sigma_u^2, with
    delta_s = min_theta ||P_A (f_s(theta) - f0)||^2 / n computed with the instruments the selection used at that n
    (K ~ n^(1/3)), on 20,000 noise-free draws. Margin = min_s [lambda_s - (p0 - p_s) ln n]: positive means the
    closest wrong formula loses in the population. Formulas with more constants than f0 can only win by fitting
    noise; that channel is measured by the beaters, not here.
    """
    warnings.filterwarnings("ignore")
    design, law_name, params = json.loads(cell)
    s = simulate(design, law_name, n=BIG_N, seed=10_000, **params)
    law, f0 = s.law, s.f0
    p0, sd2, sigma_u2 = law.n_constants, float(f0.var()), float(np.var(s.hidden["u"]))
    by_n, n_not_wrong = {}, 0
    parsed = [(e, parametrize(sp.sympify(e), s.X.shape[1])) for e, _ in forms]
    for n in ns:
        crit = gmm_criterion(s.Z, K=max(8, round(n ** (1 / 3)))) if s.X.shape[1] == 1 else gmm_criterion(s.Z, basis="poly", degree=4)
        best = None
        for e, form in parsed:
            fit = fit_gmm(form, s.X, f0, crit, n_starts=4, seed=0)
            r = f0 - form(s.X, fit.theta)
            if not np.all(np.isfinite(r)):
                continue
            if np.sqrt(np.mean(r ** 2) / sd2) < 1e-3:  # it can represent f0 after all: not a wrong formula
                n_not_wrong += n == ns[0]
                continue
            delta = crit.value(r)
            lam = n * delta / sigma_u2
            margin = lam - (p0 - form.n_constants) * np.log(n)
            if best is None or margin < best["margin"]:
                best = dict(delta=delta, delta_rel=delta / sd2, lam=lam, margin=margin, closest=e, p=form.n_constants)
        by_n[str(n)] = best
    return dict(cell=cell, p0=p0, sigma_u2=sigma_u2, n_forms=len(forms), n_not_wrong=int(n_not_wrong), by_n=by_n)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--workers", type=int, default=8)
    parser.add_argument("--separation", action="store_true")
    args = parser.parse_args()
    out_file = OUT_DIR / "analysis.jsonl"

    if args.separation:
        forms: dict[str, set] = {}
        ns: dict[str, set] = {}
        for line in out_file.read_text().splitlines():
            r = json.loads(line)
            if "error" in r or r["grid"] not in ("breadth", "nscale"):
                continue
            ck = cell_key(r)
            ns.setdefault(ck, set()).add(r["n"])
            p0 = LAWS[r["law"]].n_constants
            for c in r["candidates"]:
                if c["rel_error_form"] > 1e-3 and c["p"] <= p0:  # wrong, and not excluded by the penalty
                    # Constants as written, so each form is refitted from where its search found it.
                    forms.setdefault(ck, set()).add((c["expr"], c["p"]))
        # One task per (cell, n), largest first, so the n-scaling cells spread over the workers.
        tasks = sorted(((ck, n) for ck in ns for n in ns[ck]), key=lambda t: -len(forms.get(t[0], ())))
        merged: dict[str, dict] = {}
        with ProcessPoolExecutor(args.workers) as pool:
            futures = [pool.submit(separation, ck, sorted(forms.get(ck, ())), [n]) for ck, n in tasks]
            for f in as_completed(futures):
                res = f.result()
                m = merged.setdefault(res["cell"], res | {"by_n": {}})
                m["by_n"].update(res["by_n"])
                m["n_not_wrong"] = max(m["n_not_wrong"], res["n_not_wrong"])
        results = list(merged.values())
        (OUT_DIR / "separation.json").write_text(json.dumps(results, indent=1))
        print(f"separation: {len(results)} cells, {sum(r['n_forms'] for r in results)} wrong formulas", flush=True)
        return

    runs = [json.loads(line) for f in sorted(OUT_DIR.glob("runs-*.jsonl")) for line in f.read_text().splitlines() if line.strip()]
    done = set()
    if out_file.exists():
        done = {key(r) for r in map(json.loads, out_file.read_text().splitlines()) if "error" not in r}
    todo = [r for r in runs if key(r) not in done and not r["errors"]]
    print(f"analysis: {len(todo)} runs to do ({len(done)} done, {sum(bool(r['errors']) for r in runs)} runs with search errors skipped)", flush=True)
    with ProcessPoolExecutor(args.workers) as pool, out_file.open("a") as f:
        futures = [pool.submit(_safe, r) for r in todo]
        for i, fut in enumerate(as_completed(futures), 1):
            res = fut.result()
            f.write(json.dumps(res) + "\n")
            f.flush()
            if i % 25 == 0 or "error" in res:
                print(f"[{i}/{len(todo)}] {res['grid']} {res['design']} {res['law']} n={res['n']} seed={res['seed']}"
                      + (" ERROR " + res["error"].strip().splitlines()[-1] if "error" in res else ""), flush=True)


if __name__ == "__main__":
    main()
