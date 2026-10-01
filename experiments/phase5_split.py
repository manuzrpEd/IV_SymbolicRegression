"""Phase 5, test of Corollary 2.3: candidates generated on one sample, selected on another.

    python experiments/phase5_split.py --workers 8     -> experiments/phase5/split.jsonl

Uses the Phase 4 n-scaling fronts (D1 strong, power and log laws, 12 seeds) from the three PySR
generators (plain, one-step, distilled). For each run at n = 1000 (sample A), every candidate is
refitted and selected
- on A itself (same-sample selection, as in Phase 4), and
- on each of R = 5 fresh samples B of n = 1000, independent of A (split selection: the candidates
  were not fitted to B's noise, so Theorem 2's union bound runs over the candidates, not over all
  trees).
The same-sample selection at n = 2000 (fronts generated and selected on one sample of 2000, same
seeds) is the full-sample reference. Rules: MMSC-BIC and BIC + structure (w = 0.5). Beaters: wrong
candidates whose BIC score on the selection sample beats the true form's.
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
import sympy as sp  # noqa: E402

sys.path.insert(0, str(Path(__file__).parent))
from phase4 import default_criterion  # noqa: E402
from phase4_analysis import N_SYMBOLS  # noqa: E402

from symiv.dgp import simulate  # noqa: E402
from symiv.expressions import parametrize  # noqa: E402
from symiv.gmm import fit_gmm  # noqa: E402
from symiv.selection import mmsc  # noqa: E402

OUT_DIR = Path(__file__).parent / "phase5"
P4 = Path(__file__).parent / "phase4"
R = 5
GENS = ("plain", "onestep", "distill")


def select(run: dict, info: dict, seed: int, label: str) -> list[dict]:
    """Refit the run's candidates on the sample drawn with `seed` and select there."""
    warnings.filterwarnings("ignore")
    s = simulate(run["design"], run["law"], n=run["n"], seed=seed, **run["params"])
    X, y, n, law = s.X, s.y, s.n, s.law
    crit = default_criterion(s)
    kappa_s = np.log(N_SYMBOLS[run["ops"]] + X.shape[1])
    true_bic = mmsc(fit_gmm(law.parametric, X, y, crit, theta0=np.array(law.values)), n, "bic")
    cands: dict[str, set] = {}
    for g in GENS:
        for e in run["fronts"].get(g, {}).get("exprs", []):
            cands.setdefault(str(sp.sympify(e)), set()).add(g)
    scored = []
    for c, gens in cands.items():
        form = parametrize(c, X.shape[1])
        fit = fit_gmm(form, X, y, crit, n_starts=4, seed=run["seed"])
        bic = mmsc(fit, n, "bic") if np.isfinite(fit.J) else np.inf
        scored.append(dict(expr=c, gens=gens, bic=bic, s05=bic + 0.5 * info[c]["nodes"] * kappa_s, **info[c]))
    out = []
    for set_name, members in (("pooled", scored), ("distill", [c for c in scored if "distill" in c["gens"]])):
        for rule in ("bic", "s05"):
            best = min(members, key=lambda c: (c[rule], c["p"], c["nodes"]))
            out.append(dict(law=run["law"], seed=run["seed"], n=n, sample=label, set=set_name, rule=rule,
                            recovered=bool(best["recovered"]), expr=best["expr"],
                            coverage=any(c["recovered"] for c in members), n_candidates=len(members),
                            beaters=int(sum(c["rel_error_form"] > 1e-3 and c["bic"] < true_bic for c in members))))
    return out


def _safe(args):
    try:
        return select(*args)
    except Exception:
        run, _, seed, label = args
        return [dict(law=run["law"], seed=run["seed"], n=run["n"], sample=label, error=traceback.format_exc())]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--workers", type=int, default=8)
    args = parser.parse_args()
    OUT_DIR.mkdir(exist_ok=True)
    runs = [json.loads(line) for f in sorted(P4.glob("runs-nscale-*.jsonl")) for line in f.read_text().splitlines() if line.strip()]
    runs = [r for r in runs if r["n"] in (1000, 2000)]
    analysis = {}
    for line in (P4 / "analysis.jsonl").read_text().splitlines():
        r = json.loads(line)
        if "error" not in r and r["grid"] == "nscale" and r["n"] in (1000, 2000):
            analysis[(r["law"], r["n"], r["seed"])] = {c["expr"]: {k: c[k] for k in ("recovered", "rel_error_form", "p", "nodes")}
                                                      for c in r["candidates"]}
    tasks = []
    for run in runs:
        info = analysis[(run["law"], run["n"], run["seed"])]
        tasks.append((run, info, run["seed"], "A"))
        if run["n"] == 1000:
            tasks += [(run, info, 200_000 + 100 * run["seed"] + k, f"B{k}") for k in range(R)]
    print(f"split: {len(tasks)} selections", flush=True)
    n_err = 0
    with ProcessPoolExecutor(args.workers) as pool, (OUT_DIR / "split.jsonl").open("w") as f:
        futures = [pool.submit(_safe, t) for t in tasks]
        for i, fut in enumerate(as_completed(futures), 1):
            for row in fut.result():
                n_err += "error" in row
                f.write(json.dumps(row) + "\n")
            if i % 25 == 0:
                print(f"[{i}/{len(tasks)}]", flush=True)
    print(f"done; {n_err} errors", flush=True)


if __name__ == "__main__":
    main()
