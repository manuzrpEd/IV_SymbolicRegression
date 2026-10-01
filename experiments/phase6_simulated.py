"""Phase 6, simulated economic environments (README §8.2): demand with a cost shifter; backward-bending labour supply.

    python experiments/phase6_simulated.py --part search [--shard 0 --of 2]   # PySR; resumable
    python experiments/phase6_simulated.py --part analyze --workers 8        # selection, metrics, identification report
    python experiments/phase6_simulated.py --part report                     # phase6/summary.md

Environments (20 seeds each, n = 2000):
- demand:  design D6. Quantity = f0(price) + u; the price is set by equilibrium with a supply curve shifted by the
           cost shifter Z. Laws: demand_iso 3 p^-0.5, demand_log 6 - 1.5 log p (in the library), demand_hyper 6/(1 + p).
- labour:  design D1 with pi = 0.5. Hours = f0(wage) + u; unobserved taste for work raises both hours and the wage;
           Z is an exogenous wage shifter. Laws: hump 8 w exp(-0.5 w), quadlog 5 + 2 log w - 0.6 log(w)^2 (in the library).
- labour_strong: the control: pi = 1 and quadlog_mid 5 + 0.5 log w - 0.6 log(w)^2, whose peak is at the median wage.
Candidates: plain PySR and PySR distilled from a sieve-2SLS curve (the paper's generators), plus the library path.
Selection by MMSC-BIC and BIC + structure (Phase 4 analysis code); the identification report of Proposition 5 on the pick.
"""

from __future__ import annotations

import os

for _v in ("OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "OMP_NUM_THREADS"):
    os.environ.setdefault(_v, "1")

import argparse  # noqa: E402
import json  # noqa: E402
import sys  # noqa: E402
import time  # noqa: E402
import traceback  # noqa: E402
import warnings  # noqa: E402
from collections import defaultdict  # noqa: E402
from concurrent.futures import ProcessPoolExecutor, as_completed  # noqa: E402
from pathlib import Path  # noqa: E402

import numpy as np  # noqa: E402

sys.path.insert(0, str(Path(__file__).parent))
from phase2_report import med, wilson  # noqa: E402
from phase4 import default_criterion, key, run  # noqa: E402
from phase4_analysis import analyze  # noqa: E402

from symiv.dgp import simulate  # noqa: E402
from symiv.gmm import fit_gmm  # noqa: E402
from symiv.identification import identification_report  # noqa: E402
from symiv.metrics import elasticity, relative_error  # noqa: E402

OUT_DIR = Path(__file__).parent / "phase6"
SEEDS = 20
ENVIRONMENTS = {
    "demand": dict(design="D6", params={}, laws=("demand_iso", "demand_log", "demand_hyper")),
    "labour": dict(design="D1", params={"pi": 0.5}, laws=("hump", "quadlog")),
    # Control: a strong shifter (pi = 1), and a quadratic whose peak is at the median wage, so the bend is in the data.
    "labour_strong": dict(design="D1", params={"pi": 1.0}, laws=("hump", "quadlog_mid")),
}
LAWS = {"demand_iso": "3 p^-0.5", "demand_log": "6 - 1.5 log p", "demand_hyper": "6 / (1 + p)",
        "hump": "8 w exp(-0.5 w)", "quadlog": "5 + 2 log w - 0.6 (log w)^2", "quadlog_mid": "5 + 0.5 log w - 0.6 (log w)^2"}


def units():
    for grid, env in ENVIRONMENTS.items():
        for law in env["laws"]:
            for seed in range(SEEDS):
                yield dict(grid=grid, design=env["design"], law=law, n=2000, seed=seed, setting="default",
                           params=env["params"], ops="default", gens=["plain", "distill"])


def search(args) -> None:
    OUT_DIR.mkdir(exist_ok=True)
    done = {key(json.loads(line)) for f in OUT_DIR.glob("runs-*.jsonl") for line in f.read_text().splitlines() if line.strip()}
    todo = [u for i, u in enumerate(units()) if i % args.of == args.shard and key(u) not in done]
    out_file = OUT_DIR / f"runs-{args.shard}.jsonl"
    print(f"search shard {args.shard}/{args.of}: {len(todo)} runs to do", flush=True)
    for i, u in enumerate(todo, 1):
        t = time.time()
        rec = run(u)
        with out_file.open("a") as f:
            f.write(json.dumps(rec) + "\n")
        errs = f" errors: {sorted(rec['errors'])}" if rec["errors"] else ""
        print(f"[{i}/{len(todo)}] {u['grid']} {u['law']:12s} seed={u['seed']:2d} {time.time() - t:5.0f}s{errs}", flush=True)
    print("search done", flush=True)


def _analyze(rec: dict) -> dict:
    warnings.filterwarnings("ignore")
    try:
        out = analyze(rec)
        s = simulate(rec["design"], rec["law"], n=rec["n"], seed=rec["seed"], **rec["params"])
        crit = default_criterion(s)
        x_med = float(np.median(s.X[:, 0]))
        oracle = fit_gmm(s.law.parametric, s.X, s.y, crit, theta0=np.array(s.law.values))
        out["oracle"] = dict(rel_error=relative_error(s.law.parametric.expr(oracle.theta), s.law, s.X),
                             elasticity=elasticity(s.law.parametric.expr(oracle.theta), x_med))
        out["true_elasticity"] = elasticity(s.law.expr, x_med)
        sel = out["select"]["pooled"]["bic_s05"]
        cands = [c["expr"] for c in out["candidates"] if "pooled" in c["sets"]]
        rep = identification_report(sel["expr"], cands, s.X, s.y, crit, seed=rec["seed"])
        out["identification"] = dict(verdict=rep.verdict, reasons=rep.reasons[:3], first_stage_F=rep.first_stage.F,
                                     S=rep.S_selected, critical=rep.critical, max_distance=rep.max_distance,
                                     n_in_set=len(rep.formula_set) - 1, n_candidates=len(rep.candidates),
                                     ar_intervals=rep.ar_intervals, wald_se=rep.se, width_ratio=rep.width_ratio)
        return out
    except Exception:
        return {k: rec[k] for k in ("grid", "design", "law", "n", "seed")} | {"error": traceback.format_exc()}


def analyze_all(args) -> None:
    runs = [json.loads(line) for f in sorted(OUT_DIR.glob("runs-*.jsonl")) for line in f.read_text().splitlines() if line.strip()]
    out_file = OUT_DIR / "analysis.jsonl"
    done = set()
    if out_file.exists() and not args.recompute:
        done = {key(r) for r in map(json.loads, out_file.read_text().splitlines()) if "error" not in r}
    todo = [r for r in runs if key(r) not in done and not r["errors"]]
    print(f"analysis: {len(todo)} runs to do ({len(done)} done)", flush=True)
    with ProcessPoolExecutor(args.workers) as pool, out_file.open("w" if args.recompute else "a") as f:
        futures = [pool.submit(_analyze, r) for r in todo]
        for i, fut in enumerate(as_completed(futures), 1):
            res = fut.result()
            f.write(json.dumps(res) + "\n")
            f.flush()
            if i % 10 == 0 or "error" in res:
                print(f"[{i}/{len(todo)}] {res['grid']} {res['law']} seed={res['seed']}"
                      + (" ERROR " + res["error"].strip().splitlines()[-1] if "error" in res else ""), flush=True)


def pct(xs) -> str:
    xs = list(xs)
    return f"{100 * np.mean(xs):.0f}%" if xs else "–"


def report(args) -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    rows = [json.loads(line) for line in (OUT_DIR / "analysis.jsonl").read_text().splitlines() if line.strip()]
    errors = [r for r in rows if "error" in r]
    rows = [r for r in rows if "error" not in r]
    L = []
    w = L.append
    w("# Phase 6: simulated economic environments\n")
    w(f"Generated by `experiments/phase6_simulated.py` from {len(rows)} analysed runs ({len(errors)} errors), {SEEDS} seeds per law, "
      "n = 2000. Candidates: plain PySR, PySR distilled from a sieve-2SLS curve, and the library path, pooled. "
      "Recovery = the selected formula has the true form; errors are RMS(f̂ − f₀) in units of the in-sample sd of f₀; "
      "extrapolation on [q99, 3 q99] of the regressor. Elasticities at the median regressor (median over seeds).\n")
    w("| Environment | Law | Plain PySR, own pick: recovered / error | Pooled + MMSC-BIC | **Pooled + BIC + structure** | "
      "Error: pooled + structure / oracle IV | Extrapolation error | Library path + MMSC | Any candidate has the form | "
      "Elasticity at the median: truth / selected | Identification: identified / weak / rejected | First-stage F, median |")
    w("|---|---|---|---|---|---|---|---|---|---|---|---|")
    for grid, env in ENVIRONMENTS.items():
        for law in env["laws"]:
            rs = [r for r in rows if r["grid"] == grid and r["law"] == law]
            if not rs:
                continue
            sel = lambda k, rule="bic_s05": [r["select"][k][rule] for r in rs if r["select"].get(k)]
            ident = [r["identification"]["verdict"] for r in rs]
            w(f"| {grid} | {LAWS[law]} | {pct(r['pysr_pick']['plain']['recovered'] for r in rs)} / "
              f"{med(r['pysr_pick']['plain']['rel_error'] for r in rs)} | "
              f"{wilson(sum(x['recovered'] for x in sel('pooled', 'bic')), len(rs))} | "
              f"**{wilson(sum(x['recovered'] for x in sel('pooled')), len(rs))}** | "
              f"{med(x['rel_error'] for x in sel('pooled'))} / {med(r['oracle']['rel_error'] for r in rs)} | "
              f"{med(x['extrap_error'] for x in sel('pooled'))} | "
              f"{pct(x['recovered'] for x in sel('library', 'bic'))} | {pct(r['coverage']['pooled'] for r in rs)} | "
              f"{np.median([r['true_elasticity'] for r in rs]):.2f} / {med(x['elasticity'] for x in sel('pooled') if x['elasticity'] is not None)} | "
              f"{pct(v == 'identified' for v in ident)} / {pct(v == 'weakly identified' for v in ident)} / {pct(v == 'rejected' for v in ident)} | "
              f"{np.median([r['identification']['first_stage_F'][0] for r in rs]):.0f} |")
    w("")
    w("**Selected formulas** (pooled + BIC + structure), most frequent form per law:\n")
    for grid, env in ENVIRONMENTS.items():
        for law in env["laws"]:
            rs = [r for r in rows if r["grid"] == grid and r["law"] == law]
            forms = defaultdict(int)
            for r in rs:
                e = r["select"]["pooled"]["bic_s05"]["expr"]
                forms[next((c["form"] for c in r["candidates"] if c["expr"] == e), e)] += 1
            top = sorted(forms.items(), key=lambda kv: -kv[1])[:3]
            w(f"- {grid}, {LAWS[law]}: " + "; ".join(f"`{f}` ({k}/{len(rs)})" for f, k in top))
    (OUT_DIR / "summary.md").write_text("\n".join(L) + "\n", encoding="utf-8")
    print("\n".join(L))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--part", choices=["search", "analyze", "report"], required=True)
    parser.add_argument("--shard", type=int, default=0)
    parser.add_argument("--of", type=int, default=1)
    parser.add_argument("--workers", type=int, default=8)
    parser.add_argument("--recompute", action="store_true", help="analyze: ignore the saved analysis and rewrite it")
    args = parser.parse_args()
    warnings.filterwarnings("ignore")
    {"search": search, "analyze": analyze_all, "report": report}[args.part](args)


if __name__ == "__main__":
    main()
