"""Before the paper (README §11): can a larger search budget, or a fixed template library, reach the three-constant
and threshold laws that the Phase 2-6 budget rarely proposed?

    python experiments/phase7_budget.py --part search [--limit N]   # PySR with the large budget; resumable
    python experiments/phase7_budget.py --part analyze --workers 8  # four arms per run (pure Python; resumable)
    python experiments/phase7_budget.py --part report               # phase7/budget.md

Cells, paired with the saved runs (same data, same seeds):
- D1 and D3 x {kink, saturation}, n = 2000, seeds 0-11 (the Phase 4 breadth runs)
- labour supply: D1 with pi = 0.5 x quadlog, D1 with pi = 1 x quadlog_mid, n = 2000, seeds 0-19 (the Phase 6 runs)

Budgets:
- base:  40 iterations, 31 populations, maximum size 15 (Phases 2-6), read from the saved fronts
- large: 200 iterations, 40 populations, maximum size 25, two restarts with different seeds, fronts pooled
Generators: plain PySR and PySR distilled from the sieve-2SLS curve (the cheap generators the applications use);
the library path joins every pool. The one-step front of the saved Phase 4 runs is left out so the arms compare.

Arms: base, base + templates, large, large + templates. Templates = the fixed library of symiv.templates, scored
like any other candidate (two-step GMM refit, MMSC with the structure term).
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
from phase4 import DISTILL_POINTS, SEARCH, default_criterion  # noqa: E402
from phase4 import OUT_DIR as PHASE4_DIR  # noqa: E402
from phase4_analysis import analyze  # noqa: E402
from phase4_report import mcnemar  # noqa: E402

from symiv.baselines import fit_sieve_iv  # noqa: E402
from symiv.dgp import simulate  # noqa: E402
from symiv.expressions import parametrize  # noqa: E402
from symiv.templates import template_candidates  # noqa: E402

HERE = Path(__file__).parent
OUT_DIR = HERE / "phase7"
PHASE6_DIR = HERE / "phase6"
LARGE = dict(niterations=200, populations=40, maxsize=25, temp_equation_file=True)
SMOKE = dict(niterations=2, populations=4, maxsize=15, temp_equation_file=True)
RESTARTS = 2
ARMS = ("base", "base_tmpl", "large", "large_tmpl")
ARM_LABEL = {"base": "Base budget", "base_tmpl": "Base + templates", "large": "Large budget", "large_tmpl": "Large + templates"}
CELLS = {  # cell -> (source grid, design, params, laws, seeds)
    "D1": ("breadth", "D1", {}, ("kink", "saturation"), range(12)),
    "D3": ("breadth", "D3", {}, ("kink", "saturation"), range(12)),
    "labour": ("labour", "D1", {"pi": 0.5}, ("quadlog",), range(20)),
    "labour_strong": ("labour_strong", "D1", {"pi": 1.0}, ("quadlog_mid",), range(20)),
}
LAWS = {"kink": "x − 0.8 max(x − 1.5, 0)", "saturation": "3x / (1 + x)", "quadlog": "5 + 2 log w − 0.6 (log w)²",
        "quadlog_mid": "5 + 0.5 log w − 0.6 (log w)²"}
CELL_LABEL = {"D1": "D1 confounding", "D3": "D3 simultaneity", "labour": "Labour, π = 0.5", "labour_strong": "Labour, π = 1"}


def units():
    for cell, (_, design, params, laws, seeds) in CELLS.items():
        for law in laws:
            for seed in seeds:
                yield dict(grid="budget", cell=cell, design=design, law=law, n=2000, seed=seed, setting="default",
                           params=params, ops="default", gens=["plain", "distill"])


def ukey(u: dict) -> tuple:
    return (u["cell"], u["law"], u["seed"])


def baseline_records() -> dict[tuple, dict]:
    """The saved Phase 4 / Phase 6 search records of the cells, keyed like the units."""
    recs = {}
    files = list(PHASE4_DIR.glob("runs-breadth-*.jsonl")) + list(PHASE6_DIR.glob("runs-*.jsonl"))
    for f in files:
        for line in f.read_text().splitlines():
            if not line.strip():
                continue
            r = json.loads(line)
            for cell, (grid, design, params, laws, seeds) in CELLS.items():
                if r["grid"] == grid and r["design"] == design and r["law"] in laws and r["seed"] in seeds and r["params"] == params:
                    recs[(cell, r["law"], r["seed"])] = r
    return recs


# ------------------------------------------------------------------ search


def run(u: dict, budget: dict, restarts: int) -> dict:
    from symiv.search import pareto_front, plain_regressor

    s = simulate(u["design"], u["law"], n=u["n"], seed=u["seed"], **u["params"])
    crit = default_criterion(s)
    X, y = s.X, s.y
    out = dict(u, K=crit.K, budget=budget, restarts=restarts, fronts={}, times={}, errors={})

    def search(name, target):
        t = time.time()
        try:
            exprs, cx, picks = [], [], []
            for k in range(restarts):
                model = plain_regressor(**budget, random_state=1000 * u["seed"] + k)
                model.fit(X if name == "plain" else target[0], y if name == "plain" else target[1])
                e, c = pareto_front(model)
                exprs += [str(x) for x in e]
                cx += c
                picks.append(str(model.sympy()))
            out["fronts"][name] = dict(exprs=exprs, complexity=cx, pick=picks[0], picks=picks)
        except Exception:
            out["errors"][name] = traceback.format_exc()
        out["times"][name] = time.time() - t

    search("plain", None)
    try:
        curve = fit_sieve_iv(X, y, crit)
        idx = np.random.default_rng(u["seed"]).choice(len(y), size=min(len(y), DISTILL_POINTS), replace=False)
        out["sieve"] = dict(J=curve.J, rel_error=float(np.sqrt(np.mean((curve(X) - s.f0) ** 2)) / s.f0.std()))
        search("distill", (X[idx], curve(X[idx])))
    except Exception:
        out["errors"]["distill"] = traceback.format_exc()
    return out


def search_all(args) -> None:
    args.out_dir.mkdir(parents=True, exist_ok=True)
    out_file = args.out_dir / "runs-budget.jsonl"
    done = set()
    if out_file.exists():
        done = {ukey(json.loads(line)) for line in out_file.read_text().splitlines() if line.strip()}
    todo = [u for u in units() if ukey(u) not in done][: args.limit]
    budget, restarts = (SMOKE, 1) if args.smoke else (LARGE, RESTARTS)
    print(f"budget search: {len(todo)} runs to do ({len(done)} done); budget {budget}, {restarts} restarts", flush=True)
    for i, u in enumerate(todo, 1):
        t = time.time()
        rec = run(u, budget, restarts)
        with out_file.open("a") as f:
            f.write(json.dumps(rec) + "\n")
        errs = f" errors: {sorted(rec['errors'])}" if rec["errors"] else ""
        sizes = " ".join(f"{g}={len(fr['exprs'])}" for g, fr in rec["fronts"].items())
        print(f"[{i}/{len(todo)}] {u['cell']:14s} {u['law']:12s} seed={u['seed']:2d} {time.time() - t:5.0f}s  fronts: {sizes}{errs}", flush=True)
    print("budget search done", flush=True)


# ------------------------------------------------------------------ analysis


def _arm(rec: dict, arm: str) -> dict:
    """One arm: the record's plain and distill fronts (+ library inside `analyze`), with or without the templates."""
    warnings.filterwarnings("ignore")
    r = dict(rec, fronts={g: fr for g, fr in rec["fronts"].items() if g in ("plain", "distill")})
    try:
        out = analyze(r, extra_sets={"templates": template_candidates()} if arm.endswith("_tmpl") else None)
        out = {k: out[k] for k in ("coverage", "n_candidates", "beaters", "select", "candidates", "pysr_pick")}
    except Exception:
        out = {"error": traceback.format_exc()}
    return dict(cell=rec["cell"], law=rec["law"], seed=rec["seed"], arm=arm, times=rec.get("times"), **out)


def analyze_all(args) -> None:
    base = baseline_records()
    large = {}
    f_large = args.out_dir / "runs-budget.jsonl"
    if f_large.exists():
        large = {ukey(r): r for r in map(json.loads, f_large.read_text().splitlines()) if r.get("fronts")}
    out_file = args.out_dir / "analysis.jsonl"
    done = set()
    if out_file.exists():
        done = {(r["cell"], r["law"], r["seed"], r["arm"]) for r in map(json.loads, out_file.read_text().splitlines()) if "error" not in r}
    tasks = []
    for u in units():
        k = ukey(u)
        for arm in ARMS:
            src = large if arm.startswith("large") else base
            if k in src and k + (arm,) not in done:
                tasks.append((dict(src[k], cell=u["cell"]), arm))
    print(f"budget analysis: {len(tasks)} arm-runs to do ({len(done)} done; {len(base)} base and {len(large)} large records)", flush=True)
    with ProcessPoolExecutor(args.workers) as pool, out_file.open("a") as f:
        futures = [pool.submit(_arm, rec, arm) for rec, arm in tasks]
        for i, fut in enumerate(as_completed(futures), 1):
            res = fut.result()
            f.write(json.dumps(res) + "\n")
            f.flush()
            if i % 20 == 0 or "error" in res:
                print(f"[{i}/{len(tasks)}] {res['cell']} {res['law']} seed={res['seed']} {res['arm']}"
                      + (" ERROR " + res["error"].strip().splitlines()[-1] if "error" in res else ""), flush=True)


# ------------------------------------------------------------------ report


def pct(xs) -> str:
    xs = list(xs)
    return f"{100 * np.mean(xs):.0f}%" if xs else "–"


def report(args) -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    rows = [json.loads(line) for line in (args.out_dir / "analysis.jsonl").read_text().splitlines() if line.strip()]
    errors = [r for r in rows if "error" in r]
    rows = {(r["cell"], r["law"], r["seed"], r["arm"]): r for r in rows if "error" not in r}
    searches = {}
    f_large = args.out_dir / "runs-budget.jsonl"
    if f_large.exists():
        searches = {ukey(r): r for r in map(json.loads, f_large.read_text().splitlines())}
    L = []
    w = L.append
    w("# Search budget and templates for the three-constant and threshold laws\n")
    w(f"Generated by `experiments/phase7_budget.py` from {len(rows)} analysed arm-runs ({len(errors)} errors). "
      f"Base budget: {SEARCH['niterations']} iterations, 31 populations, size ≤ {SEARCH['maxsize']} (the Phase 2–6 setting, from the "
      f"saved fronts). Large budget: {LARGE['niterations']} iterations, {LARGE['populations']} populations, size ≤ {LARGE['maxsize']}, "
      f"{RESTARTS} restarts pooled. Generators: plain PySR and distillation; the library path is in every pool; the one-step front "
      "is left out. Templates: the fixed library of `symiv.templates` (11 economic shapes), scored like any candidate. "
      "Coverage = some candidate has the true form; recovery = the selected formula has it (pooled candidates, BIC + structure, "
      "w = 0.5); errors are RMS(f̂ − f₀) in units of the sd of f₀, median over seeds. Rates carry 95% Wilson intervals.\n")

    w("## 1. Coverage and recovery by cell and arm\n")
    w("| Cell | Law | Arm | Runs | Coverage: plain / distill / pooled | Recovery: BIC / **BIC + structure** | Error of the pick | Candidates, median | Search time, median |")
    w("|---|---|---|---|---|---|---|---|---|")
    for cell, (_, _, _, laws, seeds) in CELLS.items():
        for law in laws:
            for arm in ARMS:
                rs = [rows[(cell, law, s, arm)] for s in seeds if (cell, law, s, arm) in rows]
                if not rs:
                    continue
                cov = lambda g: pct(r["coverage"].get(g, False) for r in rs)  # noqa: E731
                rec = lambda rule: wilson(sum(r["select"]["pooled"][rule]["recovered"] for r in rs), len(rs))  # noqa: E731
                if arm.startswith("large"):
                    ts = [sum(searches[(cell, law, r["seed"])]["times"].values()) for r in rs if (cell, law, r["seed"]) in searches]
                else:
                    ts = [sum(v for g, v in (r["times"] or {}).items() if g in ("plain", "distill")) for r in rs]
                w(f"| {CELL_LABEL[cell]} | {LAWS[law]} | {ARM_LABEL[arm]} | {len(rs)} | {cov('plain')} / {cov('distill')} / {cov('pooled')} | "
                  f"{rec('bic')} / **{rec('bic_s05')}** | {med(r['select']['pooled']['bic_s05']['rel_error'] for r in rs)} | "
                  f"{np.median([r['n_candidates']['pooled'] for r in rs]):.0f} | {np.median(ts):.0f} s |")
    w("")

    w("## 2. Paired comparisons (same data and seeds)\n")
    w("Runs gained / lost by the first arm against the second, with the exact McNemar p.\n")
    w("| Cell | Law | Coverage: large vs. base | Recovery: large vs. base | Recovery: base + templates vs. base | Recovery: large + templates vs. base | Recovery: large + templates vs. large |")
    w("|---|---|---|---|---|---|---|")
    totals = defaultdict(lambda: ([], []))
    for cell, (_, _, _, laws, seeds) in CELLS.items():
        for law in laws:
            def paired(a, b, field):
                xs, ys = [], []
                for s in seeds:
                    ka, kb = (cell, law, s, a), (cell, law, s, b)
                    if ka in rows and kb in rows:
                        get = (lambda r: r["coverage"]["pooled"]) if field == "coverage" else (lambda r: r["select"]["pooled"]["bic_s05"]["recovered"])
                        xs.append(get(rows[ka]))
                        ys.append(get(rows[kb]))
                        totals[(a, b, field)][0].append(xs[-1])
                        totals[(a, b, field)][1].append(ys[-1])
                return f"{pct(xs)} vs. {pct(ys)}: {mcnemar(xs, ys)}" if xs else "–"

            w(f"| {CELL_LABEL[cell]} | {LAWS[law]} | {paired('large', 'base', 'coverage')} | {paired('large', 'base', 'recovery')} | "
              f"{paired('base_tmpl', 'base', 'recovery')} | {paired('large_tmpl', 'base', 'recovery')} | {paired('large_tmpl', 'large', 'recovery')} |")
    if totals:
        w("| **All cells** | | " + " | ".join(
            f"{pct(totals[k][0])} vs. {pct(totals[k][1])}: {mcnemar(*totals[k])}" if totals[k][0] else "–"
            for k in (("large", "base", "coverage"), ("large", "base", "recovery"), ("base_tmpl", "base", "recovery"),
                      ("large_tmpl", "base", "recovery"), ("large_tmpl", "large", "recovery"))) + " |")
    w("")

    w("## 3. What was selected with the templates in the pool, most frequent forms\n")
    for arm in ("base_tmpl", "large_tmpl"):
        for cell, (_, _, _, laws, seeds) in CELLS.items():
            for law in laws:
                rs = [rows[(cell, law, s, arm)] for s in seeds if (cell, law, s, arm) in rows]
                if not rs:
                    continue
                forms = defaultdict(int)
                srcs = defaultdict(int)
                for r in rs:
                    e = r["select"]["pooled"]["bic_s05"]["expr"]  # the refitted pick: match its form, not its constants
                    f = str(parametrize(e, 1).form)
                    c = next((c for c in r["candidates"] if c["form"] == f), None)
                    forms[f] += 1
                    if c:
                        srcs[",".join(s for s in c["sets"] if s not in ("pooled", "iv"))] += 1
                top = sorted(forms.items(), key=lambda kv: -kv[1])[:3]
                w(f"- {ARM_LABEL[arm]}, {CELL_LABEL[cell]}, {LAWS[law]}: " + "; ".join(f"`{f}` ({k}/{len(rs)})" for f, k in top)
                  + ". Source of the pick: " + ", ".join(f"{s} {k}" for s, k in sorted(srcs.items(), key=lambda kv: -kv[1])) + ".")
    w("")
    w("## 4. Recovery given coverage, by arm\n")
    w("| Arm | Runs | Coverage | Recovery | Recovery given coverage | Beaters per run (BIC) |")
    w("|---|---|---|---|---|---|")
    for arm in ARMS:
        rs = [r for k, r in rows.items() if k[3] == arm]
        if not rs:
            continue
        cov = [r["coverage"]["pooled"] for r in rs]
        rec = [r["select"]["pooled"]["bic_s05"]["recovered"] for r in rs]
        given = [x for x, c in zip(rec, cov) if c]
        w(f"| {ARM_LABEL[arm]} | {len(rs)} | {pct(cov)} | {pct(rec)} | {pct(given)} | {np.mean([r['beaters']['pooled'] for r in rs]):.1f} |")
    if errors:
        w("\n## Analysis errors\n")
        for r in errors:
            w(f"- {r['cell']} {r['law']} seed={r['seed']} {r['arm']}: `{r['error'].strip().splitlines()[-1]}`")
    (args.out_dir / "budget.md").write_text("\n".join(L) + "\n", encoding="utf-8")
    print("\n".join(L))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--part", choices=["search", "analyze", "report"], required=True)
    parser.add_argument("--limit", type=int, default=None)
    parser.add_argument("--workers", type=int, default=8)
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR)
    parser.add_argument("--smoke", action="store_true", help="a tiny budget, to test the pipeline")
    args = parser.parse_args()
    warnings.filterwarnings("ignore")
    {"search": search_all, "analyze": analyze_all, "report": report}[args.part](args)


if __name__ == "__main__":
    main()
