"""Tables for the Phase 5 simulations -> experiments/phase5/summary.md.

Reads phase5/inference.jsonl (Theorem 1 (iii): inference on an independent sample) and
phase5/split.jsonl (Corollary 2.3: candidates from one sample, selection on another).
"""

from __future__ import annotations

import json
import sys
from collections import defaultdict
from pathlib import Path

import numpy as np

from phase2_report import wilson

HERE = Path(__file__).parent
OUT = HERE / "phase5"
LAWS = {"log": "1 + 2 log x", "power": "2 x^0.7", "kink": "x - 0.8 max(x - 1.5, 0)", "saturation": "3x / (1 + x)",
        "cobb_douglas": "1.5 x1^0.3 x2^0.5"}
DESIGNS = {"D1": "D1 confounding", "D2": "D2 heterosk. first stage", "D3": "D3 simultaneity",
           "D4": "D4 discrete Z (J = 4)", "D5": "D5 weak Z (π = 0.1)"}


def pct(xs) -> str:
    xs = [x for x in xs if x is not None]
    return f"{100 * np.mean(xs):.0f}%" if xs else "–"


def rate(xs) -> str:
    xs = [x for x in xs if x is not None]
    return wilson(sum(xs), len(xs)) if xs else "–"


def inference_section(w) -> None:
    rows = [json.loads(line) for line in (OUT / "inference.jsonl").read_text().splitlines() if line.strip()]
    errors = [r for r in rows if "error" in r]
    rows = [r for r in rows if "error" not in r]
    w("## 1. Inference after selection (Theorem 1 (iii))\n")
    w(f"{len(rows)} GMM fits from {len({(r['design'], r['law'], r['seed']) for r in rows})} Phase 4 breadth runs "
      f"({len(errors)} errors). Trees: the law's own form (oracle) and, where the pooled candidates with BIC + structure "
      "selected a formula of the true form on the Phase 4 sample A, that formula (selected). Each tree is estimated by "
      "two-step efficient GMM on 10 fresh samples B (independent of A) and on A itself. Coverage is of nominal 95% "
      "Wald intervals: for the constants (pooled over the tree's constants), for f at the median and the 90th percentile "
      "of X, and for the elasticity at the median (one regressor). J: rejection rate of Hansen's test at 5%. AR: coverage "
      "of the Anderson–Rubin set at the true constants (needs no rank condition). Fits per cell in the last column.\n")
    w("| Design | Law | Tree | Sample | Constants | f(median) | f(q90) | Elasticity | J rejects | AR covers | Fits |")
    w("|---|---|---|---|---|---|---|---|---|---|---|")
    groups = defaultdict(list)
    for r in rows:
        groups[(r["design"], r["law"], r["tree"], "A" if r["sample"] == "A" else "B")].append(r)
    for design in DESIGNS:
        for law in LAWS:
            for tree in ("oracle", "selected"):
                for sample in ("B", "A"):
                    g = groups.get((design, law, tree, sample))
                    if not g:
                        continue
                    consts = [c for r in g for c in r["cover"]]
                    tg = lambda name: [r["targets"][name]["cover"] for r in g if name in r["targets"]]
                    w(f"| {DESIGNS[design]} | {LAWS[law]} | {tree} | {'fresh B' if sample == 'B' else 'same A'} | "
                      f"{pct(consts)} | {pct(tg('f_med'))} | {pct(tg('f_q90'))} | {pct(tg('elas_med'))} | "
                      f"{pct(r['J_reject'] for r in g)} | {pct(r['AR_cover'] for r in g)} | {len(g)} |")
    w("")
    w("**By design, all laws pooled** (95% Wilson intervals for the coverage of the constants):\n")
    w("| Design | Tree | Sample | Constants | f(median) | Elasticity | J rejects | AR covers | SE calibration | Fits |")
    w("|---|---|---|---|---|---|---|---|---|---|")
    by_design = defaultdict(list)
    for r in rows:
        by_design[(r["design"], r["tree"], "A" if r["sample"] == "A" else "B")].append(r)
    for design in DESIGNS:
        for tree in ("oracle", "selected"):
            for sample in ("B", "A"):
                g = by_design.get((design, tree, sample))
                if not g:
                    continue
                consts = [c for r in g for c in r["cover"]]
                # SE calibration: sd of (theta_hat - theta0) across fresh samples over the mean reported SE, per (run, constant).
                cal = []
                if sample == "B":
                    per = defaultdict(list)
                    for r in g:
                        per[(r["law"], r["seed"], r["expr"])].append((np.array(r["theta"]) - np.array(r["theta0"]), np.array(r["se"])))
                    for v in per.values():
                        if len(v) >= 5:
                            dev = np.array([x[0] for x in v])
                            se = np.array([x[1] for x in v])
                            cal.extend((dev.std(axis=0) / np.maximum(se.mean(axis=0), 1e-12)).tolist())
                w(f"| {DESIGNS[design]} | {tree} | {'fresh B' if sample == 'B' else 'same A'} | {rate(consts)} | "
                  f"{pct(r['targets']['f_med']['cover'] for r in g)} | "
                  f"{pct(r['targets']['elas_med']['cover'] for r in g if 'elas_med' in r['targets'])} | "
                  f"{pct(r['J_reject'] for r in g)} | {pct(r['AR_cover'] for r in g)} | "
                  + (f"{np.median(cal):.2f}" if cal else "–") + f" | {len(g)} |")
    w("\nSE calibration: median over (run, constant) of the standard deviation of θ̂ − θ₀ across the 10 fresh samples, "
      "divided by the mean reported standard error (1 = calibrated; > 1 = the standard errors are too small).\n")
    uniq = [r["unique"] for r in rows if r["tree"] == "selected" and r["sample"] == "A"]
    if uniq:
        w(f"Point zero sets: {pct(uniq)} of the selected trees had a unique set of constants reproducing f₀ "
          "(every refit from random starts that reached f₀ ended at the same point), as (A5)(a) requires.\n")


def split_section(w) -> None:
    rows = [json.loads(line) for line in (OUT / "split.jsonl").read_text().splitlines() if line.strip()]
    errors = [r for r in rows if "error" in r]
    rows = [r for r in rows if "error" not in r]
    w("## 2. Candidates from one sample, selection on another (Corollary 2.3)\n")
    w(f"{len(rows)} selections ({len(errors)} errors). D1 strong (π = 0.7, ρ = 1.2), 12 seeds. Candidates: the plain, "
      "one-step and distilled PySR fronts of the Phase 4 n-scaling runs (pooled, and the distilled front alone). "
      "Same-sample: selected on the sample the fronts were fitted to. Split: the n = 1000 fronts, selected on 5 fresh "
      "samples of n = 1000 each (60 selections per cell from 12 independent candidate sets). Reference: same-sample "
      "selection at n = 2000. Beaters: wrong candidates whose BIC score on the selection sample beats the true form's.\n")
    w("| Law | Set | Rule | Same-sample, n = 1000 | **Split: 1000 + 1000** | Same-sample, n = 2000 | Beaters: same-sample 1000 / split / same-sample 2000 |")
    w("|---|---|---|---|---|---|---|")
    g = defaultdict(list)
    for r in rows:
        g[(r["law"], r["set"], r["rule"], r["n"], "A" if r["sample"] == "A" else "B")].append(r)
    for law in ("power", "log"):
        for set_name in ("pooled", "distill"):
            for rule, label in (("bic", "MMSC-BIC"), ("s05", "BIC + structure")):
                a1, b1, a2 = g[(law, set_name, rule, 1000, "A")], g[(law, set_name, rule, 1000, "B")], g[(law, set_name, rule, 2000, "A")]
                beat = " / ".join(f"{np.mean([r['beaters'] for r in x]):.2f}" if x else "–" for x in (a1, b1, a2))
                w(f"| {LAWS[law]} | {set_name} | {label} | {rate(r['recovered'] for r in a1)} | **{rate(r['recovered'] for r in b1)}** | "
                  f"{rate(r['recovered'] for r in a2)} | {beat} |")
    w("")
    # paired: per (law, seed, set, rule) the same-sample outcome vs the fraction of split successes
    w("Coverage (a candidate of the true form exists) is a property of the candidate set, the same for same-sample and "
      "split selection of the same run: " + ", ".join(
          f"{LAWS[law]} {100 * np.mean([r['coverage'] for r in g[(law, 'pooled', 'bic', 1000, 'A')]]):.0f}%" for law in ("power", "log")) + " at n = 1000.\n")


def identification_section(w) -> None:
    rows = [json.loads(line) for line in (OUT / "identification.jsonl").read_text().splitlines() if line.strip()]
    errors = [r for r in rows if "error" in r]
    rows = [r for r in rows if "error" not in r]
    TAU = 0.2  # the module's default; verdicts are recomputed here from the stored statistics

    def verdict_at(r, tau):
        if r["S_selected"] > r["critical"]:
            return "rejected"
        if not all(r["ar_bounded"]) or any(d > tau for d, _, _ in r["distances"]):
            return "weakly identified"
        return "identified"

    for r in rows:
        r["verdict"] = verdict_at(r, TAU)
    w("## 3. The identification diagnostic on the Phase 4 runs (Proposition 5)\n")
    w(f"{len(rows)} runs ({len(errors)} errors): every Phase 4 breadth run, the pooled candidates and the formula selected "
      "from them by BIC + structure, on the run's own data. Verdicts: *identified*; *weakly identified* (an AR interval of "
      f"a constant reaches the bound, or a candidate the data do not reject is more than τ = {TAU} sd from the selected formula "
      "in the trimmed metric); *rejected* (the selected formula fails its own S test). Outcome of the run: recovered, "
      "statistical failure (the true form was a candidate but lost) or search failure (it was not a candidate). "
      "Flagged = weakly identified or rejected.\n")
    w("| Design | Runs | Identified | Weakly identified | Rejected | First-stage F, median | Farthest member of the set (sd), median | Candidates not rejected, median |")
    w("|---|---|---|---|---|---|---|---|")
    for design in DESIGNS:
        g = [r for r in rows if r["design"] == design]
        if not g:
            continue
        w(f"| {DESIGNS[design]} | {len(g)} | {pct(r['verdict'] == 'identified' for r in g)} | "
          f"{pct(r['verdict'] == 'weakly identified' for r in g)} | {pct(r['verdict'] == 'rejected' for r in g)} | "
          f"{np.median([r['first_stage_F'][0] for r in g]):.0f} | {np.median([r['max_distance'] for r in g]):.2f} | "
          f"{np.median([r['n_in_set'] / max(r['n_candidates'], 1) for r in g]) * 100:.0f}% |")
    w("")
    w("**By the run's outcome** (D1–D4 and D5 separately; 95% Wilson intervals):\n")
    w("| Designs | Outcome | Runs | Flagged | Of which: rejected | True form in the confidence set |")
    w("|---|---|---|---|---|---|")
    for designs, label in ((("D1", "D2", "D3", "D4"), "D1–D4"), (("D5",), "D5")):
        for outcome in ("recovered", "statistical failure", "search failure"):
            g = [r for r in rows if r["design"] in designs and r["outcome"] == outcome]
            if not g:
                continue
            cov = [r["truth_in_set"] for r in g if r["truth_candidate"]]
            w(f"| {label} | {outcome} | {len(g)} | {rate(r['verdict'] != 'identified' for r in g)} | "
              f"{pct(r['verdict'] == 'rejected' for r in g)} | {rate(cov)} |")
    w("")
    cov_all = [r["truth_in_set"] for r in rows if r["truth_candidate"]]
    w(f"Proposition 5 (a): across all {len(cov_all)} runs in which the true form was a candidate, it is in the confidence set "
      f"in {rate(cov_all)} (nominal ≥ 95%).\n")
    w("**Threshold sensitivity.** Share of runs flagged for other values of τ (the AR-bound and rejection criteria unchanged):\n")
    w("| τ (sd) | D1–D4, recovered (false alarms) | D1–D4, statistical failures | D1–D4, search failures | D5, all |")
    w("|---|---|---|---|---|")

    def flagged(r, tau):
        return verdict_at(r, tau) != "identified"

    for tau in (0.05, 0.1, 0.2, 0.3, 0.5):
        cells = []
        for designs, outcome in ((("D1", "D2", "D3", "D4"), "recovered"), (("D1", "D2", "D3", "D4"), "statistical failure"),
                                 (("D1", "D2", "D3", "D4"), "search failure"), (("D5",), None)):
            g = [r for r in rows if r["design"] in designs and (outcome is None or r["outcome"] == outcome)]
            cells.append(pct(flagged(r, tau) for r in g))
        w(f"| {tau} | " + " | ".join(cells) + " |")
    w("")


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    L = []
    w = L.append
    w("# Phase 5 simulations\n")
    w("Generated by `experiments/phase5_report.py` from `phase5_inference.py`, `phase5_split.py` and "
      "`phase5_identification.py`. They reuse the Phase 4 Pareto fronts; no new searches.\n")
    if (OUT / "inference.jsonl").exists():
        inference_section(w)
    if (OUT / "split.jsonl").exists():
        split_section(w)
    if (OUT / "identification.jsonl").exists():
        identification_section(w)
    (OUT / "summary.md").write_text("\n".join(L) + "\n", encoding="utf-8")
    print("\n".join(L))


if __name__ == "__main__":
    main()
