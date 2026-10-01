"""Phase 5, the identification diagnostic on the Phase 4 runs (THEORY.md Proposition 5).

    python experiments/phase5_identification.py --workers 8     -> experiments/phase5/identification.jsonl

For every Phase 4 breadth run: the pooled candidates and the formula selected from them by
BIC + structure, on the run's own data. `symiv.identification.identification_report` then gives
the first-stage F, the AR intervals of the selected formula's constants, the S statistic of every
other candidate, the confidence set of formulas and the verdict. Recorded with the run's outcome:
recovered, statistical failure (the true form was a candidate but lost) or search failure (it was
not a candidate), and whether the true form is in the confidence set (Proposition 5 says it is
with probability >= 95% whenever it is a candidate).
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

sys.path.insert(0, str(Path(__file__).parent))
from phase4 import default_criterion  # noqa: E402

from symiv.dgp import simulate  # noqa: E402
from symiv.identification import identification_report  # noqa: E402

OUT_DIR = Path(__file__).parent / "phase5"
P4 = Path(__file__).parent / "phase4"
SET, RULE = "pooled", "bic_s05"


def work(rec: dict) -> dict:
    warnings.filterwarnings("ignore")
    s = simulate(rec["design"], rec["law"], n=rec["n"], seed=rec["seed"], **rec["params"])
    crit = default_criterion(s)
    cands = [c for c in rec["candidates"] if SET in c["sets"]]
    sel = rec["select"][SET][RULE]
    rep = identification_report(sel["expr"], [c["expr"] for c in cands], s.X, s.y, crit, seed=rec["seed"])
    recovered_of = {c["expr"]: c["recovered"] for c in cands}
    truth_candidate = any(c["recovered"] for c in cands)
    outcome = "recovered" if sel["recovered"] else ("statistical failure" if truth_candidate else "search failure")
    in_set = [ch for ch in rep.candidates if ch.in_set]
    # The true form is in the confidence set if the selected formula has it and is not rejected, or another member has it.
    truth_in_set = (sel["recovered"] and rep.S_selected <= rep.critical) or any(recovered_of.get(ch.expr, False) for ch in in_set)
    return {k: rec[k] for k in ("design", "law", "seed", "n", "params")} | dict(
        outcome=outcome, verdict=rep.verdict, reasons=rep.reasons, first_stage_F=rep.first_stage.F,
        S_selected=rep.S_selected, critical=rep.critical, ar_bounded=rep.ar_bounded, width_ratio=rep.width_ratio,
        max_distance=rep.max_distance, n_in_set=len(in_set), n_candidates=len(rep.candidates),
        truth_candidate=truth_candidate, truth_in_set=bool(truth_in_set),
        distances=[(ch.distance, ch.distance_full, bool(recovered_of.get(ch.expr, False))) for ch in in_set],
        selected=rep.selected, rel_error=sel["rel_error"])


def _safe(rec):
    try:
        return work(rec)
    except Exception:
        return {k: rec[k] for k in ("design", "law", "seed")} | {"error": traceback.format_exc()}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--workers", type=int, default=8)
    parser.add_argument("--limit", type=int, default=None)
    args = parser.parse_args()
    OUT_DIR.mkdir(exist_ok=True)
    recs = [json.loads(line) for line in (P4 / "analysis.jsonl").read_text().splitlines() if line.strip()]
    recs = [r for r in recs if "error" not in r and r["grid"] == "breadth"][: args.limit]
    print(f"identification: {len(recs)} runs", flush=True)
    n_err = 0
    with ProcessPoolExecutor(args.workers) as pool, (OUT_DIR / "identification.jsonl").open("w") as f:
        futures = [pool.submit(_safe, r) for r in recs]
        for i, fut in enumerate(as_completed(futures), 1):
            row = fut.result()
            n_err += "error" in row
            f.write(json.dumps(row) + "\n")
            if i % 25 == 0:
                print(f"[{i}/{len(recs)}]", flush=True)
    print(f"done; {n_err} errors", flush=True)


if __name__ == "__main__":
    main()
