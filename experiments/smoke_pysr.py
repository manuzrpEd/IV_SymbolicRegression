"""End-to-end smoke run: plain PySR vs. symbolic IV on one design and law.

Checks the pipeline (search -> MMSC selection -> recovery -> diagnosis), not
performance: one seed and a small search budget. Phase 2 does the real study.

    python experiments/smoke_pysr.py --design D1 --law power --n 2000
"""

from __future__ import annotations

import argparse
import time

from symiv.criteria import gmm_criterion
from symiv.diagnostics import diagnose
from symiv.dgp import simulate
from symiv.metrics import relative_error
from symiv.recovery import form_recovered
from symiv.search import fit_symbolic_iv, pareto_front, plain_regressor
from symiv.selection import select_mmsc


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--design", default="D1")
    parser.add_argument("--law", default="power")
    parser.add_argument("--n", type=int, default=2000)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--niterations", type=int, default=40)
    parser.add_argument("--maxsize", type=int, default=15)
    args = parser.parse_args()

    s = simulate(args.design, args.law, n=args.n, seed=args.seed)
    crit = gmm_criterion(s.Z)
    search = dict(niterations=args.niterations, maxsize=args.maxsize)
    print(f"{args.design} / {args.law}: f0 = {s.law.expr}   (n = {s.n}, K = {crit.K})\n")

    t = time.time()
    plain = plain_regressor(**search)
    plain.fit(s.X, s.y)
    best_mse = plain.sympy()
    print(f"Plain PySR ({time.time() - t:.0f}s), PySR's own pick: {best_mse}")
    print(
        f"  recovers the form of f0: {form_recovered(best_mse, s.law, s.X).recovered}; "
        f"||f_hat - f0|| / sd(f0) = {relative_error(best_mse, s.law, s.X):.3f}\n"
    )

    t = time.time()
    model = fit_symbolic_iv(s.X, s.y, crit, **search)
    exprs, complexities = pareto_front(model)
    sel = select_mmsc(exprs, s.X, s.y, crit, complexities=complexities)
    print(f"Symbolic IV ({time.time() - t:.0f}s), Pareto front scored by MMSC (best first):")
    for c in sel.candidates:
        print(f"  MMSC {c.mmsc:9.2f}  J {c.fit.J:8.2f}  p {c.n_constants}  {c.fitted_expr}")
    d = diagnose(sel.best, s.law, s.X, s.y, crit)
    print(f"\nSelected: {sel.best.fitted_expr}")
    print(f"  ||f_hat - f0|| / sd(f0) = {relative_error(sel.best.fitted_expr, s.law, s.X):.3f}")
    print(f"Outcome: {d.outcome}  (MMSC selected {d.mmsc_selected:.2f}, true form {d.mmsc_true:.2f})")


if __name__ == "__main__":
    main()
