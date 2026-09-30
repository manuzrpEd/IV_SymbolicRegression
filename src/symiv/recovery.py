"""Did the search recover the true law? (README §8.1, metrics)

Two checks:

- `form_recovered` (primary): the found formula's *form* reproduces f0 exactly
  once its constants are refit to the noise-free f0, and it has no more
  constants than f0. Robust to algebraic rearrangement (log(c x^k) vs a + b log x)
  and to estimation noise in the constants.
- `srbench_solution`: the SymPy criterion of SRBench (La Cava et al. 2021) on the
  expression as found. Estimated constants rarely match exactly, so on noisy
  data this is mainly a sanity check.
"""

from __future__ import annotations

from dataclasses import dataclass

import numpy as np
import sympy as sp
from scipy.optimize import least_squares

from symiv.dgp.laws import Law
from symiv.expressions import canonical, parametrize


@dataclass
class Recovery:
    recovered: bool
    rel_error: float  # best RMSE / sd(f0) the found form can reach (constants refit to f0)
    n_constants: int
    n_constants_true: int
    srbench: bool | None  # None when the expression was too large to simplify


def form_recovered(
    expr: sp.Expr | str,
    law: Law,
    X: np.ndarray,
    rtol: float = 1e-4,
    n_starts: int = 8,
    max_points: int = 2000,
    seed: int = 0,
) -> Recovery:
    rng = np.random.default_rng(seed)
    if len(X) > max_points:
        X = X[rng.choice(len(X), size=max_points, replace=False)]
    form = parametrize(expr, law.dim)
    target = law(X)
    scale = target.std() if target.std() > 0 else 1.0

    def residuals(theta):
        r = (form(X, theta) - target) / scale
        return np.where(np.isfinite(r), r, 1e6)

    p = form.n_constants
    if p == 0:
        best = residuals(np.empty(0))
    else:
        starts = [form.values] + [
            form.values * (1 + 0.5 * rng.standard_normal(p)) + 0.5 * rng.standard_normal(p) for _ in range(n_starts - 1)
        ]
        fits = [least_squares(residuals, s) for s in starts]
        best = min(fits, key=lambda f: f.cost).fun
    rel_error = float(np.sqrt(np.mean(best**2)))
    return Recovery(
        recovered=rel_error < rtol and p <= law.n_constants,
        rel_error=rel_error,
        n_constants=p,
        n_constants_true=law.n_constants,
        srbench=srbench_solution(expr, law.expr, law.dim),
    )


def _is_constant(e: sp.Expr) -> bool:
    return not e.free_symbols and e.is_finite is not False


def srbench_solution(expr_hat: sp.Expr | str, expr_true: sp.Expr | str, d: int, max_ops: int = 80) -> bool | None:
    """f_hat is a symbolic solution if it is not constant and f - f_hat or f_hat / f simplifies to a constant."""
    e_hat, e_true = canonical(expr_hat, d), canonical(expr_true, d)
    if sp.count_ops(e_hat) > max_ops:
        return None
    if not e_hat.free_symbols:
        return False
    diff = sp.simplify(sp.expand_log(e_true - e_hat, force=True))
    if _is_constant(diff):
        return True
    ratio = sp.simplify(sp.expand_log(e_hat / e_true, force=True))
    return bool(_is_constant(ratio) and ratio != 0)


def symbolically_equal(e1: sp.Expr | str, e2: sp.Expr | str, d: int, atol: float = 1e-9) -> bool:
    """True if e1 - e2 simplifies to (numerically) zero."""
    diff = sp.simplify(sp.expand_log(canonical(e1, d) - canonical(e2, d), force=True))
    return not diff.free_symbols and abs(complex(diff)) < atol
