"""Accuracy of a found formula against the true law (README §8.1, metrics).

Errors are in units of the in-sample standard deviation of f0, so in-sample and
extrapolation errors are comparable across laws and designs.
"""

from __future__ import annotations

import numpy as np
import sympy as sp

from symiv._lsq import robust_least_squares
from symiv.dgp.laws import Law
from symiv.expressions import parametrize


def relative_error(expr: sp.Expr | str, law: Law, X: np.ndarray) -> float:
    """RMS(f_hat - f0) / sd(f0) on the rows of X; inf where f_hat is undefined."""
    f0, fh = law(X), parametrize(expr, law.dim)(X)
    if not np.all(np.isfinite(fh)):
        return np.inf
    return float(np.sqrt(np.mean((fh - f0) ** 2)) / f0.std())


def extrapolation_grid(X: np.ndarray, quantile: float = 0.99, factor: float = 3.0, size: int = 200) -> np.ndarray:
    """Points beyond the training support: log-spaced from the `quantile` of each regressor to `factor` times it."""
    q = np.quantile(X, quantile, axis=0)
    return q * factor ** np.linspace(0.0, 1.0, size)[:, None]


def extrapolation_error(expr: sp.Expr | str, law: Law, X_train: np.ndarray) -> float:
    """RMS(f_hat - f0) on the extrapolation grid, in units of the in-sample sd(f0)."""
    G = extrapolation_grid(X_train)
    f0, fh = law(G), parametrize(expr, law.dim)(G)
    if not np.all(np.isfinite(fh)):
        return np.inf
    return float(np.sqrt(np.mean((fh - f0) ** 2)) / law(X_train).std())


def elasticity(expr: sp.Expr | str, x: float, h: float = 1e-4) -> float:
    """x f'(x) / f(x) of a one-regressor formula, by central differences."""
    lo, mid, hi = parametrize(expr, 1)(np.array([[x * (1 - h)], [x], [x * (1 + h)]]))
    return float((hi - lo) / (2 * h * mid))


def implied_constants(expr: sp.Expr | str, law: Law, X: np.ndarray) -> np.ndarray:
    """Constants of the true form that best reproduce f_hat on X (noise-free least squares).

    When f_hat has the true form, these are its constants in the true
    parametrization (e.g. x**0.709/0.479 -> a = 2.09, theta = 0.709).
    """
    fh = parametrize(expr, law.dim)(X)
    if not np.all(np.isfinite(fh)):
        return np.full(law.n_constants, np.nan)
    form = law.parametric

    def residuals(theta):
        r = form(X, theta) - fh
        return np.where(np.isfinite(r), r, 1e6)

    fit = robust_least_squares(residuals, np.array(law.values))
    return fit.x if fit is not None else np.full(law.n_constants, np.nan)
