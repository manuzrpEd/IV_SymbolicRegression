"""Two-step GMM refit of a formula's constants, with Hansen's J statistic (README §6.3)."""

from __future__ import annotations

from dataclasses import dataclass

import numpy as np

from symiv._lsq import robust_least_squares
from symiv.criteria import MomentCriterion
from symiv.expressions import ParametricForm

_INVALID = 1e6  # residual used where a formula is undefined (log of a negative, overflow)


@dataclass
class GMMFit:
    theta: np.ndarray  # efficient two-step estimate
    Q: float  # first-step criterion ||A'r||^2 / n, minimized
    J: float  # Hansen's J with the weight from first-step residuals, at theta
    K: int  # number of moments
    p: int  # number of free constants

    @property
    def df(self) -> int:
        return self.K - self.p


def inverse_sqrt(S: np.ndarray, rtol: float = 1e-10) -> np.ndarray:
    """Symmetric S^{-1/2}, treating directions with tiny eigenvalues as absent."""
    w, V = np.linalg.eigh(S)
    keep = w > rtol * max(w.max(), 0.0)
    return (V[:, keep] / np.sqrt(w[keep])) @ V[:, keep].T


def efficient_weight_sqrt(crit: MomentCriterion, residuals: np.ndarray) -> np.ndarray:
    """S^{-1/2} for moments g_i = sqrt(n) A_i r_i, where S = (1/n) sum g_i g_i' = A' diag(r^2) A."""
    return inverse_sqrt((crit.A * residuals[:, None] ** 2).T @ crit.A)


def hansen_j(crit: MomentCriterion, residuals: np.ndarray, W_sqrt: np.ndarray) -> float:
    """J = n g' S^{-1} g with g = A'r / sqrt(n), i.e. ||S^{-1/2} A'r||^2."""
    m = W_sqrt @ crit.moments(residuals)
    return float(m @ m)


def fit_gmm(
    form: ParametricForm,
    X: np.ndarray,
    y: np.ndarray,
    crit: MomentCriterion,
    bound: float = 10.0,
    theta0: np.ndarray | None = None,
    n_starts: int = 4,
    seed: int = 0,
) -> GMMFit:
    """Refit the constants of `form` by two-step GMM with |theta_j| <= bound.

    Step 1 minimizes Q_n (the criterion PySR searched with) from `theta0`
    (default: the form's own constants) and n_starts - 1 perturbed starts.
    Step 2 minimizes J with the efficient weight from step-1 residuals.
    """
    n, p = len(y), form.n_constants
    lo, hi = -bound, bound

    def residuals(theta):
        r = y - form(X, theta)
        return r if np.all(np.isfinite(r)) else None

    def scaled_moments(theta, W_sqrt):
        r = residuals(theta)
        if r is None:
            return np.full(W_sqrt.shape[0], _INVALID)
        return W_sqrt @ crit.moments(r)

    if p == 0:
        theta = np.empty(0)
        r = residuals(theta)
        if r is None:
            return GMMFit(theta, np.inf, np.inf, crit.K, 0)
        return GMMFit(theta, crit.value(r), hansen_j(crit, r, efficient_weight_sqrt(crit, r)), crit.K, 0)

    rng = np.random.default_rng(seed)
    start = np.asarray(form.values if theta0 is None else theta0, dtype=float)
    starts = [start] + [start * (1 + 0.5 * rng.standard_normal(p)) + 0.1 * rng.standard_normal(p) for _ in range(n_starts - 1)]
    eps = 1e-9 * bound
    starts = [np.clip(s, lo + eps, hi - eps) for s in starts]

    identity = np.eye(crit.K) / np.sqrt(n)  # step 1: ||A'r / sqrt(n)||^2 = Q_n
    fits = [robust_least_squares(scaled_moments, s, args=(identity,), bounds=(lo, hi)) for s in starts]
    fits = [f for f in fits if f is not None]
    if not fits:
        return GMMFit(starts[0], np.inf, np.inf, crit.K, p)
    step1 = min(fits, key=lambda res: res.cost)
    r1 = residuals(step1.x)
    if r1 is None:
        return GMMFit(step1.x, np.inf, np.inf, crit.K, p)

    W_sqrt = efficient_weight_sqrt(crit, r1)
    step2 = robust_least_squares(scaled_moments, np.clip(step1.x, lo + eps, hi - eps), args=(W_sqrt,), bounds=(lo, hi))
    if step2 is None:  # keep the first-step estimate, with J evaluated there
        return GMMFit(step1.x, 2 * step1.cost, hansen_j(crit, r1, W_sqrt), crit.K, p)
    return GMMFit(step2.x, 2 * step1.cost, 2 * step2.cost, crit.K, p)
