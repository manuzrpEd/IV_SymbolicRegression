"""Nonparametric IV baselines for positive regressors: sieve 2SLS (any number) and kernel IV (one) (README §8.1).

Both return a callable f_hat(X) and no formula.
"""

from __future__ import annotations

import warnings
from dataclasses import dataclass
from math import comb

import numpy as np
from scipy.linalg import LinAlgWarning, solve
from sklearn.pipeline import make_pipeline
from sklearn.preprocessing import PolynomialFeatures, SplineTransformer, StandardScaler

from symiv.criteria import MomentCriterion
from symiv.criteria.instruments import as_2d, gaussian_kernel, median_bandwidth


def _log_regressor(X: np.ndarray) -> np.ndarray:
    X = as_2d(X)
    if X.shape[1] != 1:
        raise ValueError("kernel IV here takes one regressor")
    return np.log(X)


# ----------------------------------------------------------------- sieve 2SLS


def _basis(J: int, d: int):
    """One regressor: J cubic B-splines in log x, continued linearly outside the data.
    Several: all monomials of standardized log x up to total degree J (a product law needs interactions)."""
    if d == 1:
        return SplineTransformer(n_knots=J - 2, degree=3, knots="quantile", extrapolation="linear", include_bias=True)
    return make_pipeline(StandardScaler(), PolynomialFeatures(degree=J, include_bias=True))


def _n_columns(J: int, d: int) -> int:
    return J if d == 1 else comb(J + d, d)


def _sieve_2sls(Psi: np.ndarray, y: np.ndarray, A: np.ndarray) -> np.ndarray:
    """argmin_beta ||A'(y - Psi beta)||^2."""
    return np.linalg.lstsq(A.T @ Psi, A.T @ y, rcond=None)[0]


@dataclass
class SieveIV:
    basis: object  # fitted transformer of log x
    beta: np.ndarray
    J: int  # number of splines (one regressor) or polynomial degree (several)

    def __call__(self, X: np.ndarray) -> np.ndarray:
        return self.basis.transform(np.log(as_2d(X))) @ self.beta


def fit_sieve_iv(
    X: np.ndarray,
    y: np.ndarray,
    crit: MomentCriterion,
    J: int | None = None,
    J_grid=None,
    folds: int = 5,
    seed: int = 0,
) -> SieveIV:
    """Series 2SLS in log x with the criterion's instruments.

    J (with no more sieve terms than instruments) is chosen by the moment
    criterion on held-out folds when not given. Default grid: 4-10 splines for
    one regressor, total degree 1-4 for several.
    """
    t = np.log(as_2d(X))
    d = t.shape[1]
    grid = [j for j in (J_grid or (range(4, 11) if d == 1 else range(1, 5))) if _n_columns(j, d) <= crit.K]
    if J is None:
        J = min(grid, key=lambda j: _cv_moment_loss(t, y, crit.A, j, folds, seed))
    basis = _basis(J, d).fit(t)
    return SieveIV(basis, _sieve_2sls(basis.transform(t), y, crit.A), J)


def _cv_moment_loss(t, y, A, J, folds, seed) -> float:
    fold = np.random.default_rng(seed).permutation(len(y)) % folds
    total = 0.0
    for k in range(folds):
        train, val = fold != k, fold == k
        basis = _basis(J, t.shape[1]).fit(t[train])
        beta = _sieve_2sls(basis.transform(t[train]), y[train], A[train])
        g = A[val].T @ (y[val] - basis.transform(t[val]) @ beta)
        total += g @ g / val.sum()
    return total


# ----------------------------------------------------------------- kernel IV


@dataclass
class KernelIV:
    """Kernel IV (Singh, Sahani & Gretton 2019) on standardized log x."""

    t_train: np.ndarray
    alpha: np.ndarray
    bandwidth: float
    t_mean: float
    t_sd: float
    lam: float
    xi: float

    def __call__(self, X: np.ndarray) -> np.ndarray:
        t = (_log_regressor(X) - self.t_mean) / self.t_sd
        return gaussian_kernel(t, self.t_train, self.bandwidth) @ self.alpha


def fit_kiv(
    X: np.ndarray,
    y: np.ndarray,
    Z: np.ndarray,
    seed: int = 0,
    lambdas: np.ndarray = np.logspace(-8, 0, 17),
    xis: np.ndarray = np.logspace(-8, 0, 17),
) -> KernelIV:
    """KIV with the paper's sample split and tuning.

    Stage 1 (first half) learns the conditional mean embedding of x given z with
    ridge penalty lambda, tuned on the second half's x. Stage 2 (second half's y)
    learns h with penalty xi, tuned by predicting the first half's y from its z.
    Gaussian kernels on standardized log x and z, median-heuristic bandwidths.
    """
    t_all = _log_regressor(X)
    t_mean, t_sd = float(t_all.mean()), float(t_all.std())
    t_all = (t_all - t_mean) / t_sd
    z_all = as_2d(Z)
    z_all = (z_all - z_all.mean(0)) / np.where(z_all.std(0) > 0, z_all.std(0), 1.0)

    rng = np.random.default_rng(seed)
    perm = rng.permutation(len(y))
    one, two = perm[: len(y) // 2], perm[len(y) // 2 :]
    n, m = len(one), len(two)
    t1, t2, z1, z2, y1, y2 = t_all[one], t_all[two], z_all[one], z_all[two], y[one], y[two]
    hx, hz = median_bandwidth(t_all, rng), median_bandwidth(z_all, rng)

    K_XX = gaussian_kernel(t1, t1, hx)
    K_X2 = gaussian_kernel(t1, t2, hx)
    K_ZZ = gaussian_kernel(z1, z1, hz)
    K_Z2 = gaussian_kernel(z1, z2, hz)
    s, V = np.linalg.eigh(K_ZZ)
    VtK_Z2, VtK_ZZ = V.T @ K_Z2, V.T @ K_ZZ

    def gamma(lam, VtK):  # (K_ZZ + n lam I)^{-1} K
        return V @ (VtK / (s + n * lam)[:, None])

    def stage1_loss(lam):  # mean RKHS distance between phi(x2_j) and mu_hat(z2_j); k(x, x) = 1
        G = gamma(lam, VtK_Z2)
        return (m - 2 * np.sum(K_X2 * G) + np.sum(G * (K_XX @ G))) / m

    lam = min(lambdas, key=stage1_loss)
    W = K_XX @ gamma(lam, VtK_Z2)  # n x m
    Gamma1 = gamma(lam, VtK_ZZ)  # n x n, embeddings of the first half's z

    def stage2(xi):
        with warnings.catch_warnings():  # tiny xi is ill-conditioned by design; tuning rejects it
            warnings.simplefilter("ignore", LinAlgWarning)
            return solve(W @ W.T + m * xi * K_XX + 1e-10 * np.eye(n), W @ y2, assume_a="sym")

    def stage2_loss(xi):
        alpha = stage2(xi)
        return np.mean((y1 - Gamma1.T @ (K_XX @ alpha)) ** 2)

    xi = min(xis, key=stage2_loss)
    return KernelIV(t1, stage2(xi), hx, t_mean, t_sd, float(lam), float(xi))
