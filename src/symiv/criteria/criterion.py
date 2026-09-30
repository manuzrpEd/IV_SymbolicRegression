"""The moment criterion Q_n(f) = ||A' r||^2 / n shared by GMM and kernel MMR (README §6.2)."""

from __future__ import annotations

from dataclasses import dataclass

import numpy as np

from symiv.criteria.instruments import (
    as_2d,
    default_n_instruments,
    gaussian_kernel,
    nystrom_features,
    orthonormalize,
    polynomial_basis,
    spline_basis,
    standardize,
)


@dataclass(frozen=True)
class MomentCriterion:
    """Q_n(f) = ||A' r||^2 / n for residuals r = y - f(X).

    kind="gmm": A is an orthonormal basis of the instrument columns B, so Q_n is
        the GMM criterion with 2SLS weights, g' (B'B/n)^{-1} g with g = B'r/n.
    kind="mmr": A = Phi / sqrt(n) with Phi Phi' ~= K_Z, so Q_n ~= r' K_Z r / n^2.

    Either way sqrt(n) * A are the instruments for efficient GMM and J statistics.
    """

    A: np.ndarray
    kind: str

    @property
    def n(self) -> int:
        return self.A.shape[0]

    @property
    def K(self) -> int:
        """Number of unconditional moments (columns of A)."""
        return self.A.shape[1]

    def moments(self, residuals: np.ndarray) -> np.ndarray:
        return self.A.T @ residuals

    def value(self, residuals: np.ndarray) -> float:
        g = self.moments(residuals)
        return float(g @ g) / len(residuals)


def gmm_criterion(Z: np.ndarray, K: int | None = None, basis: str = "spline", degree: int = 3) -> MomentCriterion:
    """Criterion (b): sieve instruments with 2SLS weights.

    basis="spline": additive cubic B-splines, about K columns (default grows like n^(1/3)).
    basis="poly": all monomials up to total `degree` (captures interactions when Z has several columns).
    """
    Z = as_2d(Z)
    if basis == "spline":
        B = spline_basis(Z, K or default_n_instruments(len(Z)))
    elif basis == "poly":
        B = polynomial_basis(Z, degree)
    else:
        raise ValueError(f"basis must be 'spline' or 'poly', not {basis!r}")
    return MomentCriterion(orthonormalize(B), "gmm")


def mmr_criterion(Z: np.ndarray, m: int = 100, bandwidth: float | None = None, seed: int = 0) -> MomentCriterion:
    """Criterion (c): kernel MMR with a rank-m Nystrom approximation of the Gaussian kernel."""
    Phi, _ = nystrom_features(Z, m=m, bandwidth=bandwidth, seed=seed)
    return MomentCriterion(Phi / np.sqrt(len(Phi)), "mmr")


def exact_mmr(Z: np.ndarray, residuals: np.ndarray, bandwidth: float) -> float:
    """r' K_Z r / n^2 with the full kernel matrix. O(n^2); for checking the Nystrom version."""
    Zs = standardize(Z)
    return float(residuals @ gaussian_kernel(Zs, Zs, bandwidth) @ residuals) / len(residuals) ** 2
