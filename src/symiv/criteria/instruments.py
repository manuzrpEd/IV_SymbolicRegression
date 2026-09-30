"""Instrument functions b(Z): sieve bases for GMM and Nystrom features for kernel MMR (README §6.2)."""

from __future__ import annotations

import numpy as np
from sklearn.preprocessing import PolynomialFeatures, SplineTransformer


def as_2d(Z: np.ndarray) -> np.ndarray:
    Z = np.asarray(Z, dtype=float)
    return Z[:, None] if Z.ndim == 1 else Z


def standardize(Z: np.ndarray) -> np.ndarray:
    Z = as_2d(Z)
    sd = Z.std(axis=0)
    return (Z - Z.mean(axis=0)) / np.where(sd > 0, sd, 1.0)


def default_n_instruments(n: int) -> int:
    """K grows with n (README §6.2): about n^(1/3), and never fewer than 8."""
    return int(max(8, round(n ** (1 / 3))))


def polynomial_basis(Z: np.ndarray, degree: int = 3) -> np.ndarray:
    """All monomials of standardized Z up to total `degree`, including the intercept."""
    return PolynomialFeatures(degree=degree, include_bias=True).fit_transform(standardize(Z))


def spline_basis(Z: np.ndarray, K: int) -> np.ndarray:
    """Additive cubic B-splines with quantile knots, about K columns in total.

    A column with few distinct values (a discrete instrument) gets one dummy per
    value instead, which is the saturated instrument set for that column.
    """
    Z = standardize(Z)
    n, d = Z.shape
    n_knots = max(2, int(np.ceil(K / d)) - 2)  # cubic B-splines: n_knots + 2 columns per variable
    blocks = [np.ones((n, 1))]
    for j in range(d):
        col = Z[:, [j]]
        values = np.unique(col)
        if len(values) <= n_knots + 2:
            blocks.append((col == values[None, :]).astype(float))
        else:
            spline = SplineTransformer(n_knots=n_knots, degree=3, knots="quantile", include_bias=True)
            blocks.append(spline.fit_transform(col))
    return np.hstack(blocks)


def orthonormalize(B: np.ndarray, rtol: float = 1e-8) -> np.ndarray:
    """Orthonormal basis A of the column space of B, dropping collinear directions."""
    U, s, _ = np.linalg.svd(B, full_matrices=False)
    return U[:, s > rtol * s[0]]


def median_bandwidth(Z: np.ndarray, rng: np.random.Generator, max_points: int = 1000) -> float:
    """Median pairwise distance (the median heuristic), on a subsample."""
    idx = rng.choice(len(Z), size=min(len(Z), max_points), replace=False)
    S = Z[idx]
    dist = np.sqrt(((S[:, None, :] - S[None, :, :]) ** 2).sum(-1))
    positive = dist[np.triu_indices(len(S), k=1)]
    positive = positive[positive > 0]
    return float(np.median(positive)) if positive.size else 1.0


def gaussian_kernel(Z1: np.ndarray, Z2: np.ndarray, bandwidth: float) -> np.ndarray:
    sq = ((Z1[:, None, :] - Z2[None, :, :]) ** 2).sum(-1)
    return np.exp(-sq / (2.0 * bandwidth**2))


def nystrom_features(
    Z: np.ndarray, m: int = 100, bandwidth: float | None = None, seed: int = 0
) -> tuple[np.ndarray, float]:
    """Features Phi (n, r) with Phi Phi' ~= K_Z for a Gaussian kernel on standardized Z.

    Returns (Phi, bandwidth). Landmarks are m random rows; r <= m after dropping
    null directions of the landmark kernel matrix (e.g. repeated discrete values).
    """
    Zs = standardize(Z)
    rng = np.random.default_rng(seed)
    h = bandwidth if bandwidth is not None else median_bandwidth(Zs, rng)
    landmarks = Zs[rng.choice(len(Zs), size=min(m, len(Zs)), replace=False)]
    C = gaussian_kernel(Zs, landmarks, h)
    w, V = np.linalg.eigh(gaussian_kernel(landmarks, landmarks, h))
    keep = w > 1e-10 * w.max()
    return C @ (V[:, keep] / np.sqrt(w[keep])), h
