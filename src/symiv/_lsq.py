"""Least squares that fails soft: formulas from a search can drive a fit into non-finite territory."""

from __future__ import annotations

import numpy as np
from scipy.optimize import OptimizeResult, least_squares


def robust_least_squares(fun, x0: np.ndarray, **kwargs) -> OptimizeResult | None:
    """scipy's least_squares, or None when the fit breaks down (e.g. a non-finite Jacobian)."""
    x0 = np.asarray(x0, dtype=float)
    x0 = np.where(np.isfinite(x0), x0, 1.0)
    try:
        return least_squares(fun, x0, **kwargs)
    except (ValueError, np.linalg.LinAlgError):
        return None
