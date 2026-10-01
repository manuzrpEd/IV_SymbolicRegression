"""A simplified SRIT-style baseline (Yan et al., SSRN 6879831; README §3.1).

The original is not runnable here: its code link (github.com/Super-SUM-Plus/SRIT)
returned 404 on 2026-09-30, and it used the commercial Eureqa engine. This keeps
SRIT's core idea with PySR as the engine: offer all observed variables (X and Z)
as candidate inputs; drop an input when the residuals of the SR model without it
are independent of it (HSIC permutation test, Benjamini-Hochberg within a round,
threshold 0.10 as in the paper); repeat; fit the final formula on what remains.
It assumes no unobserved confounders, which the designs here violate.
"""

from __future__ import annotations

from dataclasses import dataclass

import numpy as np
import sympy as sp

from symiv.criteria.instruments import gaussian_kernel, median_bandwidth
from symiv.expressions import parametrize, variables
from symiv.selection import select_ls


def hsic_pvalue(a: np.ndarray, b: np.ndarray, n_perm: int = 200, max_points: int = 800, seed: int = 0) -> float:
    """Permutation p-value of the HSIC independence test (Gaussian kernels, median bandwidths)."""
    rng = np.random.default_rng(seed)
    idx = rng.choice(len(a), size=min(len(a), max_points), replace=False)
    a, b = a[idx, None], b[idx, None]
    m = len(a)
    H = np.eye(m) - 1.0 / m
    Kc = H @ gaussian_kernel(a, a, median_bandwidth(a, rng)) @ H
    L = gaussian_kernel(b, b, median_bandwidth(b, rng))
    stat = np.sum(Kc * L)
    null = [np.sum(Kc * L[np.ix_(p, p)]) for p in (rng.permutation(m) for _ in range(n_perm))]
    return (1 + sum(s >= stat for s in null)) / (n_perm + 1)


def _benjamini_hochberg(p: dict[int, float]) -> dict[int, float]:
    keys = sorted(p, key=p.get)
    k = len(keys)
    adjusted, running = {}, 1.0
    for rank, key in reversed(list(enumerate(keys, 1))):
        running = min(running, p[key] * k / rank)
        adjusted[key] = running
    return adjusted


@dataclass
class SRITFit:
    retained: list[str]  # names of the inputs kept, from "x" and "z"
    expr: sp.Expr  # final formula in x0 (= X) and x1 (= Z)
    structural_expr: sp.Expr  # expr with Z at its sample mean: the formula's implied f(x)


def fit_srit_style(X: np.ndarray, Z: np.ndarray, y: np.ndarray, alpha: float = 0.10, seed: int = 0, **search) -> SRITFit:
    from symiv.search import pareto_front, plain_regressor

    W = np.column_stack([X[:, 0], Z[:, 0]])
    names = {0: "x", 1: "z"}
    x0, x1 = variables(2)

    def sr(cols: list[int]) -> sp.Expr:
        model = plain_regressor(**search)
        model.fit(W[:, cols], y, variable_names=[f"x{c}" for c in cols])
        exprs, cx = pareto_front(model)
        return select_ls(exprs, W, y, cx).best.fitted_expr

    retained, fits = [0, 1], {}
    while len(retained) > 1:
        pvals = {}
        for j in retained:
            rest = [k for k in retained if k != j]
            fits[tuple(rest)] = sr(rest)
            residual = y - parametrize(fits[tuple(rest)], 2)(W)
            pvals[j] = hsic_pvalue(residual, W[:, j], seed=seed)
        adjusted = _benjamini_hochberg(pvals)
        j = max(adjusted, key=adjusted.get)
        if adjusted[j] <= alpha:
            break  # every remaining input matters
        retained.remove(j)
    expr = fits[tuple(retained)] if tuple(retained) in fits else sr(retained)
    structural = expr.xreplace({x1: sp.Float(float(W[:, 1].mean()))})
    return SRITFit([names[k] for k in retained], expr, structural)
