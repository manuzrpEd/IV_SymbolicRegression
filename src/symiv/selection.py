"""Choosing a formula from the Pareto front with GMM model selection criteria (README §6.3)."""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass, replace

import numpy as np
import sympy as sp

from symiv._lsq import robust_least_squares
from symiv.criteria import MomentCriterion
from symiv.expressions import ParametricForm, parametrize
from symiv.gmm import GMMFit, fit_gmm

# Andrews & Lu (2001) penalty rates kappa_n. BIC and HQIC give consistent selection; AIC does not.
PENALTIES = {
    "bic": lambda n: np.log(n),
    "hqic": lambda n: 2.01 * np.log(np.log(n)),
    "aic": lambda n: 2.0,
}


def mmsc(fit: GMMFit, n: int, penalty: str = "bic") -> float:
    """MMSC_n = J - (K - p) kappa_n. Lower is better.

    With K fixed across candidates this is J + p kappa_n up to a constant: each
    extra free constant must lower J by more than kappa_n to be kept.
    """
    return fit.J - fit.df * PENALTIES[penalty](n)


@dataclass
class Candidate:
    expr: sp.Expr  # as found by the search
    form: ParametricForm
    fit: GMMFit
    mmsc: float
    complexity: int | None = None

    @property
    def n_constants(self) -> int:
        return self.form.n_constants

    @property
    def fitted_expr(self) -> sp.Expr:
        """The formula with its constants replaced by the efficient GMM estimates."""
        return self.form.expr(self.fit.theta)


@dataclass
class LSCandidate:
    """A formula scored by least squares, for plain SR (the biased baseline)."""

    expr: sp.Expr
    form: ParametricForm
    theta: np.ndarray
    rss: float
    ic: float  # n log(RSS / n) + p kappa_n
    complexity: int | None = None

    @property
    def n_constants(self) -> int:
        return self.form.n_constants

    @property
    def fitted_expr(self) -> sp.Expr:
        return self.form.expr(self.theta)


@dataclass
class Selection:
    best: Candidate | LSCandidate
    candidates: list  # all candidates, best first


def score(
    expr: sp.Expr | str,
    X: np.ndarray,
    y: np.ndarray,
    crit: MomentCriterion,
    penalty: str = "bic",
    bound: float = 10.0,
    complexity: int | None = None,
    theta0: np.ndarray | None = None,
    n_starts: int = 4,
    seed: int = 0,
) -> Candidate:
    """Refit a formula's constants by two-step GMM and compute its MMSC."""
    form = parametrize(expr, X.shape[1])
    fit = fit_gmm(form, X, y, crit, bound=bound, theta0=theta0, n_starts=n_starts, seed=seed)
    value = mmsc(fit, len(y), penalty) if np.isfinite(fit.J) else np.inf
    return Candidate(sp.sympify(expr), form, fit, value, complexity)


def select_mmsc(
    exprs: Sequence[sp.Expr | str],
    X: np.ndarray,
    y: np.ndarray,
    crit: MomentCriterion,
    complexities: Sequence[int] | None = None,
    penalty: str = "bic",
    bound: float = 10.0,
    n_starts: int = 4,
    seed: int = 0,
) -> Selection:
    """Score every candidate and pick the lowest MMSC.

    Ties are broken by fewer constants, then lower search complexity (node count
    only breaks ties; README §6.3).
    """
    complexities = list(complexities) if complexities is not None else [None] * len(exprs)
    candidates = [
        score(e, X, y, crit, penalty=penalty, bound=bound, complexity=c, n_starts=n_starts, seed=seed)
        for e, c in zip(exprs, complexities)
    ]
    candidates.sort(key=lambda c: (c.mmsc, c.n_constants, c.complexity or 0))
    return Selection(candidates[0], candidates)


def rerank(selection: Selection, n: int, penalty: str) -> Selection:
    """The same MMSC-scored candidates, ranked under another penalty (no refitting)."""
    rescored = [replace(c, mmsc=mmsc(c.fit, n, penalty) if np.isfinite(c.fit.J) else np.inf) for c in selection.candidates]
    rescored.sort(key=lambda c: (c.mmsc, c.n_constants, c.complexity or 0))
    return Selection(rescored[0], rescored)


def select_ls(
    exprs: Sequence[sp.Expr | str],
    X: np.ndarray,
    y: np.ndarray,
    complexities: Sequence[int] | None = None,
    penalty: str = "bic",
) -> Selection:
    """Plain-SR selection: refit constants by least squares (unbounded, as plain PySR),
    then pick the lowest n log(RSS / n) + p kappa_n, with the same kappa_n as MMSC."""
    n = len(y)
    complexities = list(complexities) if complexities is not None else [None] * len(exprs)
    candidates = []
    for e, c in zip(exprs, complexities):
        form = parametrize(e, X.shape[1])

        def residuals(theta, form=form):
            r = y - form(X, theta)
            return np.where(np.isfinite(r), r, 1e6)

        fit = robust_least_squares(residuals, form.values) if form.n_constants else None
        theta = fit.x if fit is not None else form.values
        r = y - form(X, theta)
        rss = float(r @ r) if np.all(np.isfinite(r)) else np.inf
        ic = n * np.log(rss / n) + form.n_constants * PENALTIES[penalty](n) if np.isfinite(rss) else np.inf
        candidates.append(LSCandidate(sp.sympify(e), form, theta, rss, ic, c))
    candidates.sort(key=lambda c: (c.ic, c.n_constants, c.complexity or 0))
    return Selection(candidates[0], candidates)
