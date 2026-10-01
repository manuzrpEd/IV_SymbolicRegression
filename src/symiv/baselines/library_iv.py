"""Library + sparse IV: "SINDy with instruments" (README §3.2, §8.1).

Two-stage regularized IV in the spirit of Lin, Feng & Li (2015): project each
library term on the instrument space, select terms by cross-validated Lasso of y
on the projected terms, then refit the selected formula by two-step GMM.
Recovers a law only if it is linear in its parameters over the library.
"""

from __future__ import annotations

from dataclasses import dataclass

import numpy as np
from sklearn.linear_model import LassoCV
from sklearn.model_selection import KFold

from symiv.criteria import MomentCriterion
from symiv.expressions import parametrize
from symiv.selection import Candidate, score

# A SINDy/PySR-style term library for one positive regressor. Contains log x, not x^0.7.
LIBRARY = ("x0", "x0**2", "sqrt(x0)", "x0**1.5", "1/x0", "log(x0)", "x0*log(x0)", "log(x0)**2", "exp(-x0)")


@dataclass
class LibraryIVFit:
    terms: list[str]  # selected library terms
    candidate: Candidate  # post-Lasso GMM refit of intercept + selected terms


def fit_library_iv(
    X: np.ndarray,
    y: np.ndarray,
    crit: MomentCriterion,
    library: tuple[str, ...] = LIBRARY,
    folds: int = 5,
    seed: int = 0,
    bound: float = 1e3,
) -> LibraryIVFit:
    if crit.kind != "gmm":
        raise ValueError("library IV projects on the instrument space: use a gmm criterion (orthonormal A)")
    Phi = np.column_stack([parametrize(term, X.shape[1])(X) for term in library])
    scale = Phi.std(axis=0)
    Phi_hat = crit.A @ (crit.A.T @ (Phi / scale))  # first stage: fitted values on the instruments
    lasso = LassoCV(cv=KFold(folds, shuffle=True, random_state=seed), fit_intercept=True, max_iter=50_000)
    lasso.fit(Phi_hat, y)

    keep = np.abs(lasso.coef_) > 1e-10
    terms = [t for t, k in zip(library, keep) if k]
    coefs = lasso.coef_[keep] / scale[keep]
    expr = " + ".join([repr(float(lasso.intercept_))] + [f"{float(c)!r}*({t})" for c, t in zip(coefs, terms)])
    return LibraryIVFit(terms, score(expr, X, y, crit, bound=bound))
