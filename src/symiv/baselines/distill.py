"""NPIV -> symbolic distillation (README §3.2): the main two-step competitor.

Fit a nonparametric IV estimate f_hat, then run plain PySR on (X, f_hat(X)), as
Cranmer et al. (2020) do with neural networks. Two ways to pick the formula:
- "pick": PySR's own choice, the two-step as a practitioner would run it;
- "mmsc": the distilled Pareto front scored on the original data by MMSC. This
  separates the value of the one-step search from the value of the selection rule.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass

import numpy as np
import sympy as sp

from symiv.criteria import MomentCriterion
from symiv.selection import Selection, select_mmsc


@dataclass
class Distillation:
    pick: sp.Expr
    by_mmsc: Selection


def distill(
    f_hat: Callable[[np.ndarray], np.ndarray],
    X: np.ndarray,
    y: np.ndarray,
    crit: MomentCriterion,
    bound: float = 10.0,
    **search,
) -> Distillation:
    from symiv.search import pareto_front, plain_regressor

    model = plain_regressor(**search)
    model.fit(X, f_hat(X))
    exprs, complexities = pareto_front(model)
    return Distillation(model.sympy(), select_mmsc(exprs, X, y, crit, complexities=complexities, bound=bound))
