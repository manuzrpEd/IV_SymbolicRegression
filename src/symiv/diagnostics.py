"""Search failures vs. statistical failures (README §7, "Not claimed")."""

from __future__ import annotations

from dataclasses import dataclass

import numpy as np

from symiv.criteria import MomentCriterion
from symiv.dgp.laws import Law
from symiv.gmm import fit_gmm
from symiv.recovery import Recovery, form_recovered
from symiv.selection import Candidate, mmsc


@dataclass
class Diagnosis:
    outcome: str  # "success" | "search_failure" | "statistical_failure"
    mmsc_selected: float
    mmsc_true: float  # MMSC of the true form, constants refit on the same data
    recovery: Recovery


def diagnose(
    selected: Candidate,
    law: Law,
    X: np.ndarray,
    y: np.ndarray,
    crit: MomentCriterion,
    penalty: str = "bic",
    bound: float = 10.0,
    tol: float = 1e-8,
) -> Diagnosis:
    """Classify the outcome of one run.

    success: the selected formula recovers the form of f0.
    search_failure: the true form scores a lower MMSC than the selected formula,
        so the estimator (global argmin) would have preferred it; the search did not find it.
    statistical_failure: the estimator itself prefers the wrong formula.

    `selected.mmsc` must come from the same criterion and penalty.
    """
    recovery = form_recovered(selected.fitted_expr, law, X)
    true_fit = fit_gmm(law.parametric, X, y, crit, bound=bound, theta0=np.array(law.values))
    mmsc_true = mmsc(true_fit, len(y), penalty) if np.isfinite(true_fit.J) else np.inf
    if recovery.recovered:
        outcome = "success"
    elif mmsc_true < selected.mmsc - tol:
        outcome = "search_failure"
    else:
        outcome = "statistical_failure"
    return Diagnosis(outcome, selected.mmsc, mmsc_true, recovery)
