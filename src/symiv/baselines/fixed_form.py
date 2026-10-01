"""Fixed-form IV: oracle 2SLS (the true form) and wrong-form 2SLS (README §8.1).

Both are the two-step GMM refit of one formula on the same instruments as symbolic IV.
"""

from __future__ import annotations

import numpy as np

from symiv.criteria import MomentCriterion
from symiv.dgp.laws import Law
from symiv.selection import Candidate, score

# Forms a practitioner might assume, with starting constants.
STANDARD_FORMS = {
    "linear": "1.0 + 1.0*x0",
    "log": "1.0 + 1.0*log(x0)",
    "power": "1.0*x0**0.5",
}


def wrong_forms(law: Law) -> dict[str, str]:
    """The standard forms that differ from the law's own family."""
    return {name: form for name, form in STANDARD_FORMS.items() if name != law.name}


def fixed_form_iv(expr: str, X: np.ndarray, y: np.ndarray, crit: MomentCriterion, bound: float = 10.0) -> Candidate:
    """Two-step GMM fit of one given form."""
    return score(expr, X, y, crit, bound=bound)


def oracle_iv(law: Law, X: np.ndarray, y: np.ndarray, crit: MomentCriterion, bound: float = 10.0) -> Candidate:
    """Two-step GMM fit of the true form, started at the true constants."""
    return score(law.expr, X, y, crit, bound=bound, theta0=np.array(law.values))
