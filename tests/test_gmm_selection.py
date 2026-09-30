import numpy as np
import pytest
import sympy as sp
from scipy.optimize import least_squares

from symiv.criteria import gmm_criterion
from symiv.dgp import simulate
from symiv.expressions import parametrize
from symiv.gmm import fit_gmm
from symiv.selection import select_mmsc


@pytest.fixture(scope="module")
def power_d1():
    s = simulate("D1", "power", n=5000, seed=0)
    return s, gmm_criterion(s.Z)


def test_gmm_recovers_constants_where_least_squares_is_biased(power_d1):
    s, crit = power_d1
    form = s.law.parametric
    start = np.array([1.5, 0.5])
    gmm = fit_gmm(form, s.X, s.y, crit, theta0=start)
    nls = least_squares(lambda t: s.y - form(s.X, t), start).x
    truth = np.array(s.law.values)
    assert np.max(np.abs(gmm.theta - truth)) < 0.1
    assert np.max(np.abs(nls - truth)) > 3 * np.max(np.abs(gmm.theta - truth))


def test_bound_on_constants_is_respected(power_d1):
    s, crit = power_d1
    fit = fit_gmm(s.law.parametric, s.X, s.y, crit, bound=1.5, theta0=np.array([1.0, 0.5]))
    assert np.all(np.abs(fit.theta) <= 1.5 + 1e-12)


def test_formula_without_constants(power_d1):
    s, crit = power_d1
    fit = fit_gmm(parametrize("log(x0)", 1), s.X, s.y, crit)
    assert fit.p == 0 and np.isfinite(fit.J) and fit.df == crit.K


def test_undefined_formula_does_not_crash(power_d1):
    s, crit = power_d1
    fit = fit_gmm(parametrize("log(x0 - 5.0)", 1), s.X, s.y, crit)
    assert fit.J > 1e3 or not np.isfinite(fit.J)


def test_mmsc_picks_minimal_true_form(power_d1):
    s, crit = power_d1
    candidates = [
        "1.2 + 1.5*log(x0)",  # wrong form
        "0.5*x0 + 1.2",  # wrong form
        "2.1*x0**0.65",  # true form
        "1.9*x0**0.7 + 0.3*log(x0)",  # contains the truth, one constant too many
    ]
    sel = select_mmsc(candidates, s.X, s.y, crit)
    assert sel.best.expr == sp.sympify("2.1*x0**0.65")
    over = next(c for c in sel.candidates if c.n_constants == 3)
    assert over.fit.J <= sel.best.fit.J + 1e-6  # fits at least as well ...
    assert over.mmsc > sel.best.mmsc  # ... but is penalized for the extra constant
    assert len(sel.candidates) == 4
