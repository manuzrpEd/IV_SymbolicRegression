import numpy as np
import pytest

from symiv.criteria import gmm_criterion
from symiv.diagnostics import diagnose
from symiv.dgp import get_law, simulate
from symiv.recovery import form_recovered, srbench_solution, symbolically_equal
from symiv.selection import score

X = np.exp(np.random.default_rng(0).standard_normal((1000, 1)))


@pytest.mark.parametrize(
    "law, expr, expected",
    [
        ("power", "2.03*x0**0.69", True),
        ("log", "log(2.7*x0**2.1)", True),  # = log(2.7) + 2.1 log x: same form, rearranged
        ("log", "0.98 + 2.01*log(x0)", True),
        ("power", "1.9*x0**0.7 + 0.01*log(x0)", False),  # one constant too many
        ("power", "0.5*x0 + 1.2", False),
        ("saturation", "3.1*x0/(0.9 + x0)", True),
        ("kink", "1.02*x0 - 0.79*Max(0, x0 - 1.45)", True),
    ],
)
def test_form_recovered(law, expr, expected):
    assert form_recovered(expr, get_law(law), X).recovered is expected


def test_each_float_occurrence_is_its_own_constant():
    from symiv.expressions import parametrize

    form = parametrize("1.0 + 1.0*x0", 1)
    assert form.n_constants == 2
    np.testing.assert_allclose(form(np.array([[2.0]]), np.array([1.0, 3.0])), [7.0])


def test_srbench_solution():
    assert srbench_solution("2*x0**0.7 + 3", "2*x0**0.7", 1)  # constant offset
    assert srbench_solution("x0**0.7", "2*x0**0.7", 1)  # constant factor
    assert not srbench_solution("x0**0.5", "2*x0**0.7", 1)
    assert not srbench_solution("4.0", "2*x0**0.7", 1)  # constants are never solutions


def test_symbolically_equal():
    assert symbolically_equal("log(2*x0)", "log(x0) + log(2)", 1)
    assert not symbolically_equal("log(2*x0)", "log(x0)", 1)


def test_diagnose_success_and_search_failure():
    s = simulate("D1", "power", n=5000, seed=0)
    crit = gmm_criterion(s.Z)
    right = score("2.1*x0**0.65", s.X, s.y, crit)
    wrong = score("1.2 + 1.5*log(x0)", s.X, s.y, crit)
    assert diagnose(right, s.law, s.X, s.y, crit).outcome == "success"
    d = diagnose(wrong, s.law, s.X, s.y, crit)
    assert d.outcome == "search_failure" and d.mmsc_true < d.mmsc_selected


def test_diagnose_statistical_failure_without_identification():
    # pi = 0: the instrument is irrelevant, every formula with an intercept satisfies
    # the moments, and the penalty prefers a constant over the true log law.
    s = simulate("D1", "log", n=2000, seed=0, pi=0.0)
    crit = gmm_criterion(s.Z)
    constant = score("1.0", s.X, s.y, crit)
    assert diagnose(constant, s.law, s.X, s.y, crit).outcome == "statistical_failure"
