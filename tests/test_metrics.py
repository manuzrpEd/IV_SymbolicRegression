import numpy as np
import pytest

from symiv.criteria import gmm_criterion
from symiv.dgp import conditional_mean, get_law, simulate
from symiv.metrics import elasticity, extrapolation_error, extrapolation_grid, implied_constants, relative_error
from symiv.selection import rerank, select_ls, select_mmsc

X = np.exp(np.random.default_rng(0).standard_normal((1000, 1)))


def test_errors_are_zero_at_the_truth_and_positive_elsewhere():
    law = get_law("power")
    assert relative_error("2.0*x0**0.7", law, X) == pytest.approx(0, abs=1e-12)
    assert extrapolation_error("2.0*x0**0.7", law, X) == pytest.approx(0, abs=1e-12)
    assert relative_error("2.1*x0**0.7", law, X) > 0
    assert relative_error("log(x0 - 1.0)", law, X) == np.inf


def test_extrapolation_grid_is_beyond_the_support():
    G = extrapolation_grid(X)
    assert G.min() >= np.quantile(X, 0.99) - 1e-12 and G.max() == pytest.approx(3 * np.quantile(X, 0.99))


def test_elasticity():
    assert elasticity("2.0*x0**0.7", 3.0) == pytest.approx(0.7, rel=1e-6)
    assert elasticity("1.0 + 2.0*log(x0)", 1.0) == pytest.approx(2.0, rel=1e-6)


def test_implied_constants_in_true_parametrization():
    np.testing.assert_allclose(implied_constants("x0**0.709/0.479", get_law("power"), X), [1 / 0.479, 0.709], rtol=1e-6)


def test_select_ls_prefers_the_conditional_mean():
    # Plain SR's target in D1 is f0 + c log X: least squares must prefer it to f0 itself.
    s = simulate("D1", "power", n=5000, seed=0, pi=0.7, rho=1.2)
    sel = select_ls(["2.0*x0**0.7", "2.0*x0**0.7 + 0.8*log(x0)", "x0 + 0.8"], s.X, s.y)
    assert sel.best.n_constants == 3
    assert np.mean((s.y - conditional_mean(s)) ** 2) <= sel.candidates[1].rss / s.n * 1.01


def test_rerank_changes_only_the_ranking():
    s = simulate("D1", "power", n=2000, seed=1, pi=0.7, rho=1.2)
    crit = gmm_criterion(s.Z)
    bic = select_mmsc(["x0 + 0.8", "2.0*x0**0.7"], s.X, s.y, crit)
    aic = rerank(bic, s.n, "aic")
    assert {str(c.expr) for c in aic.candidates} == {str(c.expr) for c in bic.candidates}
    for c in aic.candidates:
        assert c.mmsc == pytest.approx(c.fit.J - 2.0 * c.fit.df)
    # The weak-separation seed from the pilot: the line wins under BIC by ~6, under AIC by < 1.
    gap = lambda sel: sel.candidates[1].mmsc - sel.candidates[0].mmsc
    assert bic.best.n_constants == 1 and gap(aic) < 1 < gap(bic)
