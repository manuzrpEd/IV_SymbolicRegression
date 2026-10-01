import numpy as np
import pytest
import sympy as sp

from symiv.baselines import fit_kiv, fit_library_iv, fit_sieve_iv, fixed_form_iv, oracle_iv, wrong_forms
from symiv.baselines.control_function import first_stage_residual, parse_template
from symiv.baselines.srit import _benjamini_hochberg, hsic_pvalue
from symiv.criteria import gmm_criterion
from symiv.dgp import conditional_mean, simulate
from symiv.metrics import relative_error
from symiv.recovery import form_recovered


@pytest.fixture(scope="module")
def log_d1():
    s = simulate("D1", "log", n=2000, seed=0)
    return s, gmm_criterion(s.Z)


def rms_error(f_hat, s):
    return np.sqrt(np.mean((f_hat(s.X) - s.f0) ** 2)) / s.f0.std()


def test_oracle_and_wrong_forms(log_d1):
    s, crit = log_d1
    assert set(wrong_forms(s.law)) == {"linear", "power"}
    assert form_recovered(oracle_iv(s.law, s.X, s.y, crit).fitted_expr, s.law, s.X).recovered
    wrong = fixed_form_iv(wrong_forms(s.law)["linear"], s.X, s.y, crit)
    assert relative_error(wrong.fitted_expr, s.law, s.X) > 0.2


def test_sieve_iv_is_close_to_f0_and_better_than_the_conditional_mean(log_d1):
    s, crit = log_d1
    fit = fit_sieve_iv(s.X, s.y, crit)
    assert 4 <= fit.J <= crit.K
    cm_error = np.sqrt(np.mean((conditional_mean(s) - s.f0) ** 2)) / s.f0.std()
    assert rms_error(fit, s) < 0.5 * cm_error


def test_kiv_is_close_to_f0_with_a_strong_instrument():
    # With pi = 1 KIV's error is ~0.25 even without endogeneity (ill-posedness, not a bug); with pi = 3 it is small.
    s = simulate("D1", "log", n=2000, seed=0, pi=3.0)
    assert rms_error(fit_kiv(s.X, s.y, s.Z), s) < 0.1


def test_library_iv_recovers_a_law_in_the_library(log_d1):
    s, crit = log_d1
    fit = fit_library_iv(s.X, s.y, crit)
    assert "log(x0)" in fit.terms
    assert relative_error(fit.candidate.fitted_expr, s.law, s.X) < 0.1


def test_parse_template():
    f, g = parse_template("f = #1 + (#1 ^ 0.5); g = max(#1, 1.5) * 0.78")
    x0, x1 = sp.symbols("x0 x1")
    assert f == x0 + x0**0.5
    assert g.free_symbols == {x1} and g.has(sp.Max)


def test_first_stage_residual_is_orthogonal_to_instruments(log_d1):
    s, crit = log_d1
    v = first_stage_residual(s.X, crit)
    np.testing.assert_allclose(crit.A.T @ v, 0, atol=1e-8)
    assert np.corrcoef(v, s.hidden["v"][:, 0])[0, 1] > 0.95  # D1: v_hat estimates v


def test_hsic_detects_dependence_and_independence():
    rng = np.random.default_rng(0)
    a = rng.standard_normal(600)
    assert hsic_pvalue(a, a**2 + 0.1 * rng.standard_normal(600)) < 0.01  # dependent, uncorrelated
    assert hsic_pvalue(a, rng.standard_normal(600)) > 0.05


def test_benjamini_hochberg():
    adj = _benjamini_hochberg({0: 0.01, 1: 0.04, 2: 0.03})
    assert adj == pytest.approx({0: 0.03, 1: 0.04, 2: 0.04})


@pytest.mark.slow
def test_deepiv_is_close_to_f0():
    pytest.importorskip("torch")
    from symiv.baselines.deepiv import fit_deepiv

    s = simulate("D1", "log", n=2000, seed=0)
    fit = fit_deepiv(s.X, s.y, s.Z, max_epochs=100)
    cm_error = np.sqrt(np.mean((conditional_mean(s) - s.f0) ** 2)) / s.f0.std()
    assert rms_error(fit, s) < cm_error
