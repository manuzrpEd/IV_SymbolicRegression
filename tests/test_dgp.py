import numpy as np
import pytest

from symiv.dgp import LAWS, conditional_mean, get_law, simulate


@pytest.mark.parametrize("design", ["D1", "D2", "D3", "D4", "D5"])
@pytest.mark.parametrize("law", ["log", "power", "kink", "saturation"])
def test_shapes_and_support(design, law):
    s = simulate(design, law, n=500, seed=1)
    assert s.y.shape == (500,) and s.X.shape == (500, 1) and s.Z.shape == (500, 1)
    assert np.all(np.isfinite(s.y)) and np.all(s.X > 0)
    np.testing.assert_allclose(s.y, s.f0 + s.hidden["u"])


def test_reproducible_by_seed():
    a, b, c = (simulate("D1", "power", n=100, seed=k) for k in (3, 3, 4))
    np.testing.assert_array_equal(a.y, b.y)
    assert not np.array_equal(a.y, c.y)


@pytest.mark.parametrize("design", ["D1", "D2", "D3", "D4"])
def test_instrument_valid_and_regressor_endogenous(design):
    s = simulate(design, "power", n=40_000, seed=0)
    u, z, logx = s.hidden["u"], s.Z[:, 0], np.log(s.X[:, 0])
    assert abs(np.mean(u * z)) < 0.03  # E[u Z] = 0
    assert abs(np.corrcoef(u, logx)[0, 1]) > 0.1  # but u moves with X


def test_d1_conditional_mean_matches_regression():
    s = simulate("D1", "log", n=100_000, seed=0)
    slope = np.polyfit(np.log(s.X[:, 0]), s.y - s.f0, 1)[0]
    assert slope == pytest.approx(s.params["rho"] / (1 + s.params["pi"] ** 2), abs=0.02)
    assert np.mean((s.y - conditional_mean(s)) * np.log(s.X[:, 0])) == pytest.approx(0, abs=0.02)


def test_d2_breaks_control_function():
    # With v_hat = log X - pi Z, E[u | v_hat, Z] = rho v_hat exp(-gamma Z): it depends on Z.
    s = simulate("D2", "log", n=100_000, seed=0)
    z = s.Z[:, 0]
    v_hat = np.log(s.X[:, 0]) - s.params["pi"] * z
    coef, *_ = np.linalg.lstsq(np.column_stack([v_hat, v_hat * z]), s.hidden["u"], rcond=None)
    assert coef[1] < -0.1


def test_d3_is_an_equilibrium():
    s = simulate("D3", "saturation", n=2000, seed=0)
    p = s.params
    demand = -p["kappa"] * np.log(s.X[:, 0]) + p["gamma"] * s.Z[:, 0] + s.hidden["e"]
    np.testing.assert_allclose(s.y, demand, atol=1e-8)


def test_d3_rejects_decreasing_law_and_two_regressors():
    with pytest.raises(ValueError):
        simulate("D3", get_law("log", b=-1.0), n=10)
    with pytest.raises(ValueError):
        simulate("D3", "cobb_douglas", n=10)


def test_d4_has_J_support_points():
    s = simulate("D4", "log", n=1000, J=3)
    assert len(np.unique(s.Z)) == 3


def test_d5_first_stage_weaker_than_d1():
    strong, weak = (simulate(d, "log", n=5000, seed=0) for d in ("D1", "D5"))
    corr = lambda s: abs(np.corrcoef(s.Z[:, 0], np.log(s.X[:, 0]))[0, 1])
    assert corr(weak) < 0.2 < corr(strong)


def test_two_regressor_law():
    s = simulate("D1", "cobb_douglas", n=300)
    assert s.X.shape == (300, 2) and s.Z.shape == (300, 2)


def test_law_overrides_and_expr():
    law = get_law("power", theta=0.5)
    assert law.values == (2.0, 0.5)
    X = np.array([[4.0]])
    assert law(X)[0] == pytest.approx(4.0)
    assert set(LAWS) == {"log", "power", "kink", "saturation", "cobb_douglas"}
    with pytest.raises(ValueError):
        get_law("power", nope=1.0)
