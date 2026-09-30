import numpy as np
import pytest

from symiv.criteria import exact_mmr, gmm_criterion, mmr_criterion, nystrom_features
from symiv.criteria.instruments import spline_basis
from symiv.dgp import conditional_mean, simulate
from symiv.gmm import efficient_weight_sqrt, hansen_j


def test_gmm_value_equals_2sls_weighted_criterion():
    rng = np.random.default_rng(0)
    Z = rng.standard_normal((400, 1))
    r = rng.standard_normal(400)
    crit = gmm_criterion(Z, K=10)
    B = spline_basis(Z, 10)
    g = B.T @ r / len(r)
    W = np.linalg.pinv(B.T @ B / len(r))
    assert crit.value(r) == pytest.approx(g @ W @ g, rel=1e-8)
    np.testing.assert_allclose(crit.A.T @ crit.A, np.eye(crit.K), atol=1e-10)


def test_discrete_instrument_basis_is_saturated():
    Z = np.repeat([-1.0, 0.0, 1.0], 100)[:, None]
    crit = gmm_criterion(Z, K=12)
    assert crit.K == 3


def test_nystrom_mmr_matches_exact():
    rng = np.random.default_rng(1)
    Z = rng.standard_normal((500, 1))
    r = np.sin(2 * Z[:, 0]) + 0.3 * rng.standard_normal(500)
    _, h = nystrom_features(Z, m=200)
    crit = mmr_criterion(Z, m=200)
    assert crit.value(r) == pytest.approx(exact_mmr(Z, r, h), rel=0.02)


@pytest.mark.parametrize("make", [lambda Z: gmm_criterion(Z), lambda Z: mmr_criterion(Z)])
@pytest.mark.parametrize("law", ["log", "power"])
def test_criterion_small_at_truth_large_at_plain_sr_target(make, law):
    s = simulate("D1", law, n=5000, seed=0)
    crit = make(s.Z)
    at_truth = crit.value(s.y - s.f0)
    at_conditional_mean = crit.value(s.y - conditional_mean(s))
    assert at_conditional_mean > 20 * at_truth


def test_j_statistic_at_truth_is_chi_squared_K():
    js, K = [], None
    for seed in range(200):
        s = simulate("D1", "power", n=1000, seed=seed)
        crit = gmm_criterion(s.Z, K=10)
        r = s.y - s.f0
        js.append(hansen_j(crit, r, efficient_weight_sqrt(crit, r)))
        K = crit.K
    assert np.mean(js) == pytest.approx(K, abs=4 * np.sqrt(2 * K / 200) + 0.5)
