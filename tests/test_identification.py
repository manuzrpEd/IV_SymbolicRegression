import numpy as np
from scipy.stats import chi2

from symiv.criteria import gmm_criterion
from symiv.dgp import simulate
from symiv.identification import ar_statistic, first_stage, identification_report, s_statistic

# The true power law, a wrong linear form, a superset with one extra term, and the (wrong) log law.
CANDIDATES = ["2.0*x0**0.7", "1.0*x0 + 0.5", "2.0*x0**0.7 + 0.1*log(x0)", "1.0 + 2.0*log(x0)"]


def _data(pi: float, seed: int = 0, n: int = 1000):
    s = simulate("D1" if pi >= 0.5 else "D5", "power", n=n, seed=seed, pi=pi)
    return s, gmm_criterion(s.Z)


def test_ar_at_truth_is_chi2_sized():
    s, crit = _data(1.0)
    ar_true = ar_statistic(s.law.parametric, s.X, s.y, crit, np.array(s.law.values))
    assert ar_true < chi2.ppf(0.999, crit.K)
    assert s_statistic(s.law.parametric, s.X, s.y, crit, np.array(s.law.values))[0] <= ar_true + 1e-9


def test_strong_instrument_identified():
    s, crit = _data(1.0)
    rep = identification_report("2.0*x0**0.7", CANDIDATES, s.X, s.y, crit)
    assert rep.verdict == "identified", rep.reasons
    assert first_stage(s.X, crit).F[0] > 50
    assert all(rep.ar_bounded) and max(rep.width_ratio) < 3
    linear = next(c for c in rep.candidates if c.expr == "1.0*x0 + 0.5")
    assert not linear.in_set  # the data reject the wrong form


def test_weak_instrument_flagged():
    s, crit = _data(0.02)
    rep = identification_report("2.0*x0**0.7", CANDIDATES, s.X, s.y, crit)
    assert rep.verdict == "weakly identified", rep.reasons
    assert first_stage(s.X, crit).F[0] < 10


def test_wrong_selection_rejected():
    s, crit = _data(1.0)
    rep = identification_report("1.0*x0 + 0.5", ["2.0*x0**0.7"], s.X, s.y, crit)
    assert rep.verdict == "rejected"
    assert rep.reasons[0].startswith("the selected formula fails")


def test_flat_selection_has_a_finite_distance_scale():
    # y = 0.3 + noise, no dependence on X: a constant is selected; alternatives are measured against 0.1 sd(y).
    rng = np.random.default_rng(0)
    n = 1000
    Z = rng.normal(size=(n, 1))
    X = np.exp(0.5 * Z[:, 0] + 0.5 * rng.normal(size=n))[:, None]
    y = 0.3 + 0.05 * rng.normal(size=n)
    crit = gmm_criterion(Z)
    rep = identification_report("0.3", ["0.3 + 0.01*log(x0)", "0.2*x0**0.5"], X, y, crit)
    assert all(np.isfinite(c.distance) and c.distance < 100 for c in rep.candidates), [c.distance for c in rep.candidates]
    assert rep.max_distance < 100
