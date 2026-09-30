"""Checks that the Julia loss is wired correctly. Slow (Julia); run with `pytest -m julia`."""

import numpy as np
import pytest

pytest.importorskip("pysr")

from symiv.criteria import gmm_criterion  # noqa: E402
from symiv.dgp import simulate  # noqa: E402
from symiv.search import fit_symbolic_iv, pareto_front  # noqa: E402

pytestmark = pytest.mark.julia


@pytest.fixture(scope="module")
def fitted():
    s = simulate("D1", "power", n=500, seed=0)
    crit = gmm_criterion(s.Z)
    model = fit_symbolic_iv(s.X, s.y, crit, niterations=5, populations=4, maxsize=12)
    return s, crit, model


def test_julia_loss_equals_python_criterion(fitted):
    s, crit, model = fitted
    for i in range(len(model.equations_)):
        r = s.y - model.predict(s.X, index=i)
        assert model.equations_["loss"].iloc[i] == pytest.approx(crit.value(r), rel=1e-6)


def test_pareto_front_is_sympy(fitted):
    _, _, model = fitted
    exprs, complexities = pareto_front(model)
    assert len(exprs) == len(complexities) > 0
    assert all(e.free_symbols <= {__import__("sympy").Symbol("x0")} for e in exprs)
