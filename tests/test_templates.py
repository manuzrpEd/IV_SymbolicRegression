import numpy as np
import pytest

from symiv.dgp import get_law
from symiv.expressions import parametrize
from symiv.recovery import form_recovered
from symiv.templates import TEMPLATES, template_candidates

X = np.linspace(0.3, 6.0, 300)[:, None]


def test_every_template_keeps_its_constants():
    expected = {"linear": 2, "semilog": 2, "power": 2, "quadlog": 3, "kink": 3, "saturation": 2, "hump": 2,
                "hyperbola": 2, "exponential": 2, "quadratic": 3, "logistic": 3}
    for name, e in TEMPLATES.items():
        form = parametrize(e, 1)
        assert form.n_constants == expected[name], name  # SymPy did not simplify a placeholder away
        assert np.all(np.isfinite(form(X))), name


@pytest.mark.parametrize("law, template", [("log", "semilog"), ("power", "power"), ("kink", "kink"), ("saturation", "saturation"),
                                           ("hump", "hump"), ("quadlog", "quadlog"), ("demand_hyper", "hyperbola")])
def test_templates_cover_the_benchmark_laws(law, template):
    r = form_recovered(TEMPLATES[template], get_law(law), X)
    assert r.recovered and r.rel_error < 1e-6


def test_a_template_does_not_cover_a_law_of_another_shape():
    assert not form_recovered(TEMPLATES["semilog"], get_law("power"), X).recovered
    assert len(template_candidates()) == len(TEMPLATES)
