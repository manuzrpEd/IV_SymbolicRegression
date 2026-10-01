"""A template library of economic shapes, used as a candidate generator (README §11, "Before the paper").

Each template is a formula in one positive regressor whose constants are free; it is scored like any other
candidate (two-step GMM refit, MMSC with the structure term), so templates compete with the search's formulas
instead of replacing them. The library is fixed in advance and holds the textbook shapes of applied economics:
constant elasticity, semi-log (Working–Leser), quadratic in logs (QUAIDS), a kinked linear schedule (a tax or
benefit threshold), saturation (diminishing returns), a hump (backward-bending supply, a Laffer curve), a
hyperbola, an exponential, a quadratic, and a logistic. Every placeholder constant is a float that SymPy keeps
(no 0.0 or 1.0, which it would simplify away), so `parametrize` sees the right number of constants.
"""

from __future__ import annotations

TEMPLATES: dict[str, str] = {
    "linear": "0.5 + 0.5*x0",
    "semilog": "0.5 + 0.5*log(x0)",
    "power": "1.5*x0**0.5",
    "quadlog": "0.5 + 0.5*log(x0) - 0.2*log(x0)**2",
    "kink": "0.5*x0 - 0.5*Max(x0 - 1.5, 0)",
    "saturation": "2.0*x0/(1.5 + x0)",
    "hump": "2.0*x0*exp(-0.5*x0)",
    "hyperbola": "2.0/(1.5 + x0)",
    "exponential": "0.5*exp(0.5*x0)",
    "quadratic": "0.5 + 0.5*x0 - 0.2*x0**2",
    "logistic": "2.0/(1.5 + exp(-0.5*x0))",
}


def template_candidates() -> list[str]:
    """The templates as candidate expressions (one regressor)."""
    return list(TEMPLATES.values())
