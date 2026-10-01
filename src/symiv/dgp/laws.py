"""Structural laws f0 for the Monte Carlo (README §8.1)."""

from __future__ import annotations

from dataclasses import dataclass, replace

import numpy as np
import sympy as sp

from symiv.expressions import ParametricForm, variables


@dataclass(frozen=True)
class Law:
    """A structural law f0(x; theta0) with known parametric form."""

    name: str
    dim: int
    form: sp.Expr
    params: tuple[sp.Symbol, ...]
    values: tuple[float, ...]

    @property
    def n_constants(self) -> int:
        return len(self.params)

    @property
    def parametric(self) -> ParametricForm:
        return ParametricForm(self.form, self.params, np.array(self.values, dtype=float), variables(self.dim))

    @property
    def expr(self) -> sp.Expr:
        """f0 with the true constants substituted."""
        return self.form.xreplace({p: sp.Float(v) for p, v in zip(self.params, self.values)})

    def __call__(self, X: np.ndarray) -> np.ndarray:
        return self.parametric(X)


_x0, _x1 = variables(2)
_a, _b, _c, _theta, _A, _alpha, _beta = sp.symbols("a b c theta A alpha beta")

LAWS: dict[str, Law] = {
    # In any finite library: library-based sparse IV should also succeed.
    "log": Law("log", 1, _a + _b * sp.log(_x0), (_a, _b), (1.0, 2.0)),
    # Outside any finite library (nonlinear in a parameter). Constants avoid coincidences (e.g. beta = 2 alpha, A = 1)
    # that would let a simpler formula reproduce the law exactly.
    "power": Law("power", 1, _a * _x0**_theta, (_a, _theta), (2.0, 0.7)),
    "kink": Law("kink", 1, _a * _x0 + _b * sp.Max(_x0 - _c, 0), (_a, _b, _c), (1.0, -0.8, 1.5)),
    "saturation": Law("saturation", 1, _a * _x0 / (_b + _x0), (_a, _b), (3.0, 1.0)),
    "cobb_douglas": Law(
        "cobb_douglas", 2, _A * _x0**_alpha * _x1**_beta, (_A, _alpha, _beta), (1.5, 0.3, 0.5)
    ),
}


def get_law(name: str, **values: float) -> Law:
    """A law from LAWS, optionally with different true constants (by parameter name)."""
    law = LAWS[name]
    names = [p.name for p in law.params]
    unknown = set(values) - set(names)
    if unknown:
        raise ValueError(f"law {name!r} has parameters {names}, not {sorted(unknown)}")
    return replace(law, values=tuple(float(values.get(n, v)) for n, v in zip(names, law.values)))
