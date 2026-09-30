"""Formulas as SymPy expressions: free constants and fast numeric evaluation."""

from __future__ import annotations

from dataclasses import dataclass
from functools import cached_property

import numpy as np
import sympy as sp


def variables(d: int) -> tuple[sp.Symbol, ...]:
    """Regressor symbols x0, ..., x{d-1}, matching PySR's default feature names."""
    return tuple(sp.Symbol(f"x{j}") for j in range(d))


@dataclass
class ParametricForm:
    """A formula whose numeric constants are free parameters.

    `form` is an expression in `variables` and `params`; `values` are the
    constants as found (the starting point for any refit).
    """

    form: sp.Expr
    params: tuple[sp.Symbol, ...]
    values: np.ndarray
    variables: tuple[sp.Symbol, ...]

    @property
    def n_constants(self) -> int:
        return len(self.params)

    @cached_property
    def _func(self):
        return sp.lambdify(self.variables + self.params, self.form, modules="numpy")

    def __call__(self, X: np.ndarray, theta: np.ndarray | None = None) -> np.ndarray:
        """Evaluate at the rows of X (n, d). Invalid operations give nan, not errors."""
        theta = self.values if theta is None else theta
        with np.errstate(all="ignore"):
            out = self._func(*X.T, *theta)
        return np.broadcast_to(np.asarray(out, dtype=float), (X.shape[0],)).copy()

    def expr(self, theta: np.ndarray | None = None) -> sp.Expr:
        theta = self.values if theta is None else theta
        return self.form.xreplace({p: sp.Float(float(t)) for p, t in zip(self.params, theta)})


def canonical(expr: sp.Expr | str, d: int) -> sp.Expr:
    """`expr` with its symbols replaced by plain x0..x{d-1}.

    PySR and hand-written expressions may create symbols with different
    assumptions; SymPy treats those as different symbols.
    """
    expr = sp.sympify(expr)
    by_name = {x.name: x for x in variables(d)}
    unknown = {s.name for s in expr.free_symbols} - set(by_name)
    if unknown:
        raise ValueError(f"expression uses symbols other than x0..x{d - 1}: {sorted(unknown)}")
    return expr.xreplace({s: by_name[s.name] for s in expr.free_symbols})


def parametrize(expr: sp.Expr | str, d: int) -> ParametricForm:
    """Turn every Float in `expr` into a free constant c0, c1, ...

    Integers are structural (x0**2, the -1 in a subtraction); Floats are
    constants, which is how PySR exports them.
    """
    expr = canonical(expr, d)
    floats = sorted(expr.atoms(sp.Float), key=sp.default_sort_key)
    params = tuple(sp.Symbol(f"c{j}") for j in range(len(floats)))
    form = expr.xreplace(dict(zip(floats, params)))
    return ParametricForm(form, params, np.array([float(f) for f in floats]), variables(d))
