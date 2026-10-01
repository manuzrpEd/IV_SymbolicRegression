"""Control-function SR, variant (a) of README §6.2.

First stage: v_hat = log X - E_hat[log X | Z] on the criterion's instruments.
Second stage: PySR with the template f(x) + g(v) and squared-error loss. Valid when
E[u | v, Z] = E[u | v] (Newey, Powell & Vella 1999); design D2 violates that.
The structural function is f(x) + mean(g(v_hat)), since E[g(v)] = E[u] = 0.
"""

from __future__ import annotations

from dataclasses import dataclass

import numpy as np
import sympy as sp

from symiv.criteria import MomentCriterion
from symiv.expressions import parametrize, variables
from symiv.selection import Selection, select_ls

_PARSE = {"max": sp.Max, "min": sp.Min}


@dataclass
class ControlFunctionFit:
    f_expr: sp.Expr  # structural part, in x0
    g_expr: sp.Expr  # control part, in x1 = v_hat
    selection: Selection  # over f(x0) + g(x1), least squares with BIC
    v_hat: np.ndarray


def first_stage_residual(X: np.ndarray, crit: MomentCriterion) -> np.ndarray:
    """log X minus its projection on the instrument space."""
    if crit.kind != "gmm":
        raise ValueError("needs a gmm criterion (orthonormal A) for the first-stage projection")
    t = np.log(X[:, 0])
    return t - crit.A @ (crit.A.T @ t)


def parse_template(equation: str) -> tuple[sp.Expr, sp.Expr]:
    """PySR's 'f = <expr in #1>; g = <expr in #1>' as (f(x0), g(x1))."""
    parts = dict(p.split(" = ", 1) for p in equation.split("; "))
    f = sp.sympify(parts["f"].replace("#1", "x0"), locals=_PARSE)
    g = sp.sympify(parts["g"].replace("#1", "x1"), locals=_PARSE)
    return f, g


def fit_control_function_sr(X: np.ndarray, y: np.ndarray, crit: MomentCriterion, **search) -> ControlFunctionFit:
    from pysr import PySRRegressor, TemplateExpressionSpec

    from symiv.search import SEARCH_DEFAULTS

    v_hat = first_stage_residual(X, crit)
    W = np.column_stack([X[:, 0], v_hat])
    spec = TemplateExpressionSpec(expressions=["f", "g"], variable_names=["x", "v"], combine="f(x) + g(v)")
    model = PySRRegressor(expression_spec=spec, **{**SEARCH_DEFAULTS, **search})
    model.fit(W, y)

    exprs = [sum(parse_template(eq)) for eq in model.equations_["equation"]]
    sel = select_ls(exprs, W, y, list(model.equations_["complexity"]))
    x1 = variables(2)[1]
    f_part, g_part = sel.best.fitted_expr.as_independent(x1, as_Add=True)
    shift = float(np.mean(parametrize(g_part, 2)(W))) if g_part != 0 else 0.0
    if abs(shift) < 1e-8 * max(1.0, float(np.std(y))):  # g(v) = c v has mean 0 exactly: no extra constant
        shift = 0.0
    f_expr = sp.sympify(f_part) + sp.Float(shift) if shift else sp.sympify(f_part)
    return ControlFunctionFit(f_expr, g_part, sel, v_hat)
