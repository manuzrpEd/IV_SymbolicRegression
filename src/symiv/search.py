"""PySR search scored by the moment criterion (README §6.6).

Needs the `search` extra (`pip install -e .[search]`); the first import of PySR
installs Julia and SymbolicRegression.jl.
"""

from __future__ import annotations

from importlib.resources import files

import numpy as np
import sympy as sp

from symiv.criteria import MomentCriterion

MOMENT_LOSS = files("symiv").joinpath("julia/moment_loss.jl").read_text()

_JULIA_SETUP = """
if !isdefined(Main, :SYMIV_A)
    const SYMIV_A = Ref{Matrix{Float64}}(zeros(0, 0))
    const SYMIV_BOUND = Ref{Float64}(Inf)
    symiv_set!(A, bound) = (SYMIV_A[] = Matrix{Float64}(A); SYMIV_BOUND[] = Float64(bound); nothing)
end
"""

# Formula class of README §6.1. `^` only takes a constant or a single variable as exponent.
SEARCH_DEFAULTS = dict(
    binary_operators=["+", "-", "*", "/", "^", "max"],
    unary_operators=["log", "exp"],
    constraints={"^": (-1, 1)},
    nested_constraints={"log": {"log": 0, "exp": 0}, "exp": {"log": 0, "exp": 0}},
    maxsize=20,
    precision=64,
    parallelism="multithreading",
    progress=False,
    verbosity=0,
)


def set_instruments(crit: MomentCriterion, bound: float) -> None:
    """Hand A and the constant bound to the Julia loss (a global in Julia's Main)."""
    from pysr import jl

    jl.seval(_JULIA_SETUP)
    jl.seval("symiv_set!")(np.ascontiguousarray(crit.A), float(bound))


def symbolic_iv_regressor(**kwargs):
    """A PySRRegressor whose loss is the moment criterion. Call `fit_symbolic_iv` to fit it."""
    from pysr import PySRRegressor

    return PySRRegressor(**{**SEARCH_DEFAULTS, **kwargs, "loss_function": MOMENT_LOSS, "batching": False})


def plain_regressor(**kwargs):
    """Plain PySR (MSE loss) on the same formula class: the biased baseline."""
    from pysr import PySRRegressor

    return PySRRegressor(**{**SEARCH_DEFAULTS, **kwargs})


def fit_symbolic_iv(X: np.ndarray, y: np.ndarray, crit: MomentCriterion, bound: float = 10.0, **kwargs):
    """Run the PySR search with loss Q_n(f) = ||A'(y - f(X))||^2 / n (+ penalty on |constants| > bound)."""
    if crit.n != len(y):
        raise ValueError(f"criterion built for n={crit.n}, data has n={len(y)}")
    model = symbolic_iv_regressor(**kwargs)
    set_instruments(crit, bound)
    model.fit(X, y)
    return model


def pareto_front(model) -> tuple[list[sp.Expr], list[int]]:
    """The fitted model's Pareto front as (SymPy expressions, complexities)."""
    eqs = model.equations_
    return list(eqs["sympy_format"]), [int(c) for c in eqs["complexity"]]
