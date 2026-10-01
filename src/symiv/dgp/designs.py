"""Monte Carlo designs D1-D5 (README §8.1). The econometrician sees only (y, X, Z)."""

from __future__ import annotations

from dataclasses import dataclass, field

import numpy as np

from symiv.dgp.laws import Law, get_law

DESIGN_DEFAULTS: dict[str, dict[str, float]] = {
    # Confounding: X = exp(pi Z + v), u = rho v + sigma eps.
    "D1": dict(pi=1.0, rho=0.8, sigma=0.5),
    # Heteroskedastic first stage: X = exp(pi Z + exp(gamma Z) v). IV holds, control function fails.
    "D2": dict(pi=1.0, rho=0.8, sigma=0.5, gamma=0.3),
    # Simultaneity: y = f0(X) + u and y = -kappa log X + gamma Z + e, solved for X.
    "D3": dict(gamma=1.0, kappa=1.0, sigma_u=0.5, sigma_e=0.5),
    # Discrete instrument with J support points; otherwise as D1.
    "D4": dict(pi=1.0, rho=0.8, sigma=0.5, J=4),
    # Weak instrument: D1 with small pi.
    "D5": dict(pi=0.1, rho=0.8, sigma=0.5),
    # Demand with a cost shifter (the mirror image of D3): y = f0(X) + u is a decreasing demand curve,
    # supply is y = kappa log X + gamma Z + e, shifted by Z; solved for the price X.
    "D6": dict(gamma=1.0, kappa=1.0, sigma_u=0.5, sigma_e=0.5),
}


@dataclass
class Sample:
    y: np.ndarray  # (n,)
    X: np.ndarray  # (n, d), strictly positive
    Z: np.ndarray  # (n, k)
    law: Law
    design: str
    params: dict[str, float]
    hidden: dict[str, np.ndarray] = field(default_factory=dict)  # not observed by the econometrician

    @property
    def n(self) -> int:
        return len(self.y)

    @property
    def f0(self) -> np.ndarray:
        """True structural values f0(X) at the sample points."""
        return self.law(self.X)


def simulate(design: str, law: str | Law, n: int, seed: int = 0, **params: float) -> Sample:
    """Draw n observations from `design` with structural law `law`."""
    if design not in DESIGN_DEFAULTS:
        raise ValueError(f"unknown design {design!r}; choose from {sorted(DESIGN_DEFAULTS)}")
    law = get_law(law) if isinstance(law, str) else law
    unknown = set(params) - set(DESIGN_DEFAULTS[design])
    if unknown:
        raise ValueError(f"design {design} has parameters {sorted(DESIGN_DEFAULTS[design])}, not {sorted(unknown)}")
    p = {**DESIGN_DEFAULTS[design], **params}
    rng = np.random.default_rng(seed)

    if design in ("D3", "D6"):
        y, X, Z, hidden = _simultaneous(law, n, rng, p, demand=design == "D6")
    else:
        d = law.dim
        if design == "D4":
            J = int(p["J"])
            support = np.linspace(-1.0, 1.0, J)
            support = (support - support.mean()) / support.std()
            Z = rng.choice(support, size=(n, d))
        else:
            Z = rng.standard_normal((n, d))
        v = rng.standard_normal((n, d))
        eps = rng.standard_normal(n)
        scale = np.exp(p["gamma"] * Z) if design == "D2" else 1.0
        X = np.exp(p["pi"] * Z + scale * v)
        u = p["rho"] * v.sum(axis=1) / np.sqrt(d) + p["sigma"] * eps
        y = law(X) + u
        hidden = {"v": v, "u": u}

    return Sample(y=y, X=X, Z=Z, law=law, design=design, params=p, hidden=hidden)


def _simultaneous(law: Law, n: int, rng: np.random.Generator, p: dict[str, float], demand: bool = False):
    """D3: the target f0 is an increasing (supply) curve, identified by a shifter Z of the demand equation.
    D6 (demand=True): the target is a decreasing demand curve, identified by a shifter Z of the supply equation."""
    name = "D6" if demand else "D3"
    if law.dim != 1:
        raise ValueError(f"{name} is defined for one regressor")
    grid = np.exp(np.linspace(-6.0, 6.0, 400))[:, None]
    slope = np.diff(law(grid))
    if (demand and np.any(slope > 0)) or (not demand and np.any(slope < 0)):
        kind = "decreasing" if demand else "increasing"
        raise ValueError(f"{name} needs a {kind} law; {law.name} with {law.values} is not")

    Z = rng.standard_normal((n, 1))
    u = p["sigma_u"] * rng.standard_normal(n)
    e = p["sigma_e"] * rng.standard_normal(n)
    # Equilibrium: f0(X) + u = -kappa log X + gamma Z + e (D3) or f0(X) + u = kappa log X + gamma Z + e (D6).
    # Solve for t = log X by bisection: g(t) = f0(e^t) -+ kappa t - rhs is strictly monotone in t.
    rhs = p["gamma"] * Z[:, 0] + e - u
    sign = -1.0 if demand else 1.0
    lo, hi = np.full(n, -30.0), np.full(n, 30.0)
    for _ in range(100):
        mid = 0.5 * (lo + hi)
        above = law(np.exp(mid)[:, None]) + sign * p["kappa"] * mid - rhs > 0
        root_left = above if not demand else ~above  # g increasing (D3): g > 0 means the root is to the left
        hi = np.where(root_left, mid, hi)
        lo = np.where(root_left, lo, mid)
    X = np.exp(0.5 * (lo + hi))[:, None]
    y = law(X) + u
    return y, X, Z, {"u": u, "e": e}


def conditional_mean(sample: Sample) -> np.ndarray:
    """E[y | X] at the sample points: the target of plain SR (D1 and D5 only).

    With Z, v independent N(0, 1) and log X_j = pi Z_j + v_j,
    E[v_j | X] = log X_j / (1 + pi^2), so E[y | X] = f0(X) + rho / (sqrt(d) (1 + pi^2)) sum_j log X_j.
    """
    if sample.design not in ("D1", "D5"):
        raise ValueError("closed form only for D1 and D5")
    d = sample.X.shape[1]
    c = sample.params["rho"] / (np.sqrt(d) * (1.0 + sample.params["pi"] ** 2))
    return sample.f0 + c * np.log(sample.X).sum(axis=1)
