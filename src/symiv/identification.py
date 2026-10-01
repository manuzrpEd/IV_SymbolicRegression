"""Identification diagnostics after selection (README §6.4; THEORY.md Proposition 5).

Wald intervals and Hansen's J assume the selected formula is identified. Anderson–Rubin
statistics do not (Stock & Wright 2000), so they can say when the instruments are too weak:

- constants: invert the AR statistic along each constant of the selected formula, profiling
  the others. A weak instrument gives an interval that reaches the constant bound, or one
  many times wider than the Wald interval.
- formula: each candidate's S statistic (its minimal AR) tests "this form holds for some
  constants" without a rank condition. The candidates the data do not reject form a
  confidence set of formulas that contains the true form with probability >= 1 - alpha,
  whatever the instrument strength. If it contains formulas far from the selected one, the
  data do not identify the formula.

The report's verdict is "identified", "weakly identified" (with the reasons: which constants
and which other formulas the data allow) or "rejected" (the selected formula itself fails
the moment conditions).
"""

from __future__ import annotations

from dataclasses import dataclass, field

import numpy as np
from scipy.linalg import solve
from scipy.optimize import minimize
from scipy.stats import chi2

from symiv.criteria import MomentCriterion
from symiv.expressions import ParametricForm, parametrize
from symiv.gmm import fit_gmm

Z95 = 1.959964


@dataclass
class FirstStage:
    F: list[float]  # per regressor: F statistic of (log) X on the instrument span, constant excluded
    r2: list[float]


def first_stage(X: np.ndarray, crit: MomentCriterion) -> FirstStage:
    """Instrument strength: the F statistic of each regressor (in logs when positive) on the instruments."""
    A = crit.A
    n, K = A.shape
    Fs, r2s = [], []
    for j in range(X.shape[1]):
        x = X[:, j]
        x = np.log(x) if np.all(x > 0) else x
        xc = x - x.mean()
        fitted = A @ (A.T @ xc)
        r2 = float(fitted @ fitted / (xc @ xc)) if xc @ xc > 0 else 0.0
        df1, df2 = max(K - 1, 1), max(n - K, 1)
        Fs.append(float((r2 / df1) / max((1 - r2) / df2, 1e-300)))
        r2s.append(r2)
    return FirstStage(Fs, r2s)


def ar_statistic(form: ParametricForm, X, y, crit: MomentCriterion, theta, envelope: float | None = None) -> float:
    """Anderson–Rubin statistic at theta: n g' Omega(theta)^{-1} g with the weight evaluated at theta (CUE objective).

    `envelope` bounds max |f(X; theta)|: the sample version of the envelope in (A3). Without it the statistic
    can be small at absurd constants, because residuals dominated by a few observations make the robust
    weight tiny everywhere else.
    """
    vals = form(X, np.asarray(theta, dtype=float))
    if not np.all(np.isfinite(vals)) or (envelope is not None and np.max(np.abs(vals)) > envelope):
        return np.inf
    r = y - vals
    g = crit.moments(r)
    S = (crit.A * r[:, None] ** 2).T @ crit.A
    try:
        val = float(g @ solve(S, g, assume_a="pos"))
    except (np.linalg.LinAlgError, ValueError):
        val = float(g @ np.linalg.pinv(S) @ g)
    return val if np.isfinite(val) and val >= 0 else np.inf


def s_statistic(form, X, y, crit, theta0, bound: float = 10.0, n_starts: int = 3, seed: int = 0, envelope: float | None = None):
    """Stock–Wright's S statistic, min over theta of the AR statistic, from theta0 and perturbed starts."""
    theta0 = np.asarray(theta0, dtype=float)
    p = len(theta0)
    if p == 0:
        return ar_statistic(form, X, y, crit, theta0, envelope), theta0
    rng = np.random.default_rng(seed)

    def obj(t):
        return ar_statistic(form, X, y, crit, np.clip(t, -bound, bound), envelope)

    starts = [theta0] + [theta0 * (1 + 0.1 * rng.standard_normal(p)) + 0.05 * rng.standard_normal(p) for _ in range(n_starts - 1)]
    best_val, best_x = np.inf, theta0
    for s in starts:
        res = minimize(obj, np.clip(s, -bound, bound), method="Nelder-Mead", options=dict(xatol=1e-6, fatol=1e-6, maxfev=300 * p))
        if res.fun < best_val:
            best_val, best_x = float(res.fun), np.clip(res.x, -bound, bound)
    return best_val, best_x


def _jacobian(form, X, theta, rel: float = 1e-6) -> np.ndarray:
    D = np.empty((len(X), len(theta)))
    for j in range(len(theta)):
        h = rel * max(1.0, abs(theta[j]))
        e = np.zeros(len(theta))
        e[j] = h
        D[:, j] = (form(X, theta + e) - form(X, theta - e)) / (2 * h)
    return D


def wald_se(form, X, y, crit: MomentCriterion, theta) -> np.ndarray:
    """Standard errors of the two-step GMM estimate: V = (G' Omega^{-1} G)^{-1} / n with instruments sqrt(n) A."""
    theta = np.asarray(theta, dtype=float)
    n = len(y)
    r = y - form(X, theta)
    if not np.all(np.isfinite(r)) or len(theta) == 0:
        return np.full(len(theta), np.nan)
    A = crit.A
    Omega = (A * r[:, None] ** 2).T @ A
    G = A.T @ _jacobian(form, X, theta) / np.sqrt(n)
    V = np.linalg.pinv(G.T @ np.linalg.pinv(Omega) @ G) / n
    return np.sqrt(np.clip(np.diag(V), 0.0, None))


def _profile(form, X, y, crit, theta, j, value, bound, envelope):
    """AR minimized over the other constants with constant j fixed at `value`; warm start at theta."""
    p = len(theta)
    t = np.array(theta, dtype=float)
    t[j] = value
    if p == 1:
        return ar_statistic(form, X, y, crit, t, envelope), t
    free = [i for i in range(p) if i != j]

    def full(tf):
        out = t.copy()
        out[free] = np.clip(tf, -bound, bound)
        return out

    res = minimize(lambda tf: ar_statistic(form, X, y, crit, full(tf), envelope), t[free], method="Nelder-Mead",
                   options=dict(xatol=1e-5, fatol=1e-4, maxfev=150 * (p - 1)))
    return float(res.fun), full(res.x)


def ar_interval(form, X, y, crit, theta, j, step, bound: float = 10.0, level: float = 0.95, max_steps: int = 25,
                envelope: float | None = None):
    """Projection AR interval for constant j around theta (the S minimizer).

    The connected set of values whose profiled AR statistic is below chi2_{K, level}, found by stepping
    out geometrically from theta[j] and bisecting. Returns (lo, hi, lo_bounded, hi_bounded): an end that
    reaches the constant bound is unbounded. (nan, nan, False, False) if theta itself is rejected.
    """
    c = chi2.ppf(level, crit.K)
    a0, _ = _profile(form, X, y, crit, theta, j, theta[j], bound, envelope)
    if a0 > c:
        return np.nan, np.nan, False, False

    def endpoint(direction):
        inside, warm, h = theta[j], theta, step
        for _ in range(max_steps):
            v = inside + direction * h
            if direction * v >= bound:
                return direction * bound, False
            a, w = _profile(form, X, y, crit, warm, j, v, bound, envelope)
            if a <= c:
                inside, warm, h = v, w, h * 1.6
                continue
            lo, hi = inside, v  # bracket: lo accepted, hi rejected
            for _ in range(6):
                mid = (lo + hi) / 2
                a, w2 = _profile(form, X, y, crit, warm, j, mid, bound, envelope)
                if a <= c:
                    lo, warm = mid, w2
                else:
                    hi = mid
            return lo, True
        return direction * bound, False

    lo, lo_b = endpoint(-1.0)
    hi, hi_b = endpoint(1.0)
    return lo, hi, lo_b, hi_b


@dataclass
class CandidateCheck:
    expr: str
    S: float  # its S statistic
    in_set: bool  # S <= chi2_{K, level}: the data do not reject this form
    distance: float  # RMS(f_s - f_hat) / sd(f_hat) at the candidate's S minimizer, ignoring the 5% largest differences
    distance_full: float  # the same over the whole sample (a pole or a tail difference shows here, not above)


@dataclass
class IdentificationReport:
    verdict: str  # "identified" | "weakly identified" | "rejected"
    selected: str
    S_selected: float
    critical: float
    first_stage: FirstStage
    theta: list[float]
    se: list[float]
    ar_intervals: list[tuple[float, float]]
    ar_bounded: list[bool]
    width_ratio: list[float]  # AR interval width / Wald interval width; inf when unbounded
    formula_set: list[str]  # the selected formula and every candidate the data do not reject
    max_distance: float  # the farthest member of the formula set from the selected formula, in sd units
    candidates: list[CandidateCheck]
    reasons: list[str] = field(default_factory=list)


def identification_report(
    selected_expr,
    candidate_exprs,
    X: np.ndarray,
    y: np.ndarray,
    crit: MomentCriterion,
    bound: float = 10.0,
    level: float = 0.95,
    tau: float = 0.2,
    envelope_factor: float = 3.0,
    seed: int = 0,
) -> IdentificationReport:
    """Is the selected formula identified by the data? (module docstring)

    tau: a candidate the data do not reject counts as a different formula when its fit is more than
    tau standard deviations of f_hat away from f_hat (trimmed). On the Phase 4 runs, 0.2 flags every
    weak-instrument run and 5% of the strong-instrument runs whose selection was right; 0.1 flags 16%.
    envelope_factor: constants are restricted to formulas whose values on the sample stay within this
    multiple of max |y| (see `ar_statistic`).
    """
    d = X.shape[1]
    envelope = envelope_factor * float(np.max(np.abs(y)))
    keep = int(np.ceil(0.95 * len(y)))  # the distance ignores the 5% largest differences: a pole, or a tail the moments do not see
    form = parametrize(selected_expr, d)
    fit = fit_gmm(form, X, y, crit, bound=bound, seed=seed)
    theta_hat = fit.theta
    f_hat = form(X, theta_hat)
    sd = float(f_hat.std()) if np.all(np.isfinite(f_hat)) and f_hat.std() > 0 else 1.0
    se = wald_se(form, X, y, crit, theta_hat)
    c = float(chi2.ppf(level, crit.K))
    S_sel, theta_s = s_statistic(form, X, y, crit, theta_hat, bound, seed=seed, envelope=envelope)
    reasons: list[str] = []

    ar, ar_b, ratio = [], [], []
    if S_sel <= c:
        for j in range(form.n_constants):
            step = float(se[j]) if np.isfinite(se[j]) and se[j] > 0 else 0.05 * max(1.0, abs(theta_s[j]))
            lo, hi, lb, hb = ar_interval(form, X, y, crit, theta_s, j, step, bound, level, envelope=envelope)
            ar.append((float(lo), float(hi)))
            ar_b.append(bool(lb and hb))
            ok = lb and hb and np.isfinite(se[j]) and se[j] > 0
            ratio.append(float((hi - lo) / (2 * Z95 * se[j])) if ok else np.inf)
            if not (lb and hb):
                reasons.append(f"constant {form.params[j]}: the AR interval reaches the bound {bound:g}")

    checks: list[CandidateCheck] = []
    sel_form = str(form.form)
    for e in candidate_exprs:
        try:
            cf = parametrize(e, d)
        except Exception:
            continue
        if str(cf.form) == sel_form:
            continue
        cfit = fit_gmm(cf, X, y, crit, bound=bound, n_starts=2, seed=seed)
        S, th = s_statistic(cf, X, y, crit, cfit.theta, bound, n_starts=2, seed=seed, envelope=envelope)
        vals = cf(X, th)
        if np.all(np.isfinite(vals)):
            diff = np.sort((vals - f_hat) ** 2)
            dist, dist_full = float(np.sqrt(diff[:keep].mean()) / sd), float(np.sqrt(diff.mean()) / sd)
        else:
            dist = dist_full = np.inf
        checks.append(CandidateCheck(str(e), float(S), bool(S <= c), dist, dist_full))
    in_set = [ch for ch in checks if ch.in_set]
    D = max((ch.distance for ch in in_set), default=0.0)
    for ch in sorted(in_set, key=lambda ch: -ch.distance):
        if ch.distance > tau:
            reasons.append(f"not rejected (S = {ch.S:.1f} <= {c:.1f}), {ch.distance:.2f} sd away: {ch.expr}")

    if S_sel > c:
        verdict = "rejected"
        reasons.insert(0, f"the selected formula fails the moment conditions (S = {S_sel:.1f} > {c:.1f})")
    elif reasons:
        verdict = "weakly identified"
    else:
        verdict = "identified"
    selected = str(form.expr(theta_hat))
    return IdentificationReport(verdict, selected, float(S_sel), c, first_stage(X, crit), theta_hat.tolist(), se.tolist(),
                                ar, ar_b, ratio, [selected] + [ch.expr for ch in in_set], float(D), checks, reasons)
