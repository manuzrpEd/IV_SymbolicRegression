# Theory: selecting formulas with instruments

Phase 5 of the plan in [README.md](README.md) (§7, §11). This file states the setting, the assumptions and the results, with proofs. The Monte Carlo evidence each result explains is in README §12; the two simulations written for this phase are in §7.1 below and in [experiments/phase5/summary.md](experiments/phase5/summary.md).

Second pass (2026-10-01): every proof was re-derived line by line; §9 lists what was wrong in the first pass and what changed. Third pass (2026-10-01): two fresh-context referees (separate model instances with no memory of writing the document, one per half) read the proofs cold; §9 lists their findings and the fixes. The theorem statements and proofs stood; Proposition 5 and two informal readings did not, and were repaired. A human reading before submission remains advisable.

**Status**

| Result | What it says | Status |
|---|---|---|
| Lemma 1 | Bounded constants make the identification gap positive | Proved |
| Lemma 2 | Spline-GMM and kernel (MMR) criteria satisfy the conditions used below | Proved (standard tools) |
| Theorem 1 (i)–(ii) | Consistency and selection of a minimal true formula, for any candidate generator that covers the truth | Proved |
| Corollary 1.1 | Parametric rate $n^{-1/2}$ when the law is in the class | Proved |
| Theorem 1 (iii) | Split-sample normality, Hansen's $J$, Anderson–Rubin sets | Proved (standard GMM results, applied conditionally); simulated in §7.1 |
| Proposition 5 | An identification-robust confidence set for the formula: the diagnostic that reports weak identification instead of a formula | Proved for the plain statistic; the two implementation guards (sample envelope, winsorized weight) need condition (E) and a slowly growing cap, stated with their costs; evaluated on the Phase 4 runs in §7.1 |
| Theorem 2 | Finite-sample selection bound with two failure channels, separation and complexity; all constants explicit | Proved for GMM with population-orthonormal instruments, a known scale, sub-Gaussian errors and a bounded Lipschitz class |
| Corollary 2.2 | A per-node structure penalty makes the bound uniform in the maximal formula size | Proved; its constants certify nothing at practical $n$, so it fixes the direction of the structure term, not its weight (§4, Numbers) |
| Corollary 2.3 | Candidates from an independent sample shrink the union bound to the candidate set | Proved; simulated in §7.1 |
| Proposition 2.4 | The bound survives perturbed weights: the code's sample-orthonormalized criterion, an estimated common scale (one more event) | Proved |
| Proposition 4 (a)–(b) | Discrete instruments: formulas with $\ge J$ constants can zero the criterion | Proved |
| Conjecture 4 (c) | Fewer constants than support points: generically identified | Precise transversality hypothesis stated; a design family of dimension $\ge J - p_s$ is needed. *Beyond the paper* |
| Theorem 3 (a) | Fixed size, misspecified law: convergence to the pseudo-true set | Proved |
| Theorem 3 (b) | Growing size: consistency on a compact support, any number of regressors | Proved. The unbounded-support version is *beyond the paper* |
| Proposition 3.3 | Rates for growing size reduce to a modulus of continuity on the sieve | Proved; bounding the modulus is open. *Beyond the paper* |
| Kernel criterion, exact | Theorem 2 for the $O(n^2)$ kernel criterion | Open (the Nyström version used in the code is covered). *Beyond the paper* |

**Scope for the paper.** The paper contains Theorems 1 and 2 with their corollaries and Propositions 2.4 and 5, Theorem 3 (a) and (b) on a compact support, Proposition 4 (a)–(b), and the simulations of §7.1. Four items are **beyond the paper**; they are marked as such where they appear below and will be stated as open problems in the paper, not resolved:
1. the rate problem for growing formula size (Proposition 3.3: bounding the sieve modulus);
2. Theorem 3 (b) on an unbounded support (§6, remark);
3. Theorem 2 for the exact kernel criterion and for the estimation error of an efficient weight under heteroskedasticity (§4, remarks);
4. Conjecture 4 (c), generic identification below $J$ constants (§5).

---

## 0. Setting

**Data.** Observations $W_i = (y_i, X_i, Z_i)$, $i = 1, \dots, n$, are i.i.d. copies of $W = (y, X, Z)$, with $X \in \mathcal X \subseteq \mathbb R^d$.

**Model.**

$$y = f_0(X) + u, \qquad E[u \mid Z] = 0, \qquad E[y^2] < \infty.$$

Write $\lVert \cdot \rVert$ for $L^2$ norms, and let $T$ be the conditional-expectation operator, $(Th)(z) = E[h(X) \mid Z = z]$, from $L^2(P_X)$ to $L^2(P_Z)$. It satisfies $\lVert Th \rVert \le \lVert h \rVert$.

**Formulas.**
- **Trees.** A tree $s$ is an expression tree over an alphabet of $m$ symbols: binary and unary operators, the $d$ variables, and a constant placeholder. It has $\ell_s$ nodes and $p_s$ constant placeholders, and defines $f_s(x;\theta)$ for $\theta$ in its parameter set $\Theta_s$.
- **Parameter sets.** $\Theta_s$ is a closed subset of $[-C, C]^{p_s}$ on which $f_s(\cdot;\theta)$ is finite on the support of $X$ and (A3) below holds; it is compact. Where the formula is finite everywhere, $\Theta_s$ is the whole cube. For $\log(x - c)$ on a support bounded below by $x_{\mathrm{lo}}$, it is $\{c \le x_{\mathrm{lo}} - \eta\}$ for some margin $\eta > 0$. The code discards candidates whose refit gives non-finite residuals, which is the sample version of this restriction.
- **Formula class.** $\mathcal S_L$ is the set of trees with at most $L$ nodes. Write $\mathcal F_s = \{f_s(\cdot;\theta) : \theta \in \Theta_s\}$ and $\mathcal F_L = \bigcup_{s \in \mathcal S_L} \mathcal F_s$.
- **How many trees.** Unary-binary plane trees with $\ell$ nodes are counted by a Motzkin number, which is at most $3^{\ell}$. Each node gets one of $m$ labels, so there are at most $(3m)^{\ell}$ trees of size $\ell$ (an overcount: labels must match arities), and

  $$\log\lvert\mathcal S_L\rvert \le L\log(3m) + \log 2.$$

**True trees.**
- **(A0) Well-specified:** $f_0 \in \mathcal F_L$.
- **True and wrong trees.** $\mathcal S_0 = \{s : f_0 \in \mathcal F_s\}$ is the set of true trees, equality being in $L^2(P_X)$. Every other tree in $\mathcal S_L$ is *wrong*: $f_s(\cdot;\theta) \ne f_0$ for every $\theta \in \Theta_s$.
- **Minimal true trees.** $p_0 = \min_{s \in \mathcal S_0} p_s$ is the smallest number of constants that can represent $f_0$. The minimal true trees are $\mathcal S_0^{\min} = \{s \in \mathcal S_0 : p_s = p_0\}$.
- **Zero sets.** For $s \in \mathcal S_0$, $\Theta_s^0 = \{\theta \in \Theta_s : f_s(\cdot;\theta) = f_0\}$.

$\mathcal S_0^{\min}$ usually has several elements; for example, $a + b\log x$ and $\log(c\,x^{b})$ are both minimal trees for the log law. "Recovering the form" means selecting *some* element of $\mathcal S_0^{\min}$. That is exactly the Monte Carlo's criterion: refit the constants to the noise-free $f_0$, then require an exact fit and $p \le p_0$.

**Assumptions.**
- **(A1)** $E[u \mid Z] = 0$.
- **(A2) Restricted identification:** for $f \in \mathcal F_L$, $T(f - f_0) = 0$ implies $f = f_0$.
- **(A3) Regularity:** for every $s$ and every $x$, $\theta \mapsto f_s(x;\theta)$ is continuous on $\Theta_s$, and $\sup_{\theta \in \Theta_s} \lvert f_s(x;\theta)\rvert \le F(x)$ with $E[F(X)^2] < \infty$.

**Estimator.** Given a sample criterion $Q_n$ (Section 2), the estimator works in three steps:
1. **Refit.** Each candidate $s$ gets $\hat\theta_s \in \arg\min_{\theta \in \Theta_s} Q_n(f_s(\cdot;\theta))$; write $\hat Q_s = Q_n(f_s(\cdot;\hat\theta_s))$.
2. **Select.**

   $$\hat s \in \arg\min_{s \in \hat{\mathcal S}} \ \mathrm{crit}_n(s), \qquad \mathrm{crit}_n(s) = \frac{n\hat Q_s}{\hat\sigma^2} + \mathrm{pen}_n(s), \qquad \mathrm{pen}_n(s) = p_s\kappa_n + w\,\ell_s\log m.$$

   Ties go to fewer constants, then fewer nodes.
3. **Estimate.** $\hat f = f_{\hat s}(\cdot;\hat\theta_{\hat s})$.

The ingredients:
- $\hat{\mathcal S} \subseteq \mathcal S_L$ is the candidate set, from any generator;
- $\hat\sigma^2 \to_p \sigma_*^2 \in (0, \infty)$ is the scale that turns $nQ_n$ into a $J$ statistic (exactly so with the 2SLS weight under conditional homoskedasticity $E[u^2 \mid Z] = \sigma^2$, or with the efficient weight; Theorem 1 needs only the $O_p(1)$ bound (C3), not the $\chi^2$ calibration);
- $\kappa_n$ is the per-constant penalty: $\ln n$ (BIC), $2.01\ln\ln n$ (HQIC) or $2$ (AIC);
- $w \ge 0$ is the weight of the structure term.

This is the rule of Phases 2–4. MMSC-BIC (README §6.3) is $\kappa_n = \ln n$, $w = 0$, since $J - (K - p)\ln n = \mathrm{crit}_n - K\ln n$. "BIC + structure" is $w = 0.5$ or $1$. In the code the alphabet has $m = 10$ symbols for one regressor: six binary operators, two unary, the constant, the variable.

**Coverage** is the event $\{\hat{\mathcal S} \cap \mathcal S_0^{\min} \neq \emptyset\}$: the candidates contain a minimal true tree. If it fails, the failure is a search failure. Coverage is not guaranteed by anything below: it is a property of the generator, and the Monte Carlo reports it separately.

---

## 1. Identification on a bounded formula class

**Lemma 1.** Under (A2)–(A3):

(a) $\theta \mapsto f_s(\cdot;\theta)$ is continuous from $\Theta_s$ into $L^2(P_X)$, so each $\mathcal F_s$, and therefore $\mathcal F_L$, is compact.

(b) Every wrong tree has a positive separation $\delta_s := \min_{\theta \in \Theta_s} \lVert T(f_s(\cdot;\theta) - f_0)\rVert^2 > 0$. Hence $\delta_L := \min_{s \notin \mathcal S_0} \delta_s > 0$.

(c) For every $\varepsilon > 0$,

$$\omega_L(\varepsilon) := \inf\{\lVert T(f - f_0)\rVert^2 : f \in \mathcal F_L,\ \lVert f - f_0\rVert \ge \varepsilon\} > 0.$$

*Proof.*
- (a) If $\theta_k \to \theta$ in $\Theta_s$, then $f_s(x;\theta_k) \to f_s(x;\theta)$ for every $x$, and $\lvert f_s(x;\theta_k) - f_s(x;\theta)\rvert^2 \le 4F(x)^2$. Dominated convergence gives $L^2$ convergence. A continuous image of a compact set is compact, and a finite union of compact sets is compact.
- (b) $\theta \mapsto \lVert T(f_s(\cdot;\theta) - f_0)\rVert^2$ is continuous, by (a) and $\lVert T\rVert \le 1$. It is positive on $\Theta_s$ by (A2), because a wrong tree never equals $f_0$. A positive continuous function on a compact set has a positive minimum.
- (c) The set $\{f \in \mathcal F_L : \lVert f - f_0\rVert \ge \varepsilon\}$ is closed in the compact $\mathcal F_L$, hence compact. The map $f \mapsto \lVert T(f - f_0)\rVert^2$ is continuous, and by (A2) it is positive there. $\blacksquare$

**Remark (ill-posedness).** $\omega_L$ is the modulus of continuity of $T^{-1}$ at $f_0$, restricted to $\mathcal F_L$.
- **Why bounded constants regularize.** Over a ball of functions, the analogous modulus is zero; that is why nonparametric IV is ill-posed. Over bounded-constant formulas of bounded size it is positive.
- **What it does not give.** It gives no rate: $\omega_L(\varepsilon)$ can be tiny, and it shrinks as $L$ or $C$ grows.
- **Link to §7 of the README.** The separation constant $\delta_L$ is the part of this modulus that comes from wrong trees.

---

## 2. Criteria

All results below use three properties of a sample criterion $Q_n$ and its population limit $Q$:

- **(C1)** $Q \ge 0$, $Q$ is continuous on $\mathcal F_L$ in the $L^2$ norm, and for $f \in \mathcal F_L$: $Q(f) = 0 \iff f = f_0$.
- **(C2)** $\sup_{f \in \mathcal F_L} \lvert Q_n(f) - Q(f)\rvert \to_p 0$.
- **(C3)** $n\,Q_n(f_0) = O_p(1)$.

**Lemma 2.**

(a) **Spline-GMM (criterion (b) of README §6.2).**
- *Setting.* Fix $K$. The instruments $b(Z) \in \mathbb R^K$ have $E[bb']$ nonsingular, $E[\lVert b\rVert^2 (y^2 + F(X)^2)] < \infty$ and $E[\lVert b\rVert^2 u^2] < \infty$.
- *Criterion.* $Q_n(f) = \hat g(f)'\hat W \hat g(f)$, where $\hat g(f) = n^{-1}\sum_i b(Z_i)\,(y_i - f(X_i))$ and $\hat W \to_p W$ is positive definite. With 2SLS weights $\hat W = (n^{-1}\sum_i b_i b_i')^{-1}$, this is the code's $\lVert A'r\rVert^2/n$, and $Q(f) = \lVert \Pi_K T(f_0 - f)\rVert^2$, where $\Pi_K$ projects onto $\mathrm{span}(b)$.
- *Result.* (C2) and (C3) hold. (C1) holds if and only if

  **(A2$_K$)** for $f \in \mathcal F_L$, $\Pi_K T(f - f_0) = 0$ implies $f = f_0$.

(b) **Kernel MMR (criterion (c)).**
- *Setting.* The kernel $k$ is bounded ($\sup_z k(z,z) \le \bar\kappa$), continuous on a separable space of instruments (so its RKHS $\mathcal H$ is separable and $z \mapsto k(z,\cdot)$ is Bochner integrable), and integrally strictly positive definite.
- *Criterion.* $Q_n(f) = n^{-2}\sum_{i,j} r_i r_j\, k(Z_i, Z_j)$ with $r_i = y_i - f(X_i)$. Its limit is $Q(f) = E[\,T(f_0 - f)(Z)\; T(f_0 - f)(Z')\; k(Z, Z')\,]$, with $Z'$ an independent copy of $Z$.
- *Result.* (C1) holds under (A2) alone, and (C2)–(C3) hold under (A3) and $E[y^2] < \infty$.

*Proof.*
- **(a), (C2).** The uniform law of large numbers ([Newey & McFadden 1994](https://doi.org/10.1016/S1573-4412(05)80005-4), Lemma 2.4) applies to $\theta \mapsto b(z)(y - f_s(x;\theta))$ on each compact $\Theta_s$. The map is continuous, with integrable envelope $\lVert b(z)\rVert(\lvert y\rvert + F(x))$ (integrable by Cauchy–Schwarz). There are finitely many trees, and $\hat W \to_p W$.
- **(a), (C3).** $\sqrt n\,\hat g(f_0) = n^{-1/2}\sum_i b(Z_i)u_i$ has mean zero, because $E[bu] = E[b\,E(u \mid Z)] = 0$. Its second moment is $E[\lVert b\rVert^2u^2] < \infty$, so it is $O_p(1)$ by Chebyshev's inequality.
- **(a), (C1).** $Q(f) = 0$ if and only if $g(f) = 0$, if and only if $\Pi_K T(f_0 - f) = 0$. Continuity follows from $\lVert g(f) - g(f')\rVert \le (E\lVert b\rVert^2)^{1/2}\lVert f - f'\rVert$.
- **(b), (C2).** Write $Q_n(f) = \lVert n^{-1}\sum_i r_i\varphi(Z_i)\rVert_{\mathcal H}^2$ with $\varphi(z) = k(z, \cdot)$ and $\lVert\varphi(z)\rVert_{\mathcal H} \le \sqrt{\bar\kappa}$. The same uniform-law argument works in the separable Hilbert space $\mathcal H$, using Mourier's strong law at the grid points.
- **(b), (C3).** $E\lVert n^{-1/2}\sum_i u_i\varphi(Z_i)\rVert_{\mathcal H}^2 = E[u^2k(Z,Z)] \le \bar\kappa E[u^2]$. The cross terms vanish because $E[u\varphi(Z)] = 0$.
- **(b), (C1).** $Q(f) = \lVert E[T(f_0 - f)(Z)\varphi(Z)]\rVert_{\mathcal H}^2$. Continuity: $\lVert E[h\varphi]\rVert_{\mathcal H} \le \sqrt{\bar\kappa}\,\lVert h\rVert$ and $\lVert T\rVert \le 1$. For an integrally strictly positive definite kernel, $\lVert E[h(Z)\varphi(Z)]\rVert_{\mathcal H} = 0$ only if the finite signed measure $h\,dP_Z$ vanishes, i.e. $h = 0$ almost surely ([Zhang et al. 2020](https://arxiv.org/abs/2010.07684); Muandet et al. 2020). $\blacksquare$

**Remark.** (A2$_K$) is stronger than (A2), and it fails for discrete instruments once formulas have many constants (Section 5). The kernel criterion needs only (A2). That is one argument for the kernel criterion; in Phase 4 kernel instruments were also slightly better at selection (54% vs. 51% recovery).

---

## 3. Theorem 1: consistency and selection

**Theorem 1.** Assume (A0), (A1), (A3), and a criterion satisfying (C1)–(C3). Let $\kappa_n \to \infty$ with $\kappa_n/n \to 0$, let $w \ge 0$ be fixed, and let $\hat\sigma^2 \to_p \sigma_*^2 \in (0,\infty)$. The candidate set $\hat{\mathcal S}$ may depend on the data in any way.

(i) If $P(\hat{\mathcal S} \cap \mathcal S_0 \neq \emptyset) \to 1$, then $\lVert \hat f - f_0\rVert \to_p 0$.

(ii) If $P(\hat{\mathcal S} \cap \mathcal S_0^{\min} \neq \emptyset) \to 1$, then $P(\hat s \in \mathcal S_0^{\min}) \to 1$.

*Proof.*

**Setup.** Let $R_n := \sup_{f \in \mathcal F_L}\lvert Q_n(f) - Q(f)\rvert = o_p(1)$, by (C2). Let $E_n$ be the coverage event. On $E_n$, pick $s^* \in \hat{\mathcal S} \cap \mathcal S_0$ (for (ii), in $\mathcal S_0^{\min}$) and $\theta^* \in \Theta_{s^*}^0$. Then $\hat Q_{s^*} \le Q_n(f_0)$, so

$$\mathrm{crit}_n(s^*) \le \frac{n\,Q_n(f_0)}{\hat\sigma^2} + \mathrm{pen}_n(s^*) = O_p(1) + O(\kappa_n). \tag{3.1}$$

**(i)**
1. Because $\hat s$ minimizes $\mathrm{crit}_n$ over $\hat{\mathcal S}$ and penalties are nonnegative, $n\hat Q_{\hat s}/\hat\sigma^2 \le \mathrm{crit}_n(s^*)$.
2. Then $\hat Q_{\hat s} \le \hat\sigma^2\,\mathrm{crit}_n(s^*)/n = o_p(1)$, by (3.1) and $\kappa_n/n \to 0$.
3. Hence $Q(\hat f) \le \hat Q_{\hat s} + R_n = o_p(1)$.
4. Fix $\varepsilon > 0$. By (C1) and Lemma 1(a), $\eta(\varepsilon) := \inf\{Q(f) : f \in \mathcal F_L,\ \lVert f - f_0\rVert \ge \varepsilon\} > 0$, since it is the infimum of a positive continuous function over a compact set.
5. So $P(\lVert\hat f - f_0\rVert \ge \varepsilon) \le P(Q(\hat f) \ge \eta(\varepsilon)) + P(E_n^c) \to 0$.

**(ii), wrong trees.** For a wrong $s$, $\delta_s^Q := \min_\theta Q(f_s(\cdot;\theta)) > 0$, by (C1) and compactness. On $E_n$,

$$\mathrm{crit}_n(s) \ge n\hat Q_s/\hat\sigma^2 \ge n(\delta_s^Q - R_n)/\hat\sigma^2.$$

This exceeds $\mathrm{crit}_n(s^*) = O_p(\kappa_n) = o_p(n)$ with probability tending to one. There are finitely many wrong trees, so $P(\hat s \notin \mathcal S_0) \to 0$.

**(ii), over-parameterized true trees.** For $s \in \mathcal S_0$ with $p_s > p_0$, since $\hat Q_s \ge 0$,

$$\mathrm{crit}_n(s) - \mathrm{crit}_n(s^*) \ \ge\ (p_s - p_0)\kappa_n + w(\ell_s - \ell_{s^*})\log m - \frac{nQ_n(f_0)}{\hat\sigma^2} \ \ge\ \kappa_n - wL\log m - O_p(1) \to \infty.$$

So $P(\hat s \in \mathcal S_0,\ p_{\hat s} > p_0) \to 0$. Every tree outside $\mathcal S_0^{\min}$ is wrong or over-parameterized, there are finitely many, and each loses to $s^*$ with probability tending to one; therefore $P(\hat s \in \mathcal S_0^{\min}) \to 1$. $\blacksquare$

**Remarks.**
1. **Little is needed near the truth.** The proof needs no interior true constants, no rank condition and no $\chi^2$ limit. It uses only (C3), an $O_p(1)$ bound at the truth, and the linear growth of the criterion for wrong trees. Over-parameterized trees, whose extra constants are unidentified ([Andrews & Cheng 2012](https://doi.org/10.3982/ECTA9456)), do no harm to selection: they lose on the penalty.
2. **Penalties.**
   - BIC and HQIC satisfy $\kappa_n \to \infty$ and $\kappa_n/n \to 0$; AIC does not. Under AIC, over-parameterized true trees win with probability that does not vanish: when $s \supset s^*$ are nested, regular ((A5) below), the extra constants are identified and both $J$ statistics use the same efficient weight (or the 2SLS weight under conditional homoskedasticity), $J_n(s^*) - J_n(s) \to_d \chi^2_{p_s - p_0}$, so $P(\mathrm{crit}_n(s) < \mathrm{crit}_n(s^*)) \to P(\chi^2_{k} > 2k) > 0$ with $k = p_s - p_0$. Phases 2 and 4 found AIC the worst rule.
   - The structure term is bounded by $wL\log m$, so it does not affect consistency. Its role is in finite samples (Theorem 2).
3. **Any generator works.** (ii) holds for every generator whose candidates contain a minimal true tree with probability tending to one. This is the formal version of the Phase 4 finding that the instrument is needed when formulas are scored, not when they are generated.
   - The plain squared-error PySR front qualifies whenever it covers. It covered in 62% of runs, and in all runs of the strong-endogeneity $n$-scaling cells.
   - Selecting by squared error converges to the conditional-mean formula, however large $n$ is.
4. **The cross-fitted criterion has no $\kappa_n$.** Over-parameterized true trees therefore tie with minimal ones in the limit. The criterion is consistent for $f$ but not for the minimal tree, and the Monte Carlo's recovery metric ($p \le p_0$) counts those ties as failures (28% recovery in Phase 4).

### Corollary 1.1: the rate when the law is in the class

**Assumption (A5)**, for a tree $s \in \mathcal S_0^{\min}$ and the GMM criterion of Lemma 2(a) (whose setting, in particular $E[\lVert b\rVert^2(y^2 + F(X)^2)] < \infty$, is in force) with (A2$_K$):
- (a) $\Theta_s^0$ is a finite set of interior points of $\Theta_s$. It is a singleton for most trees; a sign-symmetric tree such as $(ax)^2$ has two zeros, $\pm a_0$. Write $\theta_{0s}$ for the element of $\Theta_s^0$ nearest to $\hat\theta_s$ (the unique element when there is one).
- (b) $f_s(x;\cdot)$ is continuously differentiable on a neighbourhood $\mathcal N$ of each point of $\Theta_s^0$, with $E[\lVert b(Z)\rVert^2 \sup_{\mathcal N}\lVert\partial_\theta f_s\rVert^2] < \infty$.
- (c) $G_s := E[b(Z)\,\partial_\theta f_s(X;\theta)']$ has full column rank $p_0$ at every $\theta \in \Theta_s^0$.
- (d) $\Omega := E[b(Z)b(Z)'u^2]$ is positive definite.

**Corollary 1.1.** Under the assumptions of Theorem 1(ii), with the GMM criterion of Lemma 2(a), (A2$_K$), and (A5) for every $s \in \mathcal S_0^{\min}$: $\lVert\hat\theta_{\hat s} - \theta_{0\hat s}\rVert = O_p(n^{-1/2})$. If moreover $\lVert f_s(\cdot;\theta) - f_s(\cdot;\theta')\rVert \le \Lambda\lVert\theta - \theta'\rVert$ for $\theta, \theta'$ near $\Theta_s^0$ and every $s \in \mathcal S_0^{\min}$, then $\lVert\hat f - f_0\rVert = O_p(n^{-1/2})$.

*Proof.* For a fixed $s \in \mathcal S_0^{\min}$, $\hat\theta_s$ is a GMM estimator (first step, or the two-step one) of a correctly specified moment model whose population moment vanishes exactly on the finite set $\Theta_s^0$, by (A2$_K$) and (A5)(a). Consistency to that set, $\mathrm{dist}(\hat\theta_s, \Theta_s^0) \to_p 0$, follows from the uniform law of Lemma 2(a) and compactness as in Newey & McFadden (1994, Theorem 2.1); with probability tending to one $\hat\theta_s$ then lies in a neighbourhood of a single zero $\theta_{0s}$, on which the moment model is identified, and the local argument of their Theorem 3.4, with the regularity (A5)(b)–(d), gives $\sqrt n(\hat\theta_s - \theta_{0s}) = O_p(1)$. Then, for any $M$,

$$P\bigl(\sqrt n\lVert\hat\theta_{\hat s} - \theta_{0\hat s}\rVert > M\bigr) \le \sum_{s \in \mathcal S_0^{\min}} P\bigl(\sqrt n\lVert\hat\theta_s - \theta_{0s}\rVert > M\bigr) + P(\hat s \notin \mathcal S_0^{\min}),$$

which is small for $M$ and then $n$ large. The function bound follows from the Lipschitz property. $\blacksquare$

The rate in the misspecified, growing-size case is a different matter (Proposition 3.3).

### Theorem 1 (iii): inference after selection

**Procedure.**
1. Split the sample into $A$ (size $n_A$) and $B$ (size $n_B = n - n_A$), with $n_A/n \to a \in (0,1)$, by a rule that does not depend on the data (fixed index sets, or external randomization).
2. Compute $\hat s$ on $A$ only: the candidate generator, the scale $\hat\sigma^2$ and the refits that the selection uses all run on $A$ alone, so that $\hat s$ is a function of $A$.
3. On $B$, estimate the constants of $\hat s$ by two-step efficient GMM with fixed $K$; call the result $\tilde\theta$.

**Assumptions.** The conditions of (ii) hold on $A$, together with (A2$_K$); the setting of Lemma 2(a) holds, and every $s \in \mathcal S_0^{\min}$ satisfies (A5).

**Result.** With $\hat V$ the usual estimator of $V_{\hat s} = (G_{\hat s}'\Omega^{-1}G_{\hat s})^{-1}$,

$$\hat V^{-1/2}\sqrt{n_B}\,(\tilde\theta - \theta_{0\hat s}) \to_d N(0, I_{p_0}), \qquad J_B \to_d \chi^2_{K - p_0}\ \ (K > p_0).$$

**With (A5)(c) dropped**, but (A2$_K$) and (A5)(a) kept, so that $\hat s \in \mathcal S_0^{\min}$ with probability tending to one and $\theta_{0\hat s}$ is defined: at $\theta = \theta_{0\hat s}$ the Anderson–Rubin statistic $\mathrm{AR}_B(\theta) = n_B\,\hat g_B(\theta)'\hat\Omega_B(\theta)^{-1}\hat g_B(\theta)$ converges to $\chi^2_K$, so $\{\theta : \mathrm{AR}_B(\theta) \le \chi^2_{K,1-\alpha}\}$ covers $\theta_{0\hat s}$ with probability tending to $1 - \alpha$ ([Stock & Wright 2000](https://doi.org/10.1111/1468-0262.00151)). This is pointwise in the data-generating process: the constants may be weakly identified in the sense that $G_{\hat s}$ is rank deficient, but nothing is claimed along drifting weak-instrument sequences, where selection itself fails (Theorem 2). Proposition 5 is the statement that holds without any rank condition.

*Proof.*
1. **Fixed tree.** Fix $s \in \mathcal S_0^{\min}$. On $B$, $\tilde\theta(s)$ is the efficient GMM estimator of a fixed, correctly specified moment model. (A2$_K$) and (A5)(a) give identification up to the finite set $\Theta_s^0$ of isolated zeros, and the asymptotics are those of the zero nearest $\tilde\theta(s)$, as in the proof of Corollary 1.1. Normality and the $J$ limit are then [Hansen (1982)](https://doi.org/10.2307/1912775) and Newey & McFadden (1994, Theorems 2.6 and 3.4); the consistency of $\hat\Omega$ and $\hat V$ uses $E[\lVert b\rVert^2\sup_\theta(y - f_s(X;\theta))^2] < \infty$, which Lemma 2(a)'s setting provides.
2. **Selected tree.** $\hat s$ is a function of $A$, and $A$ is independent of $B$ because the split does not depend on the data. So for any bounded continuous $\phi$, with $S_B(s)$ the studentized statistic for tree $s$,

   $$\bigl\lvert E\phi(S_B(\hat s)) - E\phi(N)\bigr\rvert \le \sum_{s \in \mathcal S_0^{\min}} P(\hat s = s)\,\bigl\lvert E\phi(S_B(s)) - E\phi(N)\bigr\rvert + 2\lVert\phi\rVert_\infty P(\hat s \notin \mathcal S_0^{\min}) \to 0.$$

3. **Other statistics.** The same argument covers $J_B$ and $\mathrm{AR}_B$. The AR limit uses only the CLT for $\sqrt{n_B}\,\bar u_B$ and $\hat\Omega_B \to_p \Omega$. $\blacksquare$

**Remarks.**
- **Pointwise only.** The result is pointwise in the data-generating process, not uniform ([Leeb & Pötscher 2005](https://doi.org/10.1017/S0266466605050036)).
- **Report tree-invariant targets.** Different minimal trees parametrize $f_0$ differently. Report quantities that do not depend on the tree, such as $f_0(x)$ or elasticities at given points, using the delta method.
- **Two kinds of weak identification.** Selection needs the *formula* to be strongly identified ($\delta_s$ large relative to $1/n$). Inference about constants can tolerate weakly identified *constants* through AR sets. Under weak instruments (design D5) it is the first that fails (Theorem 2).
- **Simulation.** §7.1 checks the coverage of these intervals on fresh samples against same-sample inference after selection, and the AR coverage under the weak instrument.

### 3.2 Proposition 5: a confidence set for the formula, and the identification diagnostic

Selection and the intervals of (iii) assume that the formula is identified. Under a weak instrument (design D5) the selection returns a wrong formula with a good fit, and nothing in the output says so. The Anderson–Rubin statistic is valid without any rank condition, so it can be turned into a diagnostic. This is implemented in `symiv.identification`.

**Setting.** GMM instruments $b(Z) \in \mathbb R^K$ with $K$ fixed, $E[\lVert b\rVert^2u^2] < \infty$, and $\Omega := E[bb'u^2]$ positive definite. For a tree $s$ and $\theta \in \Theta_s$,

$$\mathrm{AR}_s(\theta) := n\,\hat g(s,\theta)'\hat\Omega_s(\theta)^{-1}\hat g(s,\theta), \qquad \hat\Omega_s(\theta) := \frac1n\sum_i b(Z_i)b(Z_i)'\bigl(y_i - f_s(X_i;\theta)\bigr)^2,$$

the weight being evaluated at the same $\theta$ (the continuously-updated objective). The **S statistic** of a tree is $S_s := \min_{\theta \in \Theta_s}\mathrm{AR}_s(\theta)$ ([Stock & Wright 2000](https://doi.org/10.1111/1468-0262.00151)), and the **formula confidence set** of a candidate set $\hat{\mathcal S}$ is

$$\mathcal C_\alpha := \{s \in \hat{\mathcal S} : S_s \le \chi^2_{K,1-\alpha}\}.$$

Two implementation details guard against a weakness of the robust weight, which discounts exactly the observations a formula misfits most. Proposition 5 is stated for the plain statistic on $\Theta_s$; what each guard costs is stated after the proof.
- **The sample envelope.** The implementation restricts $\Theta_s$ to $\{\theta : \max_i\lvert f_s(X_i;\theta)\rvert \le 3\max_i\lvert y_i\rvert\}$, a sample version of (A3)'s envelope. Without it, $\mathrm{AR}_s(\theta)$ can be small at absurd constants: when a few observations dominate the residuals, $\hat\Omega_s(\theta)$ is dominated by them and the statistic collapses to roughly the number of those observations. The envelope is data-dependent, so for the true tree to stay feasible it needs
  **(E)** $P\bigl(\max_i\lvert f_0(X_i)\rvert \le 3\max_i\lvert y_i\rvert\bigr) \to 1$,
  which (A1) alone does not imply: an error that systematically offsets the law where it is largest (for instance $u = -0.9\,(X - E[X \mid Z])$, which satisfies (A1)) can violate it. (E) holds when the error at the observation with the largest $\lvert f_0\rvert$ is at most two thirds of that value with probability tending to one, and for a bounded $f_0$ whenever $P(\lvert y\rvert > \lVert f_0\rVert_\infty/3) > 0$, since some observation then exceeds the threshold with probability tending to one. It holds in every Monte Carlo design here.
- **The winsorized weight.** Inside $\hat\Omega_s(\theta)$ only, the residuals are winsorized at $c_n$ robust standard deviations of the formula's own residuals at its two-step fit (never below their 99.5% quantile), with $c_n := \max(5, \sqrt{2\ln n})$; the moments $\hat g$ keep the full residuals. A formula that misfits 2% of the sample by five or more standard deviations would otherwise inflate its own weight by a factor near two and halve the power of the test against it (observed in the Phase 6 labour environment). At the true form the residuals are the errors, so the cap sits at about five error standard deviations at every sample size used here ($\sqrt{2\ln n} < 5$ for $n < 270{,}000$); the slow growth makes the capped statistic asymptotically exact, and its finite-sample size is stated in the remark after the proof.

**Proposition 5.**

(a) **Coverage, without identification.** Under (A1) and the setting above, for every true tree $s_0 \in \mathcal S_0$ and $\theta_0 \in \Theta_{s_0}^0$, $\mathrm{AR}_{s_0}(\theta_0) \to_d \chi^2_K$. Hence, for any candidate set $\hat{\mathcal S}$, data-dependent or not,

$$\limsup_n P\bigl(s_0 \in \hat{\mathcal S},\ s_0 \notin \mathcal C_\alpha\bigr) \le \alpha.$$

Neither (A2), nor (A2$_K$), nor a rank condition is used: the statement holds however weak the instrument is.

(b) **Detection of statistical failures.** Let $E$ be the event that the selected tree $\hat s$ is wrong while $s_0 \in \hat{\mathcal S}$. Then

$$\limsup_n P\bigl(E \cap \{s_0 \notin \mathcal C_\alpha\}\bigr) \le \alpha:$$

among all samples, those in which a wrong formula is selected, the true form is a candidate, and the confidence set nevertheless fails to contain it are at most a fraction $\alpha$ in the limit. This is a joint, not a conditional, statement: given $E$, the miscoverage is at most $(\alpha + o(1))/P(E)$, informative when $E$ is not rare, and (a) gives nothing sharper because $E$ and $\{\mathrm{AR}_{s_0}(\theta_0) > \chi^2_{K,1-\alpha}\}$ are driven by the same sample. (In the 630 Phase 4 breadth runs $E$ occurred 146 times, and $\mathcal C_\alpha$ contained $s_0$ in 145 of them; §7.1.) When $s_0 \in \mathcal C_\alpha$ it is a tree of a form different from $\hat s$'s, and the diagnostic reports it as "a formula the data also allow" when its S-minimizing fit differs from $\hat f$ by more than $\tau$ standard deviations of $\hat f$, in a trimmed root mean square that discards the 5% largest differences (a pole, or a tail that the moments do not see); the scale is the sample standard deviation of $\hat f$, floored at a tenth of that of $y$, so that a flat selected formula (whose own spread is rounding noise) still measures its alternatives against a meaningful scale. Asymptotically, if the S-minimizing fit of $s_0$ converges to $f_0$ (which (A2$_K$) gives: the strongly identified case) and the trimmed scale converges, $s_0$ is reported whenever the limit of $\hat f$ is more than $\tau$ from $f_0$ in that metric. Near-duplicates within $\tau$ are not reported, by design: the function is then identified even though the tree is not minimal.

(c) **Link to identification.** Assume (A3), (A2$_K$), $\sup_z\lVert b(z)\rVert \le \zeta_K$, and (C2) for the identity-weight criterion (the sample envelope is not needed here). Then the set of functions the data do not reject,

$$\mathcal G_\alpha := \{f_s(\cdot;\theta) : s \in \mathcal S_L,\ \theta \in \Theta_s,\ \mathrm{AR}_s(\theta) \le \chi^2_{K,1-\alpha}\},$$

satisfies $\sup_{f \in \mathcal G_\alpha}\lVert f - f_0\rVert \to_p 0$. Without (A2$_K$), nothing forces it to shrink; the width of $\mathcal G_\alpha$ is what the diagnostic measures.

*Proof.*
- (a) At $(s_0, \theta_0)$ the residuals are $u_i$, so $\hat g(s_0,\theta_0) = \bar u := n^{-1}\sum_i b_iu_i$ and $\hat\Omega_{s_0}(\theta_0) = n^{-1}\sum_i b_ib_i'u_i^2 \to_p \Omega$ by the law of large numbers. By (A1), $E[bu] = 0$, and $\sqrt n\,\bar u \to_d N(0, \Omega)$ by the central limit theorem; Slutsky's lemma gives the $\chi^2_K$ limit. Since $\theta_0 \in \Theta_{s_0}$, $S_{s_0} \le \mathrm{AR}_{s_0}(\theta_0)$, so $\{s_0 \in \hat{\mathcal S},\ s_0 \notin \mathcal C_\alpha\} \subseteq \{\mathrm{AR}_{s_0}(\theta_0) > \chi^2_{K,1-\alpha}\}$, whatever the (random) candidate set.
- (b) The event is contained in $\{s_0 \in \hat{\mathcal S},\ s_0 \notin \mathcal C_\alpha\}$, so (a) applies; the rest is the definition of the report.
- (c) For $f = f_s(\cdot;\theta) \in \mathcal G_\alpha$, $\lVert\hat\Omega_s(\theta)\rVert \le \zeta_K^2\,n^{-1}\sum_i(y_i - f(X_i))^2 \le 2\zeta_K^2\,n^{-1}\sum_i\bigl(y_i^2 + F(X_i)^2\bigr) =: B_n$, and $B_n = O_p(1)$ by (A3) and $E[y^2] < \infty$. Then $\lVert\hat g(s,\theta)\rVert^2 \le \chi^2_{K,1-\alpha}\,B_n/n$, so $Q(f) \le \lVert\hat g\rVert^2 + R_n \to_p 0$ uniformly over $\mathcal G_\alpha$, with $R_n$ the uniform deviation of (C2). Lemma 1(c) with $\Pi_KT$ in place of $T$ (which is where (A2$_K$) enters) gives $\lVert f - f_0\rVert \to 0$ uniformly. $\blacksquare$

**What the two guards cost.**
- *The envelope.* On the event in (E), $\theta_0$ is feasible, so (a) and (b) hold for the enveloped statistic with the same bound; (c) holds for the enveloped set a fortiori, since it is smaller.
- *The winsorized weight.* Let $\tilde\Omega_{s_0}(\theta_0) := n^{-1}\sum_i b_ib_i'\min(u_i^2, c^2)$ for a cap $c$ and write $\Omega_c := E[bb'\min(u^2, c^2)] \preceq \Omega$. For a fixed cap, $\tilde\Omega \to_p \Omega_c$, so the capped statistic converges in distribution to $\xi'\Omega^{1/2}\Omega_c^{-1}\Omega^{1/2}\xi$ with $\xi \sim N(0, I_K)$, which stochastically dominates $\chi^2_K$: the capped set under-covers, with asymptotic size at most $P\bigl(\chi^2_K > \lambda_{\min}(\Omega_c\Omega^{-1})\,\chi^2_{K,1-\alpha}\bigr)$. The loss is governed by the share of $E[bb'u^2]$ beyond the cap, not of $E[u^2]$: a global cap bites hardest where the instruments make the error variance large. For Gaussian errors and a cap at five standard deviations the share is below $10^{-4}$ and the size is $\alpha$ to three decimals; for $t_3$ errors about a third of the variance lies beyond the 99.5% quantile, which inflates the statistic by a factor near $1.5$ and a nominal 5% test rejects the truth about 10–15% of the time. With the implementation's $c_n \to \infty$, $\tilde\Omega - \hat\Omega \to_p 0$ whenever $E[\lVert b\rVert^2u^2] < \infty$ (the omitted mass is $E[\lVert b\rVert^2u^2\mathbf 1\{\lvert u\rvert > c_n\}] \to 0$), so (a)–(b) hold exactly in the limit; at the sample sizes here the cap is five robust standard deviations and the finite-sample size is the one just stated. The cap is computed from the formula's own two-step fit, so this also presumes that fit converges at the true tree, which (A5) gives. The centred weight $\hat\Omega - \hat g\hat g'$ of Hansen, Heaton & Yaron (1996) does not address the problem the cap addresses: with $q := \hat g'\hat\Omega^{-1}\hat g$ it changes the statistic to $nq/(1 - q)$, a negligible change when $\mathrm{AR} \ll n$, whereas the inflation comes from a few large residuals inside $\hat\Omega$ itself.

**The report.** `identification_report` returns a verdict and its reasons:
- **rejected**: the selected formula fails its own S test, $S_{\hat s} > \chi^2_{K,1-\alpha}$: no candidate of this form fits the moment conditions;
- **weakly identified**: some AR interval of the selected formula's constants reaches the constant bound, or $\mathcal C_\alpha$ contains a formula more than $\tau$ away from $\hat f$ in the trimmed metric (the formulas are listed);
- **identified**: otherwise.

It also reports the first-stage $F$ statistic of (log) $X$ on the instruments, the Wald and AR intervals of each constant and their width ratio, and the farthest member of $\mathcal C_\alpha$. The AR intervals are projections of the $K$-dimensional AR set, so even under strong identification, where $\mathrm{AR}(\theta) \approx J + \text{Wald}(\theta)$, their half-width is about $\mathrm{se}\sqrt{\chi^2_{K,1-\alpha} - J}$: wider than the Wald interval by a factor near $\sqrt{(\chi^2_{K,1-\alpha} - J)/\chi^2_{1,1-\alpha}}$ (the width ratio the report prints), and the heteroskedasticity-robust weight gives them little power against differences carried by a few observations, a pole or the tail of $X$: that is why the distance is trimmed, and why the verdict uses only whether an interval reaches the bound.

**What it cannot do.** A search failure, where no candidate has the true form, is detected only if every candidate fails its S test ("rejected"). If a wrong formula fits the moments, which under a strong instrument means it is close to $f_0$ in the directions the instruments see, the report says "identified" and it is wrong about the tree, though usually not about the function. §7.1 measures all of this on the Phase 4 runs.

---

## 4. Theorem 2: a finite-sample selection bound

Theorem 1 says what happens as $n \to \infty$. Theorem 2 says when selection works at a given $n$, and why the two failures seen in Phases 2–4 happen:
- **(I)** a wrong formula that the instruments cannot tell apart from $f_0$ wins: weak separation;
- **(II)** a formula with extra constants or nodes wins by fitting moment noise: the contrived winners.

### Setting (F)

This is the simplest case with explicit constants.
- **(F1) Instruments.** GMM with fixed $K$ and population-orthonormal instruments: $E[bb'] = I_K$ and $\sup_z\lVert b(z)\rVert \le \zeta_K$, so $\zeta_K \ge \sqrt K$. The criterion is $Q_n(s,\theta) = \lVert\hat g(s,\theta)\rVert^2$ with identity weight. The code orthonormalizes on the sample instead; Proposition 2.4 covers that.
- **(F2) Errors.** $E[u \mid Z] = 0$ and $E[e^{\lambda u} \mid Z] \le e^{\lambda^2\bar\sigma^2/2}$ for all $\lambda$. The $J$ statistic is $J_n(s) = (n/\sigma^2)\min_\theta Q_n(s,\theta)$ with a fixed normalization $\sigma^2 > 0$, such as $\mathrm{Var}(u)$. Write $\rho := \bar\sigma^2/\sigma^2$.
- **(F3) Formula class.** For all $s$, $\theta, \theta'$ and $x$: $\lvert f_s(x;\theta) - f_0(x)\rvert \le M$, and $\lvert f_s(x;\theta) - f_s(x;\theta')\rvert \le \Lambda\lVert\theta - \theta'\rVert_\infty$.

(F3) needs a bounded class on the support of $X$. The Monte Carlo designs have lognormal regressors, so for them (F3) is an idealization: it holds after truncating the support.

**Notation.**
- **Population moments.** $g(s,\theta) := E[b(Z)(f_0 - f_s(\cdot;\theta))(X)]$, so $\lVert g(s,\theta)\rVert^2 = \lVert\Pi_K T(f_s(\cdot;\theta) - f_0)\rVert^2$. The separation of tree $s$ at this $K$ is $\delta_s := \min_\theta\lVert g(s,\theta)\rVert^2$. It is positive for wrong trees under (A2$_K$).
- **Penalty gap.** $\pi_s := \mathrm{pen}(s) - \overline{\mathrm{pen}}_0$, where $\overline{\mathrm{pen}}_0 := \max_{s' \in \mathcal S_0^{\min}}\mathrm{pen}(s')$ is the largest penalty of a minimal true tree. This is the worst case: the conditions below are then the most demanding, and the conclusion holds for whichever minimal true tree the candidate set contains.
- **Moment noise.** $Z := \sqrt n\,\bar u/\sigma$ with $\bar u := n^{-1}\sum_i b(Z_i)u_i$ is the moment noise at the truth. For every $s^* \in \mathcal S_0^{\min}$ and $\theta^* \in \Theta_{s^*}^0$, $y_i - f_{s^*}(X_i;\theta^*) = u_i$, so $J_n(s^*) \le \lVert Z\rVert^2$.
- **Empirical-process part.** $E_s(\theta) := \sqrt n\,(P_n - P)[\,b(Z)(f_0 - f_s(\cdot;\theta))(X)\,]/\sigma$.

Substituting $y_i = f_0(X_i) + u_i$ gives, for every $s$ and $\theta$,

$$\frac{\sqrt n\,\hat g(s,\theta)}{\sigma} = Z + \frac{\sqrt n\,g(s,\theta)}{\sigma} + E_s(\theta). \tag{4.1}$$

### The deterministic core

**Proposition 2.1.** Let $s \notin \mathcal S_0^{\min}$, and suppose $\lVert Z\rVert \le z$ and $\sup_{s,\theta}\lVert E_s(\theta)\rVert \le d$. Then $\mathrm{crit}_n(s) > \mathrm{crit}_n(s^*)$ for every $s^* \in \mathcal S_0^{\min}$ if either condition holds:

- **(I) Separation:** $\sqrt{n\delta_s}/\sigma > 2z + d + \sqrt{(-\pi_s)_+}$.
- **(II) Complexity:** $\pi_s > W_s^2 + 2z\,d_s^{\mathrm{loc}}$.

The quantities in (II) are defined with $r := 2z + d$:
- the localized constants $\Theta_s(r) := \{\theta \in \Theta_s : \sqrt n\lVert g(s,\theta)\rVert/\sigma \le r\}$;
- the directions $\mathcal D_s(r) := \{g(s,\theta)/\lVert g(s,\theta)\rVert : \theta \in \Theta_s(r),\ g(s,\theta) \neq 0\}$;
- $W_s := \sup_{v \in \mathcal D_s(r)}\langle -Z, v\rangle_+$, or $0$ if $\mathcal D_s(r)$ is empty;
- any bound $d_s^{\mathrm{loc}} \ge \sup_{\theta \in \Theta_s(r)}\lVert E_s(\theta)\rVert$.

Moreover $W_s \le \lVert P_{V_s} Z\rVert$, where $V_s := \mathrm{span}\,\mathcal D_s(r)$ and $P_{V_s}$ is the orthogonal projection onto it.

*Proof.*

**Reduction.** $\mathrm{crit}_n(s^*) \le \lVert Z\rVert^2 + \mathrm{pen}(s^*) \le \lVert Z\rVert^2 + \overline{\mathrm{pen}}_0$, so it suffices to show $J_n(s) > \lVert Z\rVert^2 - \pi_s$. By (4.1),

$$J_n(s) = \min_\theta\lVert Z + G(\theta) + E(\theta)\rVert^2, \qquad G(\theta) := \sqrt n\,g(s,\theta)/\sigma.$$

The minimum is attained, as $\theta \mapsto \lVert Z + G(\theta) + E(\theta)\rVert^2$ is continuous on the compact $\Theta_s$, so a strict inequality at every $\theta$ gives a strict inequality for $J_n(s)$.

**(I).** $\lVert G(\theta)\rVert \ge a := \sqrt{n\delta_s}/\sigma$ for every $\theta$, so $\lVert Z + G + E\rVert \ge a - z - d > z + \sqrt{(-\pi_s)_+} \ge 0$. Squaring,

$$J_n(s) > \bigl(z + \sqrt{(-\pi_s)_+}\bigr)^2 \ge z^2 + (-\pi_s)_+ \ge \lVert Z\rVert^2 - \pi_s.$$

**(II), outside the localized set.** Here $\pi_s > 0$. If $\theta \notin \Theta_s(r)$, then

$$\lVert Z + G + E\rVert \ge \lVert G\rVert - z - d > r - z - d = z \ge \lVert Z\rVert.$$

**(II), inside the localized set.** Let $\theta \in \Theta_s(r)$ with $G \neq 0$, and $v = G/\lVert G\rVert$. Minimizing over the length $\lVert G\rVert \ge 0$,

$$\lVert Z + G\rVert^2 = \lVert Z\rVert^2 + 2\lVert G\rVert\langle Z, v\rangle + \lVert G\rVert^2 \ \ge\ \lVert Z\rVert^2 - \langle -Z, v\rangle_+^2 \ \ge\ \lVert Z\rVert^2 - W_s^2,$$

which also holds when $G = 0$. Now let $a := ((\lVert Z\rVert^2 - W_s^2)_+)^{1/2} \le \lVert Z\rVert \le z$ and $\Delta := \lVert E(\theta)\rVert \le d_s^{\mathrm{loc}}$. Using $(a - \Delta)_+^2 \ge a^2 - 2a\Delta$,

$$\lVert Z + G + E\rVert^2 \ \ge\ (a - \Delta)_+^2 \ \ge\ a^2 - 2a\Delta \ \ge\ \lVert Z\rVert^2 - W_s^2 - 2z\,d_s^{\mathrm{loc}} \ >\ \lVert Z\rVert^2 - \pi_s.$$

**The projection bound.** For $v \in \mathcal D_s(r) \subseteq V_s$ with $\lVert v\rVert = 1$, $\langle -Z, v\rangle = \langle -P_{V_s}Z, v\rangle \le \lVert P_{V_s}Z\rVert$. $\blacksquare$

**Remark (tree-specific deviation levels).** The proof uses $d$ only through $\sup_\theta\lVert E_s(\theta)\rVert$ for the tree $s$ at hand, so $d$ and $r$ may depend on $s$: with any $d_s \ge \sup_\theta\lVert E_s(\theta)\rVert$ and $r_s := 2z + d_s$ in the definitions of $\Theta_s(\cdot)$, $\mathcal D_s(\cdot)$, $W_s$ and $d_s^{\mathrm{loc}}$, the statement holds verbatim. Theorem 2 is written with one level $t_L$ for all trees; Corollary 2.2 uses the tree-specific version.

### Concentration

**Lemma 3.** Assume (F1)–(F3) and let $t > 0$. Define

$$\varepsilon_n(t) := \sqrt{\frac{2\zeta_K^2(t + \log 2K)}{n}} + \frac{2(\zeta_K^2 + 1)(t + \log 2K)}{3n}.$$

(a) $P(\lVert\hat\Sigma - I_K\rVert > \varepsilon_n(t)) \le e^{-t}$, where $\hat\Sigma := n^{-1}\sum_i b(Z_i)b(Z_i)'$.

(b) On the event in (a), $P(\lVert Z\rVert^2 > z_t^2 \mid Z_{1:n}) \le e^{-t}$, with $z_t^2 := \rho(1 + \varepsilon_n(t))(K + 2\sqrt{Kt} + 2t)$.

(c) Let $h(x;\theta)$, $\theta \in \Theta' \subseteq [-C,C]^p$, satisfy $\lvert h\rvert \le M'$ and be $\Lambda$-Lipschitz in $\theta$ in the sup norm. Then

$$P\Bigl(\sup_{\theta \in \Theta'}\sqrt n\,\lVert(P_n - P)[b\,h(\cdot;\theta)]\rVert > M'\bigl[\sqrt K + 2\zeta_K + \zeta_K\sqrt{8(t + p\log(1 + 2C\Lambda\sqrt n/M'))}\bigr]\Bigr) \le e^{-t}.$$

(d) Let $V \subseteq \mathbb R^K$ be a fixed subspace of dimension $k$ and $P_V$ the orthogonal projection onto it. On the event in (a),

$$P\Bigl(\lVert P_V Z\rVert^2 > \rho(1 + \varepsilon_n(t))\bigl(k + 2\sqrt{kt} + 2t\bigr) \Bigm| Z_{1:n}\Bigr) \le e^{-t}.$$

*Proof.*
- **(a)** Matrix Bernstein ([Tropp 2012](https://doi.org/10.1007/s10208-011-9099-z), Theorem 1.4) for the sum of $(b_ib_i' - I)/n$. Each summand has norm at most $(\zeta_K^2 + 1)/n$, and the variance proxy is at most $\zeta_K^2/n$, because $E(bb' - I)^2 = E[\lVert b\rVert^2bb'] - I \preceq \zeta_K^2 I$. Solving $2K\exp\{-x^2/(2v + 2Rx/3)\} = e^{-t}$ for $x$ gives $x \le \sqrt{2v(t + \log 2K)} + 2R(t + \log 2K)/3$.
- **(b)** Conditionally on $Z_{1:n}$, the $u_i$ are independent with $E[e^{\alpha'u} \mid Z_{1:n}] \le e^{\lVert\alpha\rVert^2\bar\sigma^2/2}$. Write $\sqrt n\,\bar u = Mu$, where $M := n^{-1/2}[b(Z_1), \dots, b(Z_n)]$ and $MM' = \hat\Sigma$. Theorem 1 of [Hsu, Kakade & Zhang (2012)](https://doi.org/10.1214/ECP.v17-2079) bounds $\lVert Mu\rVert^2$ by $\bar\sigma^2(\mathrm{tr}\,\hat\Sigma + 2\sqrt{\mathrm{tr}(\hat\Sigma^2)\,t} + 2\lVert\hat\Sigma\rVert t)$ with probability at least $1 - e^{-t}$. On (a), $\mathrm{tr}\,\hat\Sigma \le K(1+\varepsilon)$, $\mathrm{tr}\,\hat\Sigma^2 \le K(1+\varepsilon)^2$ and $\lVert\hat\Sigma\rVert \le 1 + \varepsilon$. Divide by $\sigma^2$.
- **(c)**
  1. *Cover.* A cover of the cube at sup-radius $\eta/2$ gives a cover of $\Theta'$ at radius $\eta$ with centres in $\Theta'$ and at most $(1 + 2C/\eta)^p$ points. Take $\eta = M'/(\Lambda\sqrt n)$.
  2. *One centre.* At a fixed centre, $Y_i := b(Z_i)h(X_i) - E[bh]$ are independent with $\lVert Y_i\rVert \le 2\zeta_K M'$. The norm $F := \lVert\sum_i Y_i\rVert$ changes by at most $4\zeta_K M'$ when one observation changes, and $EF \le (nE\lVert bh\rVert^2)^{1/2} \le \sqrt n\,M'\sqrt K$, because $E\lVert b\rVert^2 = \mathrm{tr}\,I_K = K$. McDiarmid's inequality gives $P(F > \sqrt n M'\sqrt K + \zeta_K M'\sqrt{8nu}) \le e^{-u}$.
  3. *All centres.* Take a union bound over the centres, with $u = t + p\log(1 + 2C\Lambda\sqrt n/M')$.
  4. *Between centres.* Within a ball, $\lVert(P_n - P)[b(h(\theta) - h(\theta_k))]\rVert \le 2\zeta_K\Lambda\eta = 2\zeta_K M'/\sqrt n$.
- **(d)** Conditionally on $Z_{1:n}$, $P_V Z = \sigma^{-1}(P_V M)u$ is a linear image of a sub-Gaussian vector. Hsu, Kakade & Zhang's bound applies with $\Sigma := M'P_V M$, for which $\mathrm{tr}\,\Sigma = \mathrm{tr}(P_V\hat\Sigma) \le k\lVert\hat\Sigma\rVert$, $\mathrm{tr}\,\Sigma^2 = \mathrm{tr}\bigl((P_V\hat\Sigma P_V)^2\bigr) \le k\lVert\hat\Sigma\rVert^2$ (a matrix of rank at most $k$ and norm at most $\lVert\hat\Sigma\rVert$) and $\lVert\Sigma\rVert \le \lVert\hat\Sigma\rVert$. On (a), $\lVert\hat\Sigma\rVert \le 1 + \varepsilon_n(t)$. $\blacksquare$

### The theorem

**Theorem 2.** Assume (A0), (A1), (A2$_K$) and (F1)–(F3). Fix $t > 0$, let $t_L := t + \log\lvert\mathcal S_L\rvert$, take $\varepsilon_n(t)$ and $z_t$ from Lemma 3, and define

$$d_t := \frac{M}{\sigma}\Bigl[\sqrt K + 2\zeta_K + \zeta_K\sqrt{8\bigl(t_L + p_{\max}\log(1 + 2C\Lambda\sqrt n/M)\bigr)}\Bigr], \qquad r_t := 2z_t + d_t,$$

where $p_{\max} := \max_{s \in \mathcal S_L}p_s$. For each tree $s$, with the localized set $\Theta_s(r_t)$ and the directions $\mathcal D_s(r_t)$ of Proposition 2.1, let

$$M_s := \sup\{\lvert f_s(x;\theta) - f_0(x)\rvert : x \in \mathcal X,\ \theta \in \Theta_s(r_t)\}, \qquad k_s := \dim\,\mathrm{span}\,\mathcal D_s(r_t) \le K,$$

$$d^{\mathrm{loc}}_{s,t} := \frac{M_s}{\sigma}\Bigl[\sqrt K + 2\zeta_K + \zeta_K\sqrt{8\bigl(t_L + p_s\log(1 + 2C\Lambda\sqrt n/M_s)\bigr)}\Bigr],$$

with $d^{\mathrm{loc}}_{s,t} := 0$ when $M_s = 0$ and $k_s := 0$ when $\mathcal D_s(r_t)$ is empty. There is an event of probability at least $1 - 5e^{-t}$ on which, for **any** candidate set $\hat{\mathcal S} \subseteq \mathcal S_L$ (possibly data-dependent) that contains some $s^* \in \mathcal S_0^{\min}$, the selected tree is minimal and true ($\hat s \in \mathcal S_0^{\min}$), provided every $s \in \mathcal S_L \setminus \mathcal S_0^{\min}$ satisfies (I) or (II):

- **(I) Separation:** $n\delta_s/\sigma^2 > \bigl(2z_t + d_t + \sqrt{(-\pi_s)_+}\bigr)^2$.
- **(II) Complexity:** $\pi_s > \rho\,(1 + \varepsilon_n(t))\bigl(k_s + 2\sqrt{k_s t_L} + 2t_L\bigr) + 2z_t\,d^{\mathrm{loc}}_{s,t}$.

Consequently

$$P(\hat s \notin \mathcal S_0^{\min}) \ \le\ \underbrace{5e^{-t}}_{\text{statistical failure}} + \underbrace{P(\hat{\mathcal S} \cap \mathcal S_0^{\min} = \emptyset)}_{\text{search failure}}.$$

*Proof.* Intersect five events, all controlled by Lemma 3:
- (a), with probability at least $1 - e^{-t}$;
- (b), at least $1 - e^{-t}$;
- (c) with $h = f_0 - f_s$ on each $\Theta_s$, at level $t_L$, and a union bound over $\mathcal S_L$: $\sup_{s,\theta}\lVert E_s(\theta)\rVert \le d_t$, at least $1 - e^{-t}$;
- (c) on each deterministic set $\Theta_s(r_t)$ with $M' = M_s$, at level $t_L$, with a union bound over $\mathcal S_L$: $\sup_{\theta \in \Theta_s(r_t)}\lVert E_s(\theta)\rVert \le d^{\mathrm{loc}}_{s,t}$ for every $s$, at least $1 - e^{-t}$;
- (d) on each deterministic subspace $V_s = \mathrm{span}\,\mathcal D_s(r_t)$, at level $t_L$, with a union bound over $\mathcal S_L$: $\lVert P_{V_s}Z\rVert^2 \le \rho(1+\varepsilon_n(t))(k_s + 2\sqrt{k_s t_L} + 2t_L)$ for every $s$, at least $1 - e^{-t}$.

On the intersection, Proposition 2.1 applies to every tree with $z = z_t$, $d = d_t$ and $d^{\mathrm{loc}}_s = d^{\mathrm{loc}}_{s,t}$, and with $W_s^2 \le \lVert P_{V_s}Z\rVert^2$. So every $s \notin \mathcal S_0^{\min}$ has $\mathrm{crit}_n(s) > \mathrm{crit}_n(s^*)$. Because the bounds are uniform over $\mathcal S_L$, this holds whichever candidate set the search produced. The three union bounds may also run at tree-specific levels $t_s$ with $\sum_{s \in \mathcal S_L}e^{-t_s} \le e^{-t}$; then $d_t$, $r_t$ and $d^{\mathrm{loc}}_{s,t}$ become $d_{s,t}$, $r_{s,t} := 2z_t + d_{s,t}$ and $d^{\mathrm{loc}}_{s,t_s}$, which the remark after Proposition 2.1 allows. $\blacksquare$

**A cruder (II) that needs no union bound.** Since $\lVert P_{V_s}Z\rVert \le \lVert Z\rVert \le z_t$, condition (II) can be replaced by $\pi_s > z_t^2 + 2z_t d^{\mathrm{loc}}_{s,t}$, at the price of comparing the penalty gap with the whole moment noise $z_t^2 \approx \rho K$ instead of its projection on $k_s$ directions.

### Reading Theorem 2

- **When each condition applies.**
  - A **wrong tree** loses if it is separated from $f_0$ by more than the noise plus the penalty it saves (I).
  - A **longer or more heavily parameterized tree** loses if the penalty it pays exceeds the moment noise it can fit (II).
  - A tree that meets neither condition can win. That happens to wrong trees whose separation $\delta_s$ is small *and* that are no bigger than the minimal true trees: simpler wrong formulas under weak instruments (D5), and same-size near-duplicates when $w = 0$.
- **Orders of magnitude** (with $K$ and $L$ fixed). $z_t = O(1)$ and $d_t = O(\sqrt{\log n})$, the latter from the $\log(1 + 2C\Lambda\sqrt n/M)$ term of the covering bound. Using $(a + b)^2 \le 2a^2 + 2b^2$, (I) holds for a wrong tree as soon as

  $$\frac{n\delta_s}{\sigma^2} > 2(p_0 - p_s)_+\kappa_n + 2w(\bar\ell_0 - \ell_s)_+\log m + 2(2z_t + d_t)^2,$$

  where $\bar\ell_0 := \max_{s^* \in \mathcal S_0^{\min}}\ell_{s^*}$ is the size that enters $\overline{\mathrm{pen}}_0$ (every minimal true tree has $p_0$ constants), and $d_t^2 = O(\log n)$ is of the **same** order as $\kappa_n = \ln n$. So the finite-sample condition is the population comparison $n\delta_s/\sigma^2$ against the penalty saved, plus deviation terms of the same order with explicit constants; it does not reduce to the population comparison alone.
- **Link to the Phase 4 margin.** The population comparison $\lambda_s - (p_0 - p_s)\kappa_n$ with $\lambda_s := n\delta_s/\sigma^2$ is what Phase 4 computed (README §12.3): it is condition (I) with $z_t = d_t = 0$. Among runs whose candidates contained the true form, recovery was 74% in cells with a positive margin and 23% in the others (Spearman 0.56 across 32 cells). The deviation terms explain why a small positive margin is not enough.
- **Over-parameterized true trees.** For $s \in \mathcal S_0$ with $p_s > p_0$, $\delta_s = 0$, so only (II) can exclude it. As $n$ grows, $\Theta_s(r_t) = \{\theta : \lVert g(s,\theta)\rVert \le \sigma r_t/\sqrt n\}$ shrinks to the zero set $\Theta_s^0$. If the moment map is regular there, in the sense that $\lVert g(s,\theta)\rVert \ge c\,\mathrm{dist}(\theta, \Theta_s^0)$ near $\Theta_s^0$, then $M_s \le \Lambda\,\sigma r_t/(c\sqrt n) = O(\sqrt{\log n/n})$ and $d^{\mathrm{loc}}_{s,t} = O(\log n/\sqrt n) \to 0$. The dimension $k_s$ needs care. For a tree **linear in its constants**, $f_s = \sum_k\theta_k\psi_k$, every direction $g(s,\theta)/\lVert g(s,\theta)\rVert$ lies in the span of the $p_s$ vectors $E[b\,\psi_k(X)]$, so $k_s \le p_s$ exactly. For a tree **nonlinear in $\theta$** the same bound is false at any finite $n$: with $g(\theta) = (\theta, \theta^2)$ and $\Theta_s^0 = \{0\}$, the normalized directions over $\Theta_s(r) \setminus \{0\}$ span $\mathbb R^2$ for every $r > 0$ although $p_s = 1$; the directions approach the Jacobian span $V_J := \mathrm{span}\{\partial_\theta g(s,\theta) : \theta \in \Theta_s^0\}$, of dimension at most $p_s$, only as $r_t/\sqrt n \to 0$. What holds is a first-order version: for unit $v \in \mathcal D_s(r_t)$, $\langle -Z, v\rangle \le \lVert P_{V_J}Z\rVert + \lVert Z\rVert\,\mathrm{dist}(v, V_J)$, so $W_s \le \lVert P_{V_J}Z\rVert + z_t\,\eta_s$ with $\eta_s := \sup_{v \in \mathcal D_s(r_t)}\mathrm{dist}(v, V_J)$, and $W_s^2 \le \lVert P_{V_J}Z\rVert^2 + 3z_t^2\eta_s$ when $\eta_s \le 1$. If the moment map is $C^2$ and regular near $\Theta_s^0$, then $\eta_s = O(r_t/\sqrt n)$, and Lemma 3(d) applied to the fixed subspace $V_J$ gives (II) with $k_s$ replaced by $\dim V_J \le p_s$ plus a remainder $O(z_t^2 r_t/\sqrt n) \to 0$. Then (II) reads $(p_s - p_0)\kappa_n > \rho(1+\varepsilon)(p_s + 2\sqrt{p_s t_L} + 2t_L) + o(1)$: Theorem 1(ii) again, with explicit sample sizes. The term $2\rho t_L \approx 2\rho(t + L\log 3m)$ is the price of the union bound over all trees; Corollary 2.2 is about it.

**Corollary 2.2 (why a structure term).**

*Derivation.*
1. **Weighted union bound.** In the union bounds of Lemma 3(c)–(d), use weights proportional to $(3m)^{-\ell_s}/L$ instead of uniform ones. They sum to at most one, because there are at most $(3m)^{\ell}$ trees of size $\ell$. Then $t_L$ becomes the tree-specific $t_s := t + \log L + \ell_s\log(3m)$ in every bound that concerns tree $s$: in $d_{s,t}$ (the deviation level $d_t$ with $t_s$ in place of $t_L$, which the remark after Proposition 2.1 and the last sentence of Theorem 2's proof allow), in $d^{\mathrm{loc}}_{s,t_s}$ and in (II).
2. **Expand (II).** Using $2\sqrt{k_s t_s} \le k_s + t_s$, (II) holds if

   $$(p_s - p_0)\kappa_n + w(\ell_s - \bar\ell_0)\log m \ >\ \rho(1+\varepsilon_n(t))\bigl(2k_s + 3t + 3\log L\bigr) + 3\rho(1+\varepsilon_n(t))\,\ell_s\log(3m) + 2z_t\,d^{\mathrm{loc}}_{s,t_s}.$$

3. **Cancel the size terms.** If

   $$w \ \ge\ 3\rho\,(1 + \varepsilon_n(t))\,\frac{\log(3m)}{\log m},$$

   the terms in $\ell_s$ cancel, and (II) holds whenever $(p_s - p_0)\kappa_n > w\bar\ell_0\log m + \rho(1+\varepsilon_n(t))(2k_s + 3t + 3\log L) + 2z_t d^{\mathrm{loc}}_{s,t_s}$: a condition that no longer depends on the size of $s$, apart from $k_s$ and the local deviation (which vanishes for true trees). The guarantee is then uniform in the maximal size $L$.

*Numbers* (one regressor, $m = 10$, $n = 2000$, $K = 13$, $\rho = 1$, $t = 3$, so $\varepsilon_n(t) \approx 0.3$ and $\kappa_n = \ln 2000 \approx 7.6$).
- **What the corollary asks.** $\log(3m)/\log m = 1.48$, so $w \ge 4.4\,\rho(1 + \varepsilon_n(t)) \approx 5.7$.
- **What it then certifies.** Uniformity in $L$ is bought with the leftover term $w\bar\ell_0\log m$ on the right of step 3. For the log law ($a + b\log x$, $\bar\ell_0 = 6$) it is $5.7 \times 6 \times 2.3 \approx 79$, so a tree with one extra constant is excluded only if $\kappa_n = 7.6 > 79 + \rho(1+\varepsilon)(2k_s + 3t + 3\log L) + \dots$: nothing is certified at $n = 2000$, for trees of any size, and the condition needs $\kappa_n$ in the hundreds, i.e. astronomically large $n$. **Without the term** ($w = 0$) the picture is the same with the size of the wrong tree in place of $\bar\ell_0$: a 15-node tree has $3\rho(1+\varepsilon)\ell_s\log(3m) \approx 199$ on the right. So the corollary says in which direction the penalty must go to make the bound independent of $L$, not that the bound is informative at this $n$; the union bound over all $(3m)^\ell$ trees of each size, together with the explicit constants of Lemma 3, is what makes it vacuous here.
- **The other side of $w$.** The same $w$ enters channel (I): for a wrong tree shorter than the true one, $(-\pi_s)_+ \approx w(\bar\ell_0 - \ell_s)\log m$ is added to the separation required, about $39$ for a tree three nodes shorter at $w = 5.7$, against $3.5$ at $w = 0.5$. A large $w$ manufactures the "simpler wrong formula wins" failure (D5; the kink law), so the theory's $w$ is not a recommendation for practice.
- **In the data** (README §12.3), $w = 0.5$ and $w = 1$ did equally well: 60% vs. 51% recovery, and 98–100% from $n = 5000$. What they fixed were same-size near-duplicates of the law ($\pi_s = 0$ when $w = 0$, $\delta_s \approx 0$), which is the case that falls under **neither** channel in the reading above, not the union-bound mechanism of this corollary. The data support the direction of the structure term, and a weight ten times smaller than the one the bound asks for.

**Corollary 2.3 (candidates generated on a separate sample).** Suppose $\hat{\mathcal S}$ is generated on data independent of the selection sample. Conditionally on $\hat{\mathcal S}$, Theorem 2 holds with every union bound running over $\hat{\mathcal S}$ instead of $\mathcal S_L$: $\log\lvert\mathcal S_L\rvert$ becomes $\log\lvert\hat{\mathcal S}\rvert$ in $t_L$.

*Proof.* Lemma 3 holds conditionally on $\hat{\mathcal S}$, because the selection sample is independent of it, and the union bounds in the proof of Theorem 2 need only cover the trees that can be selected. $\blacksquare$

- **Size of the gain.** If the Phase 4 candidates had come from an independent sample, the union bound would run over the median of 28 candidates, $\log\lvert\hat{\mathcal S}\rvert \approx 3.3$, instead of $\log\lvert\mathcal S_{15}\rvert \approx 51$, and the structure term of Corollary 2.2 would have nothing left to absorb in channel (II). The corollary does not apply to Phase 4 itself, whose candidates were generated on the selection sample; the empirical effect of $w$ there is the near-duplicate case discussed under Corollary 2.2.
- **Trade-off.** Generating on one half of the sample and selecting on the other halves the selection sample, so $n\delta_s$ in (I) halves too. §7.1 tests this trade-off.

### Perturbed criteria

**Proposition 2.4 (perturbed weights).** Let $\hat W$ be a symmetric matrix, possibly data-dependent, with

$$\lambda_-\,\sigma^{-2} I_K \ \preceq\ \hat W\ \preceq\ \lambda_+\,\sigma^{-2} I_K, \qquad 0 < \lambda_- \le \lambda_+,$$

and let the selection use $\tilde J_n(s) := n\min_\theta\hat g(s,\theta)'\hat W\hat g(s,\theta)$ in place of $J_n(s)$. Under the hypotheses of Proposition 2.1 ($\lVert Z\rVert \le z$, $\sup\lVert E_s\rVert \le d$), with the localization radius

$$r' := z\bigl(1 + \sqrt{\lambda_+/\lambda_-}\bigr) + d$$

in place of $r$ in the definitions of $\Theta_s(\cdot)$, $\mathcal D_s(\cdot)$, $W_s$ and $d^{\mathrm{loc}}_s$, the conclusion of Proposition 2.1 holds for the perturbed criterion if either

- **(I′)** $\sqrt{n\delta_s}/\sigma > z + d + \sqrt{(\lambda_+/\lambda_-)\,z^2 + (-\pi_s)_+/\lambda_-}$, or
- **(II′)** $\pi_s > (\lambda_+ - \lambda_-)\,z^2 + \lambda_-\bigl(W_s^2 + 2z\,d^{\mathrm{loc}}_s\bigr)$.

*Proof.* With $\theta^*$ feasible for $s^*$, $\tilde J_n(s^*) \le n\hat g(s^*,\theta^*)'\hat W\hat g(s^*,\theta^*) \le \lambda_+\lVert Z\rVert^2$, and $\tilde J_n(s) \ge \lambda_- J_n(s)$. So it suffices that

$$J_n(s) \ >\ \frac{\lambda_+}{\lambda_-}\lVert Z\rVert^2 - \frac{\pi_s}{\lambda_-}. \tag{4.2}$$

- Under (I′): as in Proposition 2.1, $J_n(s) \ge (\sqrt{n\delta_s}/\sigma - z - d)^2 > (\lambda_+/\lambda_-)z^2 + (-\pi_s)_+/\lambda_-$, which implies (4.2).
- Under (II′), which forces $\pi_s > 0$: outside $\Theta_s(r')$, $\lVert Z + G + E\rVert > r' - z - d = z\sqrt{\lambda_+/\lambda_-} \ge \lVert Z\rVert\sqrt{\lambda_+/\lambda_-}$, so the squared norm exceeds $(\lambda_+/\lambda_-)\lVert Z\rVert^2$, which implies (4.2). Inside $\Theta_s(r')$, the argument of Proposition 2.1 gives $\lVert Z + G + E\rVert^2 \ge \lVert Z\rVert^2 - W_s^2 - 2z\,d^{\mathrm{loc}}_s$, and (4.2) follows if $\pi_s/\lambda_- > (\lambda_+/\lambda_- - 1)\lVert Z\rVert^2 + W_s^2 + 2z\,d^{\mathrm{loc}}_s$, which (II′) implies because $\lVert Z\rVert^2 \le z^2$. $\blacksquare$

**Corollary 2.5 (the code's criterion).** The code uses sample-orthonormalized instruments, i.e. $\hat W = \hat\Sigma^{-1}/\sigma^2$. On the event of Lemma 3(a) with $\varepsilon := \varepsilon_n(t) < 1$, $\hat W$ satisfies the sandwich with $\lambda_- = (1+\varepsilon)^{-1}$ and $\lambda_+ = (1-\varepsilon)^{-1}$, so Theorem 2 holds for this criterion, on the same event of probability at least $1 - 5e^{-t}$, with (I′)–(II′) in place of (I)–(II). If the normalization is an estimated scale $\hat\sigma^2$ common to all candidates, assume $P(\lvert\hat\sigma^2/\sigma^2 - 1\rvert > \eta_n(t)) \le e^{-t}$ for some $\eta_n(t) \to 0$ (for instance the residual variance of a fixed pilot formula, by Bernstein's inequality under (F2)); on that sixth event $\lambda_\mp$ are multiplied by $(1 \pm \eta)^{-1}$, and the probability becomes $1 - 6e^{-t}$. A scale computed from each candidate's own residuals is a candidate-dependent weight, which belongs with the estimated efficient weight below *(beyond the paper)*. The perturbation is $\lambda_+ - \lambda_- \approx 2(\varepsilon + \eta)$ in (II′) and a factor $\lambda_+/\lambda_- \approx 1 + 2(\varepsilon + \eta)$ on $z^2$ in (I′); $\varepsilon_n(t)$ is of order $\sqrt{\zeta_K^2\log K/n}$, which is $\sqrt{K\log K/n}$ for a bounded-leverage basis ($\zeta_K^2 \asymp K$).

**Remark (general weights; the estimation error of an efficient weight is beyond the paper).** For a fixed positive definite weight $W$, such as the efficient $\Omega^{-1}$ under heteroskedasticity, rotate the instruments: $b_W := W^{1/2}b$ and $\Sigma_W := E[b_Wb_W']$, which is no longer the identity. Lemma 3 goes through with $I_K$ replaced by $\Sigma_W$ in (a) (matrix Bernstein for $\hat\Sigma_W - \Sigma_W$), $K$ replaced by $\mathrm{tr}\,\Sigma_W$ and $\lVert\hat\Sigma\rVert$ by $\lVert\hat\Sigma_W\rVert$ in (b) and (d), and $\sqrt K$, $\zeta_K$ replaced by $\sqrt{\mathrm{tr}\,\Sigma_W}$, $\zeta_K\lVert W^{1/2}\rVert$ in (c). The structure of Theorem 2 is unchanged; only the constants change. An estimated weight $\hat W$ then enters through Proposition 2.4 with $\lambda_\pm$ from the eigenvalues of $W^{-1/2}\hat WW^{-1/2}$.

**Remark (kernel criterion; the exact version is beyond the paper).** The code's criterion (c) is the Nyström approximation $Q_n = \lVert\Phi'r\rVert^2/n^2$ with $\Phi$ the $n \times m$ feature matrix of $m$ landmarks. With landmarks fixed in advance, or drawn from a sample independent of the one used for selection and conditioned upon, $\varphi(z) = K_{LL}^{-1/2}k(L, z)$ is a fixed bounded function and $Q_n = \lVert n^{-1}\sum_i\varphi(Z_i)r_i\rVert^2$ is a GMM criterion with $m$ instruments; Theorem 2 applies through the previous remark. The exact kernel criterion is a degenerate V-statistic at the truth, and a finite-sample analysis of it over $\mathcal F_L$ needs concentration for degenerate U-processes; that is left open.

**Limitations of Theorem 2.**
- The constants are explicit but not optimized (the factors 2 in $(a+b)^2 \le 2a^2 + 2b^2$, the crude cover of the cube).
- With heavy-tailed $u$, the tails become polynomial rather than exponential.
- For *wrong* trees with small $\delta_s$, the localized set $\Theta_s(r_t)$ can contain parameters whose functions are far from $f_0$ but have small moments. These are the ill-posed directions, so $M_s$ stays large and (II) is loose. These are the hard cases, and no general improvement should be expected.

---

## 5. Discrete instruments

Let $Z$ take $J$ values $z_1, \dots, z_J$ with $P(Z = z_j) > 0$, and write $m(h) := (E[h(X) \mid Z = z_j])_{j=1}^J \in \mathbb R^J$. Every function of $Z$ is a step function, so at most $J$ instruments are effective. With the saturated basis, $\Pi_K T h = 0$ if and only if $m(h) = 0$.

**Proposition 4.**

(a) **Linear families.** Let $s$ be a tree with $f_s(x;\theta) = \sum_{k=1}^{p}\theta_k\psi_k(x)$, and $f_0 \notin \mathcal F_s$. Suppose $p \ge J$, the $J \times p$ matrix $\Psi = [E(\psi_k(X) \mid Z = z_j)]$ has rank $J$, and $\Psi\theta = m(f_0)$ has a solution in $\Theta_s$. Then (A2$_K$) fails: $f_s(\cdot;\theta) \neq f_0$, yet $m(f_s(\cdot;\theta) - f_0) = 0$.

(b) **General families.** Let $s$ be wrong and $\bar\theta$ interior to $\Theta_s$. Suppose $\theta \mapsto m(f_s(\cdot;\theta) - f_0)$ is $C^1$ near $\bar\theta$, with Jacobian of rank $J$ there (so $p_s \ge J$). Then there is $r > 0$ such that $\lVert m(f_s(\cdot;\bar\theta) - f_0)\rVert < r$ implies $m(f_s(\cdot;\theta) - f_0) = 0$ for some $\theta \in \Theta_s$. In words, the criterion is exactly zero at a wrong formula.

*Proof.*
- **(a)** $m(f_s(\cdot;\theta) - f_0) = \Psi\theta - m(f_0) = 0$.
- **(b)** This is the surjective-derivative (Lyusternik–Graves) theorem ([Graves 1950](https://doi.org/10.1215/S0012-7094-50-01713-3)). A $C^1$ map whose derivative at $\bar\theta$ is onto maps $B(\bar\theta, \rho)$ onto a set containing $B(F(\bar\theta), c\rho)$, for some $\rho, c > 0$ with $B(\bar\theta, \rho) \subseteq \Theta_s$. Take $r = c\rho$. $\blacksquare$

**Conjecture 4 (c): fewer constants than support points** *(beyond the paper; stated there as open)*. Let $p_s < J$. Suppose the design is indexed by $\xi$ in an open set $\Xi \subseteq \mathbb R^q$, such that $F(\theta, \xi) := m_\xi(f_s(\cdot;\theta) - f_0)$ is $C^1$ on $\mathrm{int}\,\Theta_s \times \Xi$ with $0$ as a regular value, and likewise on each face of $\Theta_s$. Then for Lebesgue-almost every $\xi$, $F(\theta, \xi) \neq 0$ for all $\theta \in \Theta_s$: the wrong tree is identified.

- *Proof under the hypothesis.* By the parametric transversality theorem (Guillemin & Pollack 1974, §2.3), for almost every $\xi$ the map $F(\cdot, \xi)$ is transverse to $\{0\}$ on $\mathrm{int}\,\Theta_s$, so its zero set is a submanifold of dimension $p_s - J < 0$: empty. The same holds on each face, which has lower dimension, and there are finitely many faces and finitely many wrong trees.
- *What is open.* The hypothesis is the whole question. The derivative of $F$ at a zero is a $J \times (p_s + q)$ matrix, so $0$ can be a regular value only if $q \ge J - p_s$: the design family must have at least $J - p_s$ parameters that move the conditional moments $m_\xi$ in independent directions at every zero. Families built from the law's own constants have $q = p_0$, which is too few when $p_s + p_0 < J$; a family that perturbs each conditional distribution $P_{X \mid Z = z_j}$ separately has $q = J$ and is the natural candidate, but the regular-value condition then has to be checked at the zeros, which is a statement about the tree. No general argument is known to the author.

**What this means.**
- **Only the penalty can exclude such trees.** With a $J$-point instrument, the moments cannot exclude wrong trees with $J$ or more constants: their $\delta_s = 0$. Only the penalty can, through channel (II) of Theorem 2. A practical rule is to cap formulas at $J - 1$ constants when the instrument is discrete. The code's SVD orthonormalization already reduces $K$ to $J$, so the degrees of freedom of the MMSC are right.
- **Checked in the data** (`experiments/phase5_discrete.py`, output in [experiments/phase5/discrete.md](experiments/phase5/discrete.md)). In D4 ($J = 4$) the criterion has $K = 4$. On 20,000 noise-free draws, the wrong four-term formula $c_0 + c_1\sqrt x + c_2x + c_3x^2$ fitted to the moments sets the criterion to $10^{-33}$–$10^{-32}$ for the power, kink and saturation laws while missing $f_0$ by 0.12, 0.15 and 0.42 standard deviations: this is (a). For the log law the solution of the four moment equations lies outside the constant bound $\lvert c\rvert \le 10$, so the bound, not the moments, keeps the criterion positive ($2 \times 10^{-3}$ at the fit). Under D1's continuous instrument ($K = 27$ at this $n$) the same formula is separated from each law.

---

## 6. Misspecification and growing formula size

**Theorem 3 (a): fixed $L$, misspecified law.** Drop (A0) and (A2). Assume (A3), (C2), $Q$ continuous on $\mathcal F_L$, and $\kappa_n/n \to 0$. Let $Q^* := \min_{f \in \mathcal F_L}Q(f)$ and $\mathcal F^* := \arg\min_{\mathcal F_L} Q$, which is nonempty and compact. Suppose $\hat{\mathcal S}$ contains, with probability tending to one, a tree of some $f^* \in \mathcal F^*$. Then

$$Q(\hat f) \to_p Q^*, \qquad \inf_{f \in \mathcal F^*}\lVert\hat f - f\rVert \to_p 0.$$

*Proof.*
1. Exactly as in Theorem 1(i), $\hat Q_{\hat s} \le Q_n(f^*) + \hat\sigma^2\max_s\mathrm{pen}_n(s)/n$. Hence $Q(\hat f) \le Q^* + 2R_n + o_p(1)$, and $Q(\hat f) \ge Q^*$ by definition.
2. By compactness and continuity, $\inf\{Q(f) : f \in \mathcal F_L,\ \inf_{g \in \mathcal F^*}\lVert f - g\rVert \ge \varepsilon\} > Q^*$ for every $\varepsilon > 0$. $\blacksquare$

**Remarks.**
- **The pseudo-true set depends on the instruments.** Under misspecification, $\mathcal F^*$ depends on the instrument basis, on $K$ and on the weight ([Hall & Inoue 2003](https://doi.org/10.1016/S0304-4076(03)00089-7)). No formula is best independently of the instruments, which is why README §6.5 asks for the selection to be reported across bases.
- **The penalty cannot break ties.** Among trees with the same $Q^*$ but different pseudo-true functions, the $J$ statistics differ by $O_p(\sqrt n)$, so $\kappa_n$ does not decide between them. This is the non-nested comparison problem ([Vuong 1989](https://doi.org/10.2307/1912557)).

### Theorem 3 (b): consistency as the formula size grows

The class of formulas now grows with $n$: $L_n \to \infty$ and $K_n \to \infty$. The estimator minimizes over a compact set of functions, a **Lipschitz ball** $\mathcal H$, intersected with the formulas; in practice the Lipschitz constraint is checked on the support.

**Assumptions.**
- **(S1) Compact class.** $\mathcal H \subset L^2(P_X)$ is compact and $f_0 \in \mathcal H$. The estimator minimizes over $\mathcal H_n := \mathcal F_{L_n} \cap \mathcal H$.
- **(S2) Identification on $\mathcal H$.** For $f \in \mathcal H$, $T(f - f_0) = 0$ implies $f = f_0$.
- **(S3) Approximation.** $\inf_{f \in \mathcal H_n}\lVert f - f_0\rVert \to 0$.
- **(S4) Instruments.** For each $n$, $b^{(n)}(Z) \in \mathbb R^{K_n}$ with $E[b^{(n)}b^{(n)\prime}] = I_{K_n}$ and $\sup_z\lVert b^{(n)}(z)\rVert \le \zeta_n$; the spans are nested with a dense union in $L^2(P_Z)$, so the projections $\Pi_{K_n}$ converge strongly to the identity. The criterion is $Q_n(f) = \lVert n^{-1}\sum_i b^{(n)}(Z_i)(y_i - f(X_i))\rVert^2$, with population version $Q_{K_n}(f) = \lVert\Pi_{K_n}T(f - f_0)\rVert^2$.
- **(S5) Regularity.** $E[u \mid Z] = 0$ and $E[u^2] < \infty$. Every $f \in \mathcal H_n$ satisfies $\lvert f(x) - f_0(x)\rvert \le M$ for all $x$. For every tree $s \in \mathcal S_{L_n}$, $\theta \mapsto f_s(x;\theta)$ is $\Lambda_n$-Lipschitz in the sup norm on $\{\theta \in \Theta_s : f_s(\cdot;\theta) \in \mathcal H\}$, uniformly in $x$, with $\log\Lambda_n \le a(L_n + \log n)$ for some constant $a$.
- **(S6) Growth.** $\zeta_n^2 L_n(L_n + \log n)/n \to 0$, $\max_{s \in \mathcal S_{L_n}}\mathrm{pen}_n(s)/n \to 0$, and the scale estimate in the penalized criterion satisfies $\hat\sigma^2 = O_p(1)$.

**Theorem 3 (b).** Under (S1)–(S6), let $\hat f \in \mathcal H_n$ satisfy $Q_n(\hat f) \le \inf_{f \in \mathcal H_n}Q_n(f) + \eta_n$ with $\eta_n \to_p 0$. The penalized minimizer qualifies, with $\eta_n = \hat\sigma^2\max_s\mathrm{pen}_n(s)/n \to_p 0$ by (S6). Then $\lVert\hat f - f_0\rVert \to_p 0$.

*Proof.*

**Step 1 (identification modulus, uniform in $K$).** For $\varepsilon > 0$ let $\omega(\varepsilon) := \inf\{\lVert T(f - f_0)\rVert^2 : f \in \mathcal H,\ \lVert f - f_0\rVert \ge \varepsilon\}$. The set over which the infimum is taken is closed in the compact $\mathcal H$, hence compact; $f \mapsto \lVert T(f - f_0)\rVert^2$ is continuous and, by (S2), positive on it; so $\omega(\varepsilon) > 0$. The set $G := \{T(f - f_0) : f \in \mathcal H\}$ is compact in $L^2(P_Z)$, as the continuous image of a compact set. Strong convergence of the projections is uniform on compact sets: given $\delta > 0$, cover $G$ by finitely many balls of radius $\delta$; for $n$ large, $\lVert(I - \Pi_{K_n})h_j\rVert \le \delta$ at every centre $h_j$, and then $\lVert(I - \Pi_{K_n})h\rVert \le 3\delta$ for every $h \in G$, since $\lVert I - \Pi_{K_n}\rVert \le 1$. Hence there is $n_0(\varepsilon)$ such that for $n \ge n_0(\varepsilon)$ and every $f \in \mathcal H$ with $\lVert f - f_0\rVert \ge \varepsilon$,

$$\lVert\Pi_{K_n}T(f - f_0)\rVert \ \ge\ \lVert T(f - f_0)\rVert - \tfrac12\sqrt{\omega(\varepsilon)} \ \ge\ \tfrac12\sqrt{\omega(\varepsilon)}, \qquad\text{i.e.}\qquad Q_{K_n}(f) \ge \omega(\varepsilon)/4. \tag{6.1}$$

**Step 2 (uniform deviation).** Write $\hat g(f) = \bar u + g_{K_n}(f) + D_n(f)$ with $\bar u := n^{-1}\sum_i b^{(n)}(Z_i)u_i$, $g_{K_n}(f) := E[b^{(n)}(Z)(f_0 - f)(X)]$ and $D_n(f) := (P_n - P)[b^{(n)}(f_0 - f)]$. Then $Q_n(f) = \lVert\hat g(f)\rVert^2$ and $Q_{K_n}(f) = \lVert g_{K_n}(f)\rVert^2$, with $\lVert g_{K_n}(f)\rVert \le \lVert f - f_0\rVert \le M$ on $\mathcal H_n$.
- $E\lVert\bar u\rVert^2 = E[\lVert b^{(n)}\rVert^2u^2]/n \le \zeta_n^2E[u^2]/n \to 0$ by (S6), so $\lVert\bar u\rVert \to_p 0$.
- For the deviation, apply Lemma 3(c) to each tree $s \in \mathcal S_{L_n}$ with $h = f_0 - f_s$ on $\Theta' = \{\theta \in \Theta_s : f_s(\cdot;\theta) \in \mathcal H\}$, $M' = M$, $p = p_s \le L_n$, $\Lambda = \Lambda_n$, $K = K_n$, at level $t + \log\lvert\mathcal S_{L_n}\rvert$, and take a union bound. With probability at least $1 - e^{-t}$,

  $$\sup_{f \in \mathcal H_n}\lVert D_n(f)\rVert \ \le\ \Delta_n(t) := \frac{M}{\sqrt n}\Bigl[\sqrt{K_n} + 2\zeta_n + \zeta_n\sqrt{8\bigl(t + L_n\log(3m) + \log 2 + L_n\log(1 + 2C\Lambda_n\sqrt n/M)\bigr)}\Bigr].$$

  Since $K_n \le \zeta_n^2$ (because $K_n = E\lVert b^{(n)}\rVert^2 \le \zeta_n^2$) and $\log\Lambda_n \le a(L_n + \log n)$, (S6) gives $\Delta_n(t) \to 0$ for every fixed $t$; hence $\sup_{\mathcal H_n}\lVert D_n\rVert \to_p 0$.
- Therefore $R_n := \sup_{f \in \mathcal H_n}\lvert Q_n(f) - Q_{K_n}(f)\rvert \le (\lVert\bar u\rVert + \sup\lVert D_n\rVert)(2M + \lVert\bar u\rVert + \sup\lVert D_n\rVert) \to_p 0$.

**Step 3 (basic inequality).** By (S3), pick $f_n^* \in \mathcal H_n$ with $\lVert f_n^* - f_0\rVert \to 0$; then $Q_{K_n}(f_n^*) \le \lVert f_n^* - f_0\rVert^2 \to 0$. Now

$$Q_{K_n}(\hat f) \ \le\ Q_n(\hat f) + R_n \ \le\ Q_n(f_n^*) + \eta_n + R_n \ \le\ Q_{K_n}(f_n^*) + 2R_n + \eta_n \ \to_p\ 0.$$

**Step 4.** Fix $\varepsilon > 0$. For $n \ge n_0(\varepsilon)$, by (6.1) and $\hat f \in \mathcal H$,

$$P(\lVert\hat f - f_0\rVert \ge \varepsilon) \ \le\ P\bigl(Q_{K_n}(\hat f) \ge \omega(\varepsilon)/4\bigr) \ \to\ 0. \qquad\blacksquare$$

**Lemma 4 (approximation within a Lipschitz ball): (S3) holds in two settings.**

(a) **One regressor, compact support $[x_{\mathrm{lo}}, x_{\mathrm{hi}}]$, operators $+$, $-$, $\times$, $\max$.** Let $\mathcal H := \{f : \lVert f\rVert_\infty \le A,\ \mathrm{Lip}(f) \le \Lambda_0\}$ and $f_0 \in \mathcal H$. For $k \ge 1$, the piecewise-linear interpolant $I_kf_0$ of $f_0$ at $k + 1$ equally spaced knots is

$$I_kf_0(x) = a + bx + \sum_{j=1}^{k-1}c_j\max(x - \kappa_j, 0),$$

a tree with $5 + 8(k-1) \le 8k$ nodes: five for $a + bx$ and eight for each hinge. Its constants satisfy $\lvert b\rvert \le \Lambda_0$, $\lvert c_j\rvert \le 2\Lambda_0$, $\lvert\kappa_j\rvert \le \bar x := \max(\lvert x_{\mathrm{lo}}\rvert, \lvert x_{\mathrm{hi}}\rvert)$ and $\lvert a\rvert \le A + \Lambda_0\bar x$, so $I_kf_0 \in \mathcal F_{8k}$ as soon as $C \ge \max(2\Lambda_0,\ A + \Lambda_0\bar x,\ \bar x)$. It lies in $\mathcal H$: its values are convex combinations of values of $f_0$, and its slopes are difference quotients of $f_0$. And $\lVert I_kf_0 - f_0\rVert_\infty \le \Lambda_0(x_{\mathrm{hi}} - x_{\mathrm{lo}})/(2k)$: on a subinterval of width $h := (x_{\mathrm{hi}} - x_{\mathrm{lo}})/k$, at the point $x = \lambda x_j + (1 - \lambda)x_{j+1}$ the error is $\lvert\lambda(f_0(x) - f_0(x_j)) + (1-\lambda)(f_0(x) - f_0(x_{j+1}))\rvert \le 2\lambda(1-\lambda)\Lambda_0h \le \Lambda_0h/2$. With $L \ge 8$ nodes, $k = \lfloor (L+3)/8\rfloor \ge (L-4)/8$ knots are allowed, so $\inf_{\mathcal F_L \cap \mathcal H}\lVert f - f_0\rVert \le 4\Lambda_0(x_{\mathrm{hi}} - x_{\mathrm{lo}})/(L-4) \le 8\Lambda_0(x_{\mathrm{hi}} - x_{\mathrm{lo}})/L \to 0$.

(b) **Any number of regressors, support $[0,1]^d$, operators $+$, $-$, $\times$.** Let $\mathcal H := \{f : \lVert f\rVert_\infty \le A,\ f \text{ is } \Lambda_0\text{-Lipschitz in each coordinate}\}$ and $f_0 \in \mathcal H$. The Bernstein polynomial

$$B_kf_0(x) = \sum_{j \in \{0, \dots, k\}^d} f_0(j/k)\prod_{i=1}^d\binom{k}{j_i}x_i^{j_i}(1 - x_i)^{k - j_i}$$

satisfies: (i) $\lVert B_kf_0\rVert_\infty \le \lVert f_0\rVert_\infty$, as $B_k$ is positive and reproduces constants; (ii) $B_kf_0$ is $\Lambda_0$-Lipschitz in each coordinate, because the one-dimensional Bernstein operator preserves Lipschitz constants ([Brown, Elliott & Paget 1987](https://doi.org/10.1016/0021-9045(87)90087-6)), the $d$ one-dimensional operators commute, and each is a positive operator in its own variable, which preserves Lipschitz continuity in the other variables; (iii) $\lVert B_kf_0 - f_0\rVert_\infty \to 0$ as $k \to \infty$ (Lorentz 1953, Ch. 2; a coordinatewise telescoping of the one-dimensional bound gives at most $2d\Lambda_0/\sqrt k$). So $B_kf_0 \in \mathcal H$. It is a polynomial with $(k+1)^d$ terms, each a product of $d$ factors of degree at most $k$ times a coefficient $f_0(j/k)\prod_i\binom{k}{j_i}$; writing each binomial coefficient, which is at most $2^k$, as a product of $O(k)$ factors in $[1, C]$ and each value $f_0(j/k) \in [-A, A]$ as a constant, which needs $C \ge \max(A, 1)$ with $C > 1$ (the constant $1$ in $1 - x_i$ must also be admissible), $B_kf_0$ is a tree with $O(d\,k^{d+1})$ nodes. Hence $\inf_{\mathcal F_L \cap \mathcal H}\lVert f - f_0\rVert \to 0$ as $L \to \infty$. $\blacksquare$

**Remarks.**
- **Compactness of $\mathcal H$.** In both settings $\mathcal H$ is a bounded equicontinuous family on a compact set, so it is compact in the sup norm (Arzelà–Ascoli), hence in $L^2(P_X)$; (S1) holds. The bounded-difference part of (S5) holds with $M = 2A$.
- **Unbounded support** *(beyond the paper)*. For the lognormal designs, take $\mathcal H := \{f : \lvert f(x)\rvert \le A(1 + \lVert x\rVert)^{\beta},\ \text{coordinatewise } \Lambda_0\text{-Lipschitz}\}$ with $E(1 + \lVert X\rVert)^{2\beta} < \infty$. It is compact in $L^2(P_X)$: a sequence has a subsequence converging uniformly on every ball (Arzelà–Ascoli with a diagonal argument), and the tails contribute at most $4A^2E[(1 + \lVert X\rVert)^{2\beta}\mathbf 1\{\lVert X\rVert > R\}] \to 0$ uniformly. Two things are then not done: the approximants must respect the growth envelope (polynomials do not; clipping with $\max$ and $\min$ does, at the cost of nodes), and the bounded-difference condition in (S5) fails, so Lemma 3(c) needs a version with an unbounded envelope. Both look routine; neither is written out.
- **The operator `max`.** The Phase 4 ablation showed that dropping `max` did not help selection. Lemma 4(a) gives a separate reason to keep it: with bounded constants, `max` is what makes one-regressor formulas a free-knot spline sieve.
- **The Lipschitz constraint.** (S1) restricts the candidates to $\mathcal H$. The code does not enforce it; Theorem 3(b) says what would be needed for consistency when the law is not a short formula: a bound on the slope of candidate formulas over the support, checked on a grid.

**Proposition 3.3 (rates reduce to a modulus on the sieve).** Under (S1)–(S6), define the sieve modulus

$$\omega_n(\varepsilon) := \inf\{\lVert\Pi_{K_n}T(f - f_0)\rVert^2 : f \in \mathcal H_n,\ \lVert f - f_0\rVert \ge \varepsilon\},$$

nondecreasing in $\varepsilon$, and its generalized inverse $\omega_n^{-1}(q) := \sup\{\varepsilon : \omega_n(\varepsilon) \le q\}$. Then

$$\lVert\hat f - f_0\rVert \ \le\ \omega_n^{-1}\bigl(Q_{K_n}(\hat f)\bigr), \qquad Q_{K_n}(\hat f) \ \le\ \inf_{f \in \mathcal H_n}\lVert f - f_0\rVert^2 + 2R_n + \eta_n,$$

with $R_n = O_p\bigl(M\lVert\bar u\rVert + M\Delta_n(t)\bigr)$, where $\lVert\bar u\rVert = O_p(\zeta_n/\sqrt n)$ and $\Delta_n(t)$ is as in Step 2.

*Proof.* If $\lVert\hat f - f_0\rVert = \varepsilon$, then $\omega_n(\varepsilon) \le Q_{K_n}(\hat f)$ by definition, so $\varepsilon \le \omega_n^{-1}(Q_{K_n}(\hat f))$. The second bound is Step 3. $\blacksquare$

- **What is known.** For a linear sieve, $\omega_n(\varepsilon) = \varepsilon^2/\tau_n^2$ with $\tau_n$ the sieve measure of ill-posedness of Chen & Pouzo (2012), and the proposition gives their rate $\tau_n\,(\text{approximation} + \text{variance})$.
- **What is open** *(beyond the paper)*. $\mathcal F_{L_n} - f_0$ is not a linear space: for instance $\{x^\theta : \theta \in [-C, C]\}$ spans an infinite-dimensional space. So $\omega_n(\varepsilon)$ can fall below any quadratic $\varepsilon^2/\tau_n^2$, and the ratio $\lVert f - f_0\rVert/\lVert T(f - f_0)\rVert$ is not bounded on the sieve. Bounding $\omega_n$ for formula sieves is the open rate problem. In the well-specified case the rate is parametric (Corollary 1.1).

---

## 7. What the Monte Carlo says about the theory

| Prediction | Result | Evidence (README §12) |
|---|---|---|
| Consistent selection needs $\kappa_n \to \infty$; AIC is not selection-consistent | Theorem 1, Remark 2 | BIC > HQIC > AIC in Phases 2 and 4 (51% / 44% / 24% pooled) |
| Selection works for any generator that covers the truth | Theorem 1, Remark 3 | Plain-PySR front + MMSC recovers the law as often as the IV fronts; recovery given coverage 65–96% |
| Wrong formulas lose when the margin $n\delta_s/\sigma^2 - (p_0 - p_s)\kappa_n$ is positive, up to deviation terms | Theorem 2 (I) | Spearman 0.56 across 32 cells; 74% vs. 23% recovery |
| Long contrived formulas need a per-node penalty | Theorem 2 (II) and Corollary 2.2, as a direction only: the weight the bound asks for ($w \approx 5$) is ten times the empirical one, and the same-size near-duplicates that $w$ fixed in the data fall under neither channel (§4, "Reading Theorem 2") | BIC + structure 60% vs. BIC 51%; 98–100% from $n = 5000$ (50 seeds) vs. a BIC plateau at 75–92% |
| Discrete instruments: formulas with $\ge J$ constants can zero the criterion | Proposition 4 | D4: a wrong four-term formula sets the criterion to $10^{-33}$–$10^{-32}$ for three of the four laws while 0.1–0.4 sd from $f_0$ ([experiments/phase5/discrete.md](experiments/phase5/discrete.md)) |
| Cross-fitting is not selection-consistent for the minimal tree | Theorem 1, Remark 4 | Cross-fitted criterion 28% |
| More candidates bring more wrong formulas that outscore the truth: the pool's size is a cost (the union over candidates in channel (II)) | Theorem 2 (II); Corollary 2.3 | README §12.6: an eight-fold search budget raises coverage from 25% to 55% but recovery only from 10% to 19%; recovery given coverage falls from 41% to 22% as the pool grows from about 26 to 78 candidates |
| Split-sample intervals and AR sets have nominal coverage | Theorem 1 (iii) | §7.1 |
| Candidates from an independent sample reduce the beaters | Corollary 2.3 | §7.1 |
| The formula confidence set contains the true form with probability $\ge 95\%$, and the diagnostic flags the weak instrument | Proposition 5 | §7.1 |

### 7.1 Simulations written for this phase

Both reuse the Phase 4 Pareto fronts, so no new searches were needed. Scripts: `experiments/phase5_inference.py`, `experiments/phase5_split.py`, `experiments/phase5_report.py`; full tables in [experiments/phase5/summary.md](experiments/phase5/summary.md).

**Theorem 1 (iii): inference after selection.** For each of the 288 Phase 4 breadth runs ($n = 2000$; one run is excluded because a fresh-sample refit failed numerically, an SVD that did not converge), two trees: the law's own form (oracle), and the formula that the pooled candidates with BIC + structure selected on the Phase 4 sample $A$, when it has the true form (selected). Each tree is estimated by two-step efficient GMM on 10 fresh samples $B$, independent of $A$, and on $A$ itself. Nominal 95% intervals; 2,870 oracle fits and 1,220 selected-tree fits on fresh samples.

| | Constants | $f$ at the median | Elasticity | $J$ rejects (5%) | AR covers |
|---|---|---|---|---|---|
| D1–D4, oracle, fresh $B$ | 93–95% | 93–94% | 92–96% | 3–6% | 93–97% |
| D1–D4, selected tree, fresh $B$ | 92–98% | 94–95% | 92–94% | 3–7% | 93–97% |
| D1–D4, selected tree, **same sample $A$** | 83% / 90% / 83% / 94% | 87–100% | 88–96% | 0–6% | 94–97% |
| D5 (weak $Z$), oracle, fresh $B$ | **76%** | **68%** | **64%** | 10% | **97%** |

- On independent samples the intervals, the $J$ test and the AR sets behave as Theorem 1(iii) says, for the selected tree as for the oracle. The standard errors are calibrated: the standard deviation of $\hat\theta - \theta_0$ across the fresh samples is 0.84–1.00 times the mean reported standard error.
- **Same-sample inference after selection is distorted**: on $A$, the selected tree's intervals cover the constants in 83% (D1), 90% (D2) and 83% (D3) of cases, against 91–95% for the oracle on the same samples. This is the Leeb–Pötscher effect that splitting removes. (The same-sample cells have 12 fits each, so the design totals are the figures to read.)
- **Weak instruments** (D5): Wald intervals for the oracle tree cover the constants 76% of the time, the function at the median 68%, the elasticity 64%, and the $J$ test over-rejects (10%). The AR set at the true constants covers 97%. That is the "without (A5)(c)" clause of Theorem 1(iii): AR inference survives weak identification of the constants, Wald inference does not.
- (A5)(a) held: every selected tree had a unique set of constants reproducing $f_0$.

**Corollary 2.3: candidates from one sample, selection on another.** D1 strong setting ($\pi = 0.7$, $\rho = 1.2$), the $n$-scaling fronts at $n = 1000$ (plain + one-step + distilled, 12 seeds). Three selections of the same candidates: same-sample at $n = 1000$ (as in Phase 4); split, selecting on 5 fresh samples of $n = 1000$ each; and, as the full-sample reference, same-sample selection at $n = 2000$ on fronts generated at $n = 2000$.

| Law, set | Rule | Same-sample, $n = 1000$ | Split, $1000 + 1000$ | Same-sample, $n = 2000$ | Beaters per run: same 1000 / split / same 2000 |
|---|---|---|---|---|---|
| $2x^{0.7}$, pooled | BIC | 33% | 45% | 33% | 1.92 / 1.37 / 1.50 |
| $2x^{0.7}$, pooled | BIC + structure | 42% | 47% | **67%** | |
| $2x^{0.7}$, distilled | BIC | 50% | 73% | 67% | 0.50 / 0.33 / 0.42 |
| $2x^{0.7}$, distilled | BIC + structure | 58% | 72% | **83%** | |
| $1 + 2\log x$, pooled | BIC | 58% | 83% | 100% | 0.42 / 0.12 / 0.17 |
| $1 + 2\log x$, pooled | BIC + structure | 83% | 92% | **100%** | |
| $1 + 2\log x$, distilled | BIC | 100% | 98% | 92% | 0.00 / 0.00 / 0.08 |

- **The mechanism is real.** Wrong candidates that beat the true form become rarer when they were not fitted to the selection sample's noise: 1.92 → 1.37 per run for the power law, 0.42 → 0.12 for the log law, fewer even than same-sample selection at $n = 2000$. At equal selection size, recovery changes by $-2$ to $+25$ points across the seven rows (median $+12$).
- **But it is not the best use of the data here.** With the structure term, same-sample selection on the full $n = 2000$ beats split selection in all three BIC + structure cells (67% vs. 47%, 83% vs. 72%, 100% vs. 92%). Halving the selection sample halves $n\delta_s$ in condition (I), and the failures that remain in these cells are separation failures, which splitting makes worse. With BIC alone, split and full-sample selection are mixed (45% vs. 33% and 73% vs. 67% for the power law; 83% vs. 100% for the log law). Each cell has 12 candidate sets, so the split figures (60 selections) are not 60 independent trials.

**Proposition 5: the identification diagnostic.** `identification_report` was run on every Phase 4 breadth run, with the pooled candidates and the formula selected from them by BIC + structure (630 runs after the 50-seed extension of README §11; $\tau = 0.2$; `experiments/phase5_identification.py`; recomputed on 2026-10-02 with the final distance scale and cap).

| | Runs | Flagged (weakly identified or rejected) | Of which rejected | True form in the confidence set |
|---|---|---|---|---|
| D5 weak instrument, all runs | 250 | **100%** | 16% | 99% (103 of the 104 runs with the true form a candidate) |
| D1–D4, selection recovered the form | 257 | 4% | 2% | 99% |
| D1–D4, statistical failure (true form a candidate, lost) | 43 | 30% | 7% | 100% |
| D1–D4, search failure (true form not a candidate) | 80 | 54% | 14% | – |

- **Coverage, Proposition 5(a):** across the 404 runs in which the true form was a candidate, it is in the confidence set in 400 (99%; nominal $\ge 95\%$).
- **The weak instrument is always caught.** In D5 the median first-stage $F$ is 3, 88% of the candidates are not rejected, and the farthest member of the set differs from the selected formula by 0.8 sd (median). The method no longer returns a confident wrong formula there: 84% of the runs are "weakly identified", with the formulas the data also allow listed, and 16% "rejected".
- **False alarms:** 4% of the strong-instrument runs whose selection was right, the rate the 5% AR level implies. At $\tau = 0.1$ it would be 14%, with 58% of the statistical failures caught instead of 30%; the full trade-off is in [experiments/phase5/summary.md](experiments/phase5/summary.md).
- **Statistical failures, Proposition 5(b):** the true form was in the confidence set in all 43; the diagnostic reports it as a different formula in 30%. The other 70% are near-duplicates within $0.2$ sd of the truth, Theorem 2's channel (II): the function is identified, only the tree is not minimal.
- **Search failures:** 54% flagged (14% rejected outright), because the candidates that fit the moments disagree among themselves. The rest, mostly D3 with the kink and saturation laws, pass as "identified": the wrong formula fits the moments and the other candidates agree with it. No diagnostic computed from the candidates can detect that case.
- **Discrete instrument (D4):** 35% of runs are "weakly identified" despite $F \approx 640$. With $K = 4$ moments the S test has little power, and the set contains formulas up to 0.13 sd away (median): Proposition 4 in the data.

The Monte Carlo evidence for the rest of the table is in README §12.3.

## 8. Next steps

**For the paper.**
1. A human reading of the proofs before submission. The third pass (§9) was by fresh-context referees, which is not the same thing; it is no longer a blocker.
2. Done (2026-10-02): the headline cells of the Monte Carlo have 50 seeds (README §12.3), and the search-budget and template experiment is in README §12.6.

**Beyond the paper** (stated there as open problems):
1. **Theorem 2:** the efficient weight under heteroskedasticity with its estimation error (Proposition 2.4 plus a concentration bound for $\hat\Omega$); the exact kernel criterion (degenerate U-processes).
2. **Theorem 3(b):** unbounded supports (envelope-respecting approximants; Lemma 3(c) with an unbounded envelope); then the modulus $\omega_n$ for specific formula sieves (Proposition 3.3).
3. **Conjecture 4(c):** a design family of dimension $\ge J - p_s$ for which the regular-value condition can be verified.
4. **Theorem 1(iii)**, uniformity: the result is pointwise; a uniform version over designs with $\delta_s \ge \underline\delta$ would follow from Theorem 2 with explicit $n$.

## 9. Review log (second pass)

Every statement and proof of the first pass was re-derived. Findings, and what changed:

1. **Parameter sets were not compact where a formula can be undefined** (e.g. $\log(x - c)$ near the support). $\Theta_s$ is now a closed subset of the cube on which the formula is finite and (A3) holds. Lemma 1 and everything after it need this.
2. **The penalty gap $\pi_s$ of Theorem 2 was ambiguous** when several minimal true trees have different sizes, since which one the candidate set contains is data-dependent. It is now defined against the minimal true tree with the largest penalty, the worst case.
3. **The chaining step (old Lemma 3(d)) carried an unspecified absolute constant $C_0$**, and its failure probability was not justified in detail. Replaced by a projection bound: $W_s \le \lVert P_{V_s}Z\rVert$ with $V_s$ the span of the localized directions, controlled by the same quadratic-form inequality as $\lVert Z\rVert^2$. Theorem 2 now has explicit constants and probability $1 - 5e^{-t}$; Corollary 2.2's condition on $w$ is explicit.
4. **"Lower-order terms" in the reading of Theorem 2 was wrong.** The deviation term $d_t^2$ is of order $\log n$, the same as $\kappa_n = \ln n$. The reading now says so, and separates the population margin (what Phase 4 computed) from the finite-sample condition.
5. **The AIC remark stated a limit without hypotheses.** It now gives the nested-$\chi^2$ argument and the regularity it needs.
6. **Theorem 3(b) was a sketch.** It is now proved directly (Steps 1–4), without the Chen–Pouzo machinery, with the compactness, identification, approximation, instrument and growth conditions (S1)–(S6) stated. The approximation condition is verified for one regressor with `max` (hinge splines) and for any number of regressors with $+$, $-$, $\times$ (Bernstein polynomials, which preserve the Lipschitz ball); the first pass only had the one-regressor case.
7. **Rates were listed as open without saying what is and is not known.** Corollary 1.1 (parametric rate in the well-specified case) and Proposition 3.3 (reduction to a sieve modulus) were added; bounding the modulus for formula sieves remains open, and the obstruction is stated.
8. **The code's criterion was not covered**: Theorem 2 assumed population-orthonormal instruments. Proposition 2.4 and Corollary 2.5 extend it to the sample-orthonormalized criterion and an estimated scale, with explicit perturbation terms; a remark gives the substitution rule for general weights and for the Nyström kernel criterion.
9. **(F3) was presented as a mild condition.** It needs a bounded class, which the lognormal designs violate; the text now says it is an idealization that holds after truncation.
10. **Proposition 4(c)** was a sketch with the hypothesis implicit. It is now a conjecture with the transversality hypothesis stated, and with the reason it cannot be made automatic (the design family needs dimension $\ge J - p_s$).
11. **Two claims of Theorem 1(iii) and Corollary 2.3 were untested.** The simulations in §7.1 test them on the saved Phase 4 fronts.

Checked and unchanged: Lemma 1, Lemma 2, Theorem 1(i)–(iii), Proposition 2.1 (algebra re-derived), Lemma 3(a)–(c) (constants re-derived: the matrix Bernstein solution, the quadratic-form bound, the covering count and McDiarmid's constant), Proposition 4(a)–(b), Theorem 3(a), the tree-count bound $\log\lvert\mathcal S_L\rvert \le L\log(3m) + \log 2$.

### Third pass (2026-10-01): two fresh-context referees

Two separate reviewers, model instances with no memory of writing the document, read the proofs cold, one for §0–§3 and one for §4–§7, with instructions to recompute every constant. Their verdict: the theorem statements and proofs stand (Lemmas 1–4, Theorems 1–3, Proposition 2.1, Lemma 3 with all constants, Propositions 2.4, 3.3 and 4, and the §7 figures against README §12 and the experiment summaries); the errors were in Proposition 5 and in informal readings. Findings, most severe first, and what changed:

1. **Proposition 5(a) with the sample envelope** (error). The proof took $\theta_0$ to be feasible, which the data-dependent envelope $\max_i\lvert f_s(X_i;\theta)\rvert \le 3\max_i\lvert y_i\rvert$ does not guarantee under (A1) alone (an error that offsets the law where it is largest violates it). The proposition is now stated for $\Theta_s$; the enveloped version needs condition (E), stated with when it holds.
2. **Proposition 5(b)** (error). It read as a conditional probability; (a) gives a joint bound. Now stated as $P(E \cap \{s_0 \notin \mathcal C_\alpha\}) \le \alpha + o(1)$ with the conditional bound $(\alpha + o(1))/P(E)$ made explicit; the second claim is now asymptotic.
3. **Proposition 5(c), one step** (error). $B_n = O_p(1)$ was justified by the envelope, but $\max_i y_i^2$ is not $O_p(1)$. Now bounded by (A3); the envelope is not needed for (c).
4. **The winsorized weight** (gap). "Holds up to that share" was not a result. Replaced by the limit $\xi'\Omega^{1/2}\Omega_c^{-1}\Omega^{1/2}\xi$, a size bound, the $t_3$ example (10–15% instead of 5%), and a slowly growing cap $c_n = \max(5, \sqrt{2\ln n})$, now implemented, which makes the statistic exact in the limit and changes nothing at the sample sizes used. Why the centred weight of Hansen, Heaton & Yaron does not address the problem is stated.
5. **Theorem 1(iii)** (gap). The split must not depend on the data, and the generator, $\hat\sigma^2$ and refits must run on $A$ only: now stated. The AR clause is rewritten as pointwise, with (A2$_K$) and (A5)(a) kept.
6. **(A5)(a)** (gap). A singleton zero set excluded sign-symmetric trees such as $(ax)^2$. Now a finite set of interior zeros, with $\theta_{0s}$ the nearest one; Corollary 1.1 and Theorem 1(iii) argue consistency to the set and then locally. The unused second derivative in (A5)(b) was dropped, and Lemma 2(a)'s moment setting is cited where $\hat\Omega$'s consistency needs it.
7. **Reading of Theorem 2, over-parameterized true trees** (error). "$k_s \le p_s$" is false for trees nonlinear in $\theta$ at finite $n$ (with $g(\theta) = (\theta, \theta^2)$ the localized directions span $\mathbb R^2$). Replaced by the exact bound for trees linear in their constants and a first-order bound through the Jacobian span with an $O(z_t^2r_t/\sqrt n)$ remainder.
8. **Corollary 2.2, "Numbers"** (gap). Only the $w = 0$ side was shown. The paragraph now computes the corollary's own side: with $w \approx 5.7$ the leftover term $w\bar\ell_0\log m \approx 79$ certifies nothing at $n = 2000$; $w$ also enters channel (I) against shorter wrong trees; the empirical effect of $w$ is the "neither channel" case. The §7 table row credits the direction only.
9. **Corollary 2.2, step 1** (gap). Tree-specific deviation levels were not licensed by Proposition 2.1 and Theorem 2 as stated. A remark after Proposition 2.1 and a sentence at the end of Theorem 2's proof now allow them.
10. **Corollary 2.5** (gap). The scale event carried no probability, and a candidate-dependent scale is a candidate-dependent weight. Now an explicit assumption with probability $1 - e^{-t}$ (total $1 - 6e^{-t}$), with the candidate-dependent case deferred to the estimated-weight item; the order of $\varepsilon_n(t)$ corrected to $\sqrt{\zeta_K^2\log K/n}$.
11. **Corollary 2.3 remark** (unclear). It was applied to Phase 4, whose candidates came from the selection sample. Rewritten as a counterfactual.
12. **Minor.** §7.1: "10–25 points" is "$-2$ to $+25$, median $+12$"; "every cell except the easiest" is "all three BIC + structure cells". The D4 figures of §5 are now produced by `experiments/phase5_discrete.py` and cited. Lemma 4(a): the sharper interpolation error $\Lambda_0h/2$ and the bound stated for $L \ge 8$. Lemma 4(b): $O(d\,k^{d+1})$ nodes, with $C \ge \max(A, 1)$. (S6) now includes $\hat\sigma^2 = O_p(1)$. $\bar\ell_0$ defined as the maximum size over minimal true trees. The $\chi^2$ calibration of $n\hat Q/\hat\sigma^2$ and of the AIC remark now states its homoskedasticity or efficient-weight condition. Lemma 2(b) states separability and shows continuity. The AR half-width factor is $\sqrt{(\chi^2_{K,1-\alpha} - J)/\chi^2_{1,1-\alpha}}$.

## References

- Andrews, D. W. K., & Cheng, X. (2012). Estimation and inference with weak, semi-strong, and strong identification. *Econometrica*, 80(5). https://doi.org/10.3982/ECTA9456
- Andrews, D. W. K., & Lu, B. (2001). Consistent model and moment selection procedures for GMM estimation. *Journal of Econometrics*, 101(1). https://doi.org/10.1016/S0304-4076(00)00077-4
- Brown, B. M., Elliott, D., & Paget, D. F. (1987). Lipschitz constants for the Bernstein polynomials of a Lipschitz continuous function. *Journal of Approximation Theory*, 49(2). https://doi.org/10.1016/0021-9045(87)90087-6
- Chen, X. (2007). Large sample sieve estimation of semi-nonparametric models. *Handbook of Econometrics*, 6B. https://doi.org/10.1016/S1573-4412(07)06076-X
- Chen, X., & Pouzo, D. (2012). Estimation of nonparametric conditional moment models with possibly nonsmooth generalized residuals. *Econometrica*, 80(1). https://doi.org/10.3982/ecta7888
- Graves, L. M. (1950). Some mapping theorems. *Duke Mathematical Journal*, 17(2). https://doi.org/10.1215/S0012-7094-50-01713-3
- Guillemin, V., & Pollack, A. (1974). *Differential Topology*. Prentice-Hall.
- Hall, A. R., & Inoue, A. (2003). The large sample behaviour of the generalized method of moments estimator in misspecified models. *Journal of Econometrics*, 114(2). https://doi.org/10.1016/S0304-4076(03)00089-7
- Hansen, L. P. (1982). Large sample properties of generalized method of moments estimators. *Econometrica*, 50(4). https://doi.org/10.2307/1912775
- Hsu, D., Kakade, S., & Zhang, T. (2012). A tail inequality for quadratic forms of subgaussian random vectors. *Electronic Communications in Probability*, 17. https://doi.org/10.1214/ECP.v17-2079
- Leeb, H., & Pötscher, B. M. (2005). Model selection and inference: facts and fiction. *Econometric Theory*, 21(1). https://doi.org/10.1017/S0266466605050036
- Lorentz, G. G. (1953). *Bernstein Polynomials*. University of Toronto Press.
- McDiarmid, C. (1989). On the method of bounded differences. *Surveys in Combinatorics*, 141.
- Muandet, K., Jitkrittum, W., & Kübler, J. (2020). Kernel conditional moment test via maximum moment restriction. *UAI 2020*.
- Newey, W. K., & McFadden, D. (1994). Large sample estimation and hypothesis testing. *Handbook of Econometrics*, 4. https://doi.org/10.1016/S1573-4412(05)80005-4
- Newey, W. K., & Powell, J. L. (2003). Instrumental variable estimation of nonparametric models. *Econometrica*, 71(5). https://doi.org/10.1111/1468-0262.00459
- Stock, J. H., & Wright, J. H. (2000). GMM with weak identification. *Econometrica*, 68(5). https://doi.org/10.1111/1468-0262.00151
- Tropp, J. A. (2012). User-friendly tail bounds for sums of random matrices. *Foundations of Computational Mathematics*, 12(4). https://doi.org/10.1007/s10208-011-9099-z
- Vuong, Q. H. (1989). Likelihood ratio tests for model selection and non-nested hypotheses. *Econometrica*, 57(2). https://doi.org/10.2307/1912557
- Zhang, R., Imaizumi, M., Schölkopf, B., & Muandet, K. (2020). Instrumental variable regression via kernel maximum moment loss (first version: "Maximum moment restriction for instrumental variable regression"). https://arxiv.org/abs/2010.07684
