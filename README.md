# Symbolic IV: Discovering Structural Equations under Endogeneity

Symbolic regression that recovers the **structural** relation $f(X)$ rather than the conditional mean $E[y \mid X]$, by scoring the formula search with instrumental-variable moment conditions.

Code layout and setup: §12.

---

## 1. The gap

Symbolic regression (SR) searches over mathematical expressions for the formula that best **predicts** $y$ from $X$, so it estimates $E[y \mid X]$.

When $X$ is **endogenous** (chosen by agents, set simultaneously with $y$, confounded, or mismeasured):

$$y = f(X) + u, \qquad E[u \mid X] \neq 0 \;\Rightarrow\; E[y \mid X] = f(X) + E[u \mid X] \neq f(X).$$

SR then returns a formula that fits well but is **not the structural law**.

Econometrics handles endogeneity in several ways, and each loses something:

| Approach | Handles endogeneity | Limitation |
|---|---|---|
| Parametric IV (2SLS / GMM) | Yes | Functional form must be known in advance |
| Sparse IV over a term library (STIV, penalized GMM, IV-Lasso) | Yes | Law must be linear in its parameters over a library fixed in advance |
| Nonparametric IV (Newey–Powell; DeepIV, KIV, DeepGMM) | Yes | Returns a black box; the estimation problem is ill-posed and unstable |
| Symbolic regression (PySR, DSR, AI Feynman, SINDy) | **No** | Interpretable formula, but of $E[y \mid X]$, not $f$ |

**Gap:** no method searches over **free-form** formulas while enforcing

$$E[\,y - f(X) \mid Z\,] = 0.$$

Two neighbours come close and must be beaten, not ignored (§3.2):

- **Sparse IV over a term library** selects terms under endogeneity, but only for laws that are linear in their parameters over a library chosen in advance: $a + b\log x$ yes; $x^{\theta}$ with unknown $\theta$, a kink at an unknown point, or $ax/(b+x)$ no.
- **Nonparametric IV followed by symbolic distillation** (fit $\hat f$ with KIV or DeepIV, then run SR on $(X, \hat f(X))$) does produce a formula, but inherits the instability of the NPIV fit and has no selection theory.

## 2. Why it matters

1. **Economics:** almost every regressor of interest is endogenous: prices, schooling, hours, policy take-up. SR is starting to be applied to economic data ([Balla et al. 2025](https://doi.org/10.1057/s41599-025-04405-x)), and without this fix it produces convincing but non-causal "laws".
2. **The functional form is the policy answer:** elasticities that change with the level, thresholds, diminishing returns. Parametric IV assumes the form; black-box NPIV hides it.
3. **A theoretical hook:** NPIV is an ill-posed inverse problem ([Newey & Powell 2003](https://doi.org/10.1111/1468-0262.00459); [Hall & Horowitz 2005](https://doi.org/10.1214/009053605000000714)). Restricting $f$ to short expressions **with bounded constants** turns it into a selection among finitely many parametric models, much as sieve methods regularize ([Blundell, Chen & Kristensen 2007](https://doi.org/10.1111/j.1468-0262.2007.00808.x); [Chen & Pouzo 2012](https://doi.org/10.3982/ecta7888)). Ill-posedness then enters only through how well the instruments separate the true formula from its competitors (the separation constant $\delta_L$, §7). Expression length alone is not enough: $\sin(c\,x)$ has four nodes, yet for large $c$ it is exactly the kind of high-frequency function that $E[\,\cdot \mid Z]$ barely sees.
4. **Beyond economics:** Mendelian randomization in epidemiology, closed-loop and errors-in-variables settings in engineering, and any system with feedback.

## 3. Related work

### 3.1 Closest work, and why each isn't the gap

| Work | What it does | Why it's not the gap |
|---|---|---|
| DeepIV ([Hartford et al. 2017](https://proceedings.mlr.press/v70/hartford17a.html)), KIV ([Singh et al. 2019](https://arxiv.org/abs/1906.00232)), DeepGMM ([Bennett et al. 2019](https://arxiv.org/abs/1905.12495)), AGMM ([Lewis & Syrgkanis 2018](https://arxiv.org/abs/1803.07164)), minimax conditional moments ([Dikkala et al. 2020](https://arxiv.org/abs/2006.07201)), DFIV ([Xu et al. 2021](https://arxiv.org/abs/2010.07154)), MMR ([Zhang et al. 2020](https://arxiv.org/abs/2010.07684)) | Nonparametric IV with ML | Black box; no formula comes out |
| IV in nonlinear system identification ([Zeiringer et al. 2026](https://doi.org/10.1016/j.jfranklin.2026.108619)) | Instruments against measurement noise | Parametric model classes, not free-form formulas; not choice-driven endogeneity |
| IV system identification with synthesized instruments ([Kuang & Lin 2026, PMLR 331](https://arxiv.org/abs/2511.09024)) | Output-error model: deterministic signal observed with measurement noise; model linear in parameters over a **known, fixed** term library; instruments built from the same data by local polynomial smoothing at off-grid points; finite-sample $L^p$ consistency | **Close neighbour, but different problem.** Only measurement noise (errors-in-variables), no structural endogeneity; explicitly *"focuses on the regression step, rather than (regularized or sequential) sparse model selection"*, so no search over formulas; no external instruments |
| Closed-form ODE discovery for treatment effects, INSITE ([Kacprzyk et al. 2024](https://arxiv.org/abs/2403.10766)) | Symbolic/closed-form causal model in longitudinal data | Assumes ignorability (no unobserved confounding) |
| Causally constrained SR, SRIT ([Yan et al., SSRN 6879831](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=6879831); [code](https://github.com/Super-SUM-Plus/SRIT)) | GP-based SR (Eureqa) followed by pruning of candidate **inputs** with HSIC residual-independence tests (causal asymmetry, Markov property); output = direct-driver set + formula | **Different problem.** Selects *which variables* enter, not *how to fit* under endogeneity; guarantees assume **causal sufficiency (no unobserved confounders)**; under latent confounding it only retains variables conservatively. Authors state: *"formal guarantees under causal insufficiency remain limited."* No instruments or moment conditions |
| Causal discovery followed by SR ([Li et al. 2026](https://doi.org/10.1016/j.ejrh.2026.103355)) | Causal discovery (PCMCI) chooses variables, then SR fits | Variable selection does not remove endogeneity bias |
| SR in social science ([Balla et al. 2025](https://doi.org/10.1057/s41599-025-04405-x)) | Formulas for economic and sociological data | Predictive formulas; endogeneity not addressed |
| Theory-constrained SR: shape constraints ([Kronberger et al. 2022](https://arxiv.org/abs/2103.15624)), AI-Descartes ([Cornelio et al. 2023](https://www.nature.com/articles/s41467-023-37236-y)), AI Hilbert ([Cory-Wright et al. 2024](https://www.nature.com/articles/s41467-024-50074-w)), multi-view SR ([Russeil et al. 2024](https://arxiv.org/abs/2402.04298)) | Force formulas to agree with prior knowledge or with several datasets | Constrain the *form*, not the *identification*; still target $E[y \mid X]$ |

### 3.2 Literatures added after review (2026-09-30), and what we do about each

| Literature | What it does | Why it matters here | What we do |
|---|---|---|---|
| **Sparse / high-dimensional IV:** STIV ([Gautier & Rose](https://arxiv.org/abs/1105.2454)), penalized FGMM ([Fan & Liao 2014](https://doi.org/10.1214/13-AOS1202)), two-stage regularization ([Lin, Feng & Li 2015](https://doi.org/10.1080/01621459.2014.908125)), Lasso-GMM ([Caner 2009](https://doi.org/10.1017/S0266466608090099)) | Selects a sparse subset of many regressors under endogeneity | This is "SINDy with instruments" in all but name. If the law is linear in its parameters over a known library ($a + b\log x$), it already solves the problem | Main competitor for such laws. Add a **library + sparse IV** baseline (§8.1). Include laws outside any finite library ($x^{\theta}$, kink at unknown $c$, saturation): the contribution rests on these. Report honestly where the library wins |
| **NPIV, then symbolic distillation** (the pattern of [Cranmer et al. 2020](https://arxiv.org/abs/2006.11287), applied to an NPIV fit) | Fit $\hat f$ by sieve IV, KIV or DeepIV; run plain SR on $(X, \hat f(X))$ | The obvious two-step alternative built from existing tools | Main baseline. Hypothesis: one-step wins when the NPIV fit is unstable (weak instruments, small $n$, extrapolation). If it does not, reposition the paper around distillation plus the selection theory of §7 |
| **Model and moment selection in GMM:** [Andrews 1999](https://doi.org/10.1111/1468-0262.00036); [Andrews & Lu 2001](https://doi.org/10.1016/S0304-4076(00)00077-4); [Hong, Preston & Shum 2003](https://doi.org/10.1017/S0266466603196028) | Consistent, BIC-type criteria for choosing among moment-condition models | Gives a principled complexity penalty in place of an ad hoc $\lambda \cdot C(f)$ | Select from the Pareto front with MMSC (§6.3). Theorem 1 (§7) extends Andrews–Lu to formula classes |
| **Conditional vs. unconditional moments:** [Domínguez & Lobato 2004](https://doi.org/10.1111/j.1468-0262.2004.00545.x) | Shows that finitely many unconditional moments can lose the identification that $E[u \mid Z] = 0$ provides | Explains the finite-$K$ problem of criterion (b) | Let $K$ grow with $n$ or use kernel MMR (§6.2); report sensitivity to $K$ |
| **Parametric specification test under IV:** [Horowitz 2006](https://doi.org/10.1111/j.1468-0262.2006.00670.x) | Tests a given parametric form against the nonparametric alternative | The natural check of a discovered formula | Run on the held-out split for the selected formula (§6.4) |
| **Identification theory:** completeness is not testable ([Canay, Santos & Shaikh 2013](https://doi.org/10.3982/ECTA10851)); discrete instruments and shape restrictions ([Freyberger & Horowitz 2015](https://doi.org/10.1016/j.jeconom.2015.06.020)) | Limits of what data can say about identification in NPIV | Frames what "identification within the formula class" can claim | State restricted identification as an assumption (§5); design D4 with discrete instruments; conjecture in §7 |
| **Shape-restricted NPIV:** [Chetverikov & Wilhelm 2017](https://doi.org/10.3982/ECTA13639); [Blundell, Horowitz & Parey 2012](https://doi.org/10.3982/QE91) | Regularizes NPIV with monotonicity or Slutsky restrictions instead of a formula class | An alternative way to tame ill-posedness | Cite as the competing regularization; their gasoline estimates are the benchmark in §8.3 |
| **Misspecified GMM:** [Hall & Inoue 2003](https://doi.org/10.1016/S0304-4076(03)00089-7) | Pseudo-true values under misspecification depend on the moments and the weight matrix | On real data the "best" formula depends on the instrument basis and $W$ | Report stability across bases and weights (§6.5) |
| **Weak identification:** [Bound, Jaeger & Baker 1995](https://doi.org/10.1080/01621459.1995.10476536); [Stock & Wright 2000](https://doi.org/10.1111/1468-0262.00151); [Andrews & Cheng 2012](https://doi.org/10.3982/ECTA9456) | Weak instruments; robust inference; parameters that are unidentified in over-parameterized models | Angrist–Krueger instruments are weak; nested formulas (e.g., $f_0 + a\,g(bx)$ with $a = 0$) leave $b$ unidentified | Demote Angrist–Krueger to a stress test (§8.3); weak-ID-robust confidence sets (§6.4); Andrews–Cheng tools in Theorem 1 |
| **Control functions:** [Newey, Powell & Vella 1999](https://doi.org/10.1111/1468-0262.00037) | Triangular models with a control variable | Exact assumptions behind variant (a); neither weaker nor stronger than the IV condition | Design D2 where the control function fails but IV holds (§8.1) |
| **Sieve theory:** [Ai & Chen 2003](https://doi.org/10.1111/1468-0262.00470); [Chen 2007](https://doi.org/10.1016/S1573-4412(07)06076-X); [Chen & Pouzo 2012](https://doi.org/10.3982/ecta7888) | Consistency and rates for conditional-moment models with unknown functions | Tools for the misspecified case | Route for Theorem 3 (§7) |
| **Post-selection inference:** [Leeb & Pötscher 2005](https://doi.org/10.1017/S0266466605050036) | Shows that inference after data-driven model selection is not uniformly valid | Our estimator selects a formula | Sample splitting (§6.4); no uniform claims |

## 4. Novelty check log

| Check | Coverage | Result |
|---|---|---|
| OpenAlex: papers citing 7 core SR works (Schmidt–Lipson, AI Feynman, SINDy, DSR ×2, SRBench, 2024 review), filtered for IV / endogeneity / confounding / econometric | 7,696 papers | Nothing that enforces instruments or moment conditions |
| OpenAlex: papers citing core IV-estimation works (Newey–Powell, DeepIV, KIV, DeepGMM, AGMM, minimax CM, DFIV), filtered for symbolic / equation discovery / closed-form / genetic programming | 1,042 papers | Only black-box or kernel estimators |
| arXiv API: 14 query combinations | All of arXiv | 0 relevant |
| GitHub repository search | Public repositories | 0 results |
| Web search | General web | Nothing |
| Google Scholar (2026-09-27): `"symbolic regression" "instrumental variables"` (2 pages), `"symbolic regression" endogeneity`, `"symbolic regression" confounding`, `"symbolic regression" "method of moments"`, `"genetic programming" "instrumental variable"`, `"equation discovery" endogeneity OR "instrumental variable"` | Top 10–20 results each | No SR method with IV/GMM fitness. New neighbours: Kuang & Lin 2025, INSITE 2024, SRIT (see §3.1) |
| Full reading (2026-09-27): SRIT (Yan et al.) and Kuang & Lin 2026 | Complete texts | Neither overlaps; see §3.1 |
| Review (2026-09-30): econometrics literatures not covered by the searches above | High-dimensional IV, GMM model selection, NPIV testing and identification, symbolic distillation | No free-form formula search; library-based sparse IV and NPIV → distillation become the main baselines (§3.2) |
| Web search (2026-09-30): `symbolic regression instrumental variables endogeneity moment conditions 2026`; `SINDy instrumental variable sparse regression endogeneity library` | General web | Nothing new |

**Blind spots:** Semantic Scholar was rate-limited; OpenAlex undercounts citations to ML conference papers; very recent preprints may not be indexed yet; the searches used SR vocabulary, so work phrased as "sparse IV over a dictionary" was found only by the review.

**Refined gap.** Neighbouring work covers these pieces separately, never together:

| Piece | Covered by | Missing |
|---|---|---|
| IV correction of coefficients | Kuang & Lin 2026; Zeiringer et al. 2026 | Only measurement noise, fixed library, no formula search |
| Sparse term selection under endogeneity | Gautier & Rose; Fan & Liao 2014; Lin, Feng & Li 2015; Caner 2009 | Law must be linear in its parameters over a library fixed in advance |
| Causal constraints inside SR | SRIT | Variable selection only; assumes no unobserved confounders |
| Endogeneity-robust function estimation | NPIV / DeepIV / KIV / DeepGMM | No explicit formula |
| Formula from an NPIV fit | NPIV + symbolic distillation | Two steps; inherits NPIV instability; no selection theory |

**Target:** a **search over free-form formulas scored by instrument moment conditions** $E[y - f(X) \mid Z] = 0$, for **structural endogeneity** (unobserved confounding, simultaneity, choice) with **external instruments**, with a **consistent selection rule** and a finite-sample account of when recovery succeeds. This is exactly the setting that SRIT's authors leave open ("causal insufficiency"). The contribution must show gains over (i) library-based sparse IV on laws that are nonlinear in their parameters and (ii) NPIV → distillation, in finite samples and under weak instruments.

## 5. Model and identification

- **Model:** $y = f_0(X) + u$ with $E[u \mid Z] = 0$; the target is $f_0$. The error is **additive**. Non-separable models (random coefficients, e.g. $y = w \cdot h$ with heterogeneous $w$) violate this and are out of scope for v1; IV quantile regression ([Chernozhukov & Hansen 2005](https://doi.org/10.1111/j.1468-0262.2005.00570.x)) is the route to an extension.
- **Plain SR is biased:** at best it is consistent for $E[y \mid X] = f_0(X) + E[u \mid X]$. In design D1 (§8.1), $E[u \mid X] = \frac{\rho}{1+\pi^2}\log X$: for the log law the conditional mean has the right form with a biased coefficient; for every other law it has an extra $\log X$ term. Whether plain SR shows that term depends on its size relative to $f_0$. At the D1 defaults ($\pi = 1$, $\rho = 0.8$) it is $0.4\log X$, small next to $2x^{0.7}$, and in a smoke run plain PySR returned the right power form with biased constants (§11, Phase 2).
- **Identification within the class.** Let $\mathcal F_L$ be the formula class (§6.1). We need only **restricted identification**:

$$f \in \mathcal F_L,\quad E[f(X) - f_0(X) \mid Z] = 0 \text{ a.s.} \;\Rightarrow\; f = f_0.$$

  Completeness of $X$ given $Z$ ([D'Haultfœuille 2011](https://doi.org/10.1017/s0266466610000368)) is sufficient but not necessary. The restricted condition can hold with discrete instruments, where full nonparametric identification fails ([Freyberger & Horowitz 2015](https://doi.org/10.1016/j.jeconom.2015.06.020)). Completeness is not testable in general ([Canay, Santos & Shaikh 2013](https://doi.org/10.3982/ECTA10851)), so we treat restricted identification as an assumption and measure how close it is to failing through the separation constant $\delta_L$ (§7).

## 6. Method

### 6.1 Formula class

- **Operators:** start with $\{+, -, \times, \div, \text{pow}, \log, \exp, \max\}$; add $\sin$ and $\cos$ only for laws that need them.
- **Size:** at most $L$ nodes.
- **Bounded constants:** $\lvert\theta_j\rvert \le C$. This is required, not cosmetic. Without it, terms like $a\sin(bx)$ with large $b$ can lower the moment criterion by fitting noise in directions the instruments barely see, and the theory (§7) needs a compact class.
- **Nesting constraints:** no $\exp(\exp(\cdot))$, no $\log(\log(\cdot))$, to keep formulas smooth and readable.

### 6.2 Criteria

Residual $r_i = y_i - f(X_i)$. Each criterion is minimized over formulas and their constants.

| Variant | Criterion | Assumptions and notes |
|---|---|---|
| **(a) Control function** | SR with MSE on $y$, template $f(X) + g(\hat v)$, $\hat v$ = first-stage residual | Needs a first stage $X = h(Z, v)$ invertible in $v$ with $E[u \mid v, Z] = E[u \mid v]$ ([Newey, Powell & Vella 1999](https://doi.org/10.1111/1468-0262.00037)), which is neither weaker nor stronger than $E[u \mid Z] = 0$. Fast and a strong baseline when it holds; design D2 breaks it |
| **(b) GMM with sieve instruments** *(start here)* | $Q_n(f) = \hat g(f)^\top W \hat g(f)$, $\ \hat g(f) = \frac{1}{n}\sum_i b_K(Z_i)\, r_i$ | With 2SLS weights $W = (B^\top B/n)^{-1}$, $Q_n(f) = \frac{1}{n}\lVert A^\top r\rVert^2$, where $A$ is an orthonormal basis of the columns of $B$ (thin QR, computed once): $O(nK)$ per evaluation. **$K$ must be much larger than the number of constants**, otherwise a formula with $K$ or more constants can make the criterion exactly zero. A fixed set of unconditional moments can also lose identification ([Domínguez & Lobato 2004](https://doi.org/10.1111/j.1468-0262.2004.00545.x)), so $K$ grows with $n$. Optional second step: efficient $W$ from first-step residuals |
| **(c) Kernel MMR** | $Q_n(f) = \frac{1}{n^2}\, r^\top K_Z\, r$ | With an integrally strictly positive definite kernel, $Q = 0$ iff $E[r \mid Z] = 0$: all conditional moments at once ([Zhang et al. 2020](https://arxiv.org/abs/2010.07684)). Exact evaluation is $O(n^2)$, so use a Nyström or random-feature factor $K_Z \approx \Phi\Phi^\top$: then $Q_n = \frac{1}{n^2}\lVert \Phi^\top r\rVert^2$, **the same code path as (b)** |

(b) and (c) share one implementation: precompute an $n \times m$ matrix $A$ from $Z$ and score $\lVert A^\top r\rVert^2$.

### 6.3 Model selection

PySR returns a Pareto front (the best criterion at each complexity). Select from it with a consistent GMM model-selection criterion rather than an ad hoc $\lambda \cdot C(f)$:

- Refit the constants of each front member by efficient GMM and compute $\mathrm{MMSC}_n(s) = J_n(s) - (K - p_s)\ln n$ ([Andrews & Lu 2001](https://doi.org/10.1016/S0304-4076(00)00077-4)), where $J_n$ is Hansen's statistic and $p_s$ is the **number of free constants**, not the node count (nodes only break ties). With $K$ fixed across candidates this is $J_n(s) + p_s \ln n$ up to a constant.
- For MMR: $n\,Q_n(s) + c\, p_s \ln n$, with $c$ calibrated by simulation.
- Cross-check: the moment criterion on held-out data (not held-out MSE, which favours $E[y \mid X]$).

### 6.4 Inference after selection

Selection and inference use different data:

1. Split the sample: part A for search and selection, part B for everything reported.
2. On B: refit the selected formula's constants by efficient GMM; standard errors; Hansen $J$ test; weak-identification-robust (Anderson–Rubin type, [Stock & Wright 2000](https://doi.org/10.1111/1468-0262.00151)) confidence sets for the constants; [Horowitz (2006)](https://doi.org/10.1111/j.1468-0262.2006.00670.x) test of the selected formula against the nonparametric alternative.
3. This is valid conditional on the selected formula. Uniformly valid inference after selection without splitting is not claimed ([Leeb & Pötscher 2005](https://doi.org/10.1017/S0266466605050036); [Berk et al. 2013](https://doi.org/10.1214/12-aos1077)).

### 6.5 Interpretation on real data

Real laws are rarely exactly in $\mathcal F_L$. Under misspecification, the GMM pseudo-true formula depends on the instrument basis and on $W$ ([Hall & Inoue 2003](https://doi.org/10.1016/S0304-4076(03)00089-7)); unlike least squares, there is no single natural projection. Report the selected formula across several bases (polynomial, spline, kernel) and weights, and treat stability as part of the evidence. As an empirical counterpart of $\delta_L$, report the criterion gap between the selected formula and the runner-up.

### 6.6 Implementation (PySR)

- **PySR** ([Cranmer 2023](https://arxiv.org/abs/2305.01582)): custom criterion via **`loss_function`**, a Julia function `(tree, dataset, options) -> loss` ([docs](https://pysr.ai/api/)). `full_objective` is the deprecated name (see `pysr/deprecated.py`). No new search engine is needed.
- Pass $A$ into Julia as a global (via `juliacall`) before `fit`; use multithreading, not multiprocessing, so every worker sees it.
- `batching=False`: the projection needs all rows in their original order.
- The dataset holds only $X$; $Z$ enters only through $A$, so formulas cannot use the instruments.
- PySR's constant optimizer minimizes the same custom loss, so constants are fitted by the moment criterion with no extra code.
- Enforce $\lvert\theta_j\rvert \le C$ inside the loss (return a large loss otherwise); use `nested_constraints` for §6.1.
- Control function (a): `TemplateExpressionSpec(expressions=["f", "g"], variable_names=["x", "v"], combine="f(x) + g(v)")`.
- **Optional RL version:** Deep Symbolic Regression ([Petersen et al. 2021](https://arxiv.org/abs/1912.04871)), with reward $= -$ criterion.

## 7. Theory plan

**Setting.** $\mathcal S_L$ is the finite set of expression trees with at most $L$ nodes over the operator set. Tree $s$ has $p_s$ constants in $\Theta_s = [-C, C]^{p_s}$, and $\mathcal F_L = \{f_s(\cdot\,;\theta)\}$. The estimator is

$$(\hat s, \hat\theta) \in \arg\min_{s,\,\theta}\; Q_n\big(f_s(\cdot\,;\theta)\big) + \mathrm{pen}_n(s), \qquad \mathrm{pen}_n(s) \propto p_s \ln n / n.$$

Let $T h = E[h(X) \mid Z]$.

**Assumptions.** (A1) $E[u \mid Z] = 0$ with finite second moments. (A2) Restricted identification (§5). (A3) Each $f_s(x;\theta)$ is continuous in $\theta$ with a square-integrable envelope (protected operators, bounded support). (A4) For (c), a bounded ISPD kernel; for (b), $K_n \to \infty$, $K_n/n \to 0$, with a basis whose span is dense.

| Result | Target statement | Tools | Feasibility |
|---|---|---|---|
| **Theorem 1: consistency and selection (well-specified)** | If $f_0 \in \mathcal F_L$ with $L$ fixed, $\mathrm{pen}_n \to 0$ and $n\,\mathrm{pen}_n \to \infty$: (i) $\lVert \hat f - f_0\rVert_{L^2} \to_p 0$; (ii) with probability $\to 1$, the selected tree represents $f_0$ with the fewest constants; (iii) on the split sample, $\sqrt n(\hat\theta - \theta_0)$ is asymptotically normal under the usual rank condition (pointwise, not uniform) | Extremum-estimator consistency ([Newey & McFadden 1994](https://doi.org/10.1016/S1573-4412(05)80005-4)); consistent GMM model selection (Andrews & Lu 2001); degenerate $U$-statistics for MMR at the truth; [Andrews & Cheng (2012)](https://doi.org/10.3982/ECTA9456) for over-parameterized trees whose extra constants are unidentified | **High.** Mostly known tools; the work is careful bookkeeping (trees that represent the same function, nested trees) |
| **Theorem 2: finite-sample selection bound** (the "short formulas regularize" claim, made precise) | Separation $\delta_L = \min_{s:\, f_0 \notin f_s(\cdot;\Theta_s)}\ \min_{\theta}\ \lVert T(f_s(\cdot\,;\theta) - f_0)\rVert^2$. By (A2) and compactness, $\delta_L > 0$ even though $T^{-1}$ is unbounded. Target form: $P(\text{wrong tree}) \le \exp\{\log\lvert\mathcal S_L\rvert + p_{\max}\ln n - c\,n\,\delta_L^2\}$ | Uniform concentration over a finite union of Lipschitz-parameterized classes (bounded kernel or envelope); covering numbers | **Medium-high.** The main new result. It predicts that recovery tracks $n\,\delta_L^2$, and that $\delta_L$ shrinks with weaker instruments, larger $C$ and larger $L$. These predictions are testable in the Monte Carlo, where $\delta_L$ can be computed |
| **Theorem 3: misspecified, growing $L_n$** | $\bigcup_L \mathcal F_L$ as a nonlinear sieve in penalized sieve minimum distance (Chen & Pouzo 2012; Chen 2007): consistency of $\hat f$ when $f_0 \notin \mathcal F_L$ for every fixed $L$ | Nested classes ($\mathcal F_L \subseteq \mathcal F_{L+1}$); lower-semicompact penalty from bounded constants; approximation inherited from the polynomial sub-sieve contained in $\mathcal F_L$ | **Consistency: medium. Rates: low.** The ill-posedness measure of a nonlinear, non-convex sieve is not standard; possibly a separate paper |
| Proposition (conjecture): discrete instruments | With $Z$ taking $J$ values, restricted identification holds generically in the distribution of $X \mid Z$ when $J > p_{\max}$ | Transversality for analytic families | Speculative; only after Theorems 1–2 |

**Not claimed:**

- Guarantees for the genetic-programming search itself. The theorems concern the global minimizer, or any near-minimizer within $o_p(\mathrm{pen}_n)$. The Monte Carlo separates **search failures** (the true formula has a lower penalized criterion than the one found) from **statistical failures** (the estimator itself prefers a wrong formula).
- Uniformly valid inference after selection without sample splitting.

## 8. Experiments

### 8.1 Monte Carlo

The econometrician sees only $(y, X, Z)$.

**Designs**

| Design | Data-generating process | Purpose |
|---|---|---|
| D1 Confounding | $Z, v, \varepsilon \sim N(0,1)$ independent; $X = \exp(\pi Z + v)$; $u = \rho v + \sigma\varepsilon$ | Baseline. $X > 0$, so log and power laws are defined. $E[y \mid X]$ has an extra $\frac{\rho}{1+\pi^2}\log X$ term (§5). Control-function assumptions hold with the first stage on $\log X$ |
| D2 Heteroskedastic first stage | $X = \exp(\pi Z + \sigma(Z)\, v)$, $\sigma(Z) = e^{\gamma Z}$ | IV condition holds; control function fails, because $E[u \mid \hat v, Z] = \rho\,\hat v/\sigma(Z)$ depends on $Z$ |
| D3 Simultaneity | $y = f_0(X) + u$ with $f_0$ increasing (a supply curve), and $y = -\kappa\log X + \gamma Z + e$ (demand, shifted by $Z$); solve for the equilibrium $X$ numerically | Endogeneity from equilibrium, not from an omitted variable. All laws of the table below except the two-regressor one are increasing |
| D4 Discrete instrument | $Z$ uniform on $J$ points | Restricted identification with small $J$ (tests the conjecture in §7) |
| D5 Weak instrument | D1 with $\pi \to 0$ | Degradation ([Staiger & Stock 1997](https://doi.org/10.2307/2171753)); the method should report weak identification rather than a confident formula |

**Laws**

| Law | Formula | In a finite library? |
|---|---|---|
| Log | $a + b\log x$ | Yes: library IV should succeed |
| Power | $a\,x^{\theta}$, $\theta = 0.7$ | No: nonlinear in $\theta$ |
| Kink | $a x + b\max(x - c, 0)$ | No: unknown $c$ |
| Saturation | $a x/(b + x)$ | No |
| Two regressors | $A\,x_1^{\alpha} x_2^{\beta}$, two instruments | No |

**Vary:** instrument strength $\pi$; $n \in \{10^3, 10^4, 10^5\}$; endogeneity $\rho$; noise; $J$ (D4); constant bound $C$; operator set; $K$ for (b) and bandwidth for (c).

**Metrics**

- **Form recovery** (primary): the found formula reproduces $f_0$ exactly once its constants are refit to the noise-free $f_0$, and has no more constants than $f_0$. This is robust to rearrangement ($\log(c\,x^k)$ vs. $a + b\log x$) and to noise in the estimated constants. SRBench's SymPy check (difference or ratio simplifies to a constant) is reported alongside, but estimated constants rarely match exactly.
- $\lVert \hat f - f_0\rVert_{L^2}$ in sample and **outside the training support** (extrapolation), and the bias of the constants when the form is right. Form recovery alone misses the case where plain SR finds the right form with biased constants.
- Implied elasticities $x f'(x)/f(x)$ at quantiles of $X$.
- Search failures vs. statistical failures (§7).
- Recovery against the computed $\delta_L$ (checks Theorem 2).
- Runtime.

**Baselines**

| Baseline | Why |
|---|---|
| Plain PySR | Shows the bias |
| SRIT ([code](https://github.com/Super-SUM-Plus/SRIT)) | Closest "causal SR"; assumes no unobserved confounders |
| Oracle 2SLS with the true form | Upper bound |
| 2SLS with a wrong form | Cost of guessing the form |
| Sieve 2SLS (B-splines), KIV, DeepIV or DFIV | Nonparametric IV; no formula |
| **NPIV → PySR distillation** | Main two-step competitor (§3.2) |
| **Library + sparse IV** (PySR-style term library; Lasso on instrument-projected data; STIV if feasible) | Main competitor for laws linear in parameters (§3.2) |
| Control-function SR, variant (a) | Cheap alternative; should win on D1 and lose on D2 |

**Expected results** (stated so that they can fail):

- Plain SR returns a wrong formula or the right form with biased constants, depending on how large the endogeneity term is relative to $f_0$.
- Library IV matches symbolic IV on the log law and fails on power, kink and saturation.
- One-step symbolic IV beats NPIV → distillation when the NPIV fit is unstable (weak instruments, small $n$, extrapolation). If it does not, the paper is repositioned (§3.2).
- Recovery tracks $n\,\delta_L^2$.
- Degradation under weak instruments is documented as part of the contribution.

### 8.2 Simulated economic environments

- **Supply and demand with endogenous prices** (D3): in the simulation the target is the supply curve, identified by a demand shifter; recovering a demand curve with cost-shifter instruments is the mirror image and needs decreasing laws.
- **Labour supply:** hours $= f_0(w) + u$ with a backward-bending $f_0$. The wage is endogenous because unobserved taste for work is correlated with productivity; the instrument is an exogenous wage shifter (e.g., a simulated tax reform).
- *Dropped:* earnings $=$ wage $\times$ hours with heterogeneous wages. It is not additive: $u = (w - \bar w)\,h$, and $E[u \mid Z] \neq 0$ because hours respond to $w$. In logs it becomes additive, but then the "law" is an identity with coefficient 1. The motivation that earnings risk partly reflects hours choices ([Halvorsen et al. 2024](https://academic.oup.com/jeea/article-abstract/22/2/617/7251473); [Kaplan & Violante 2010](https://www.aeaweb.org/articles?id=10.1257%2Fmac.2.4.53)) belongs to the non-separable extension (§5).

### 8.3 Real applications with known answers

| Application | Data | Instrument | Known answer | Role |
|---|---|---|---|---|
| **Engel curves** ([Blundell, Chen & Kristensen 2007](https://doi.org/10.1111/j.1468-0262.2007.00808.x)) | UK Family Expenditure Survey (UK Data Service; free registration) | Household head's earnings, for log total expenditure | Budget shares linear in log expenditure (Working–Leser) for food; quadratic in log expenditure for some goods ([Banks, Blundell & Lewbel 1997](https://doi.org/10.1162/003465397557015)) | **Primary:** continuous instrument and a formula-shaped answer |
| **Gasoline demand** ([Blundell, Horowitz & Parey 2012](https://doi.org/10.3982/QE91); earlier nonparametric estimates in [Hausman & Newey 1995](https://doi.org/10.2307/2171777)) | US National Household Travel Survey 2001 (public) | Distance from the Gulf of Mexico (price shifter) | Price responsiveness that varies with price and income | **Secondary:** comparison with shape-restricted NPIV |
| Returns to schooling ([Angrist & Krueger 1991](https://doi.org/10.2307/2937954)) | Public | Quarter of birth | None usable for functional form | **Stress test only.** The instruments are weak ([Bound, Jaeger & Baker 1995](https://doi.org/10.1080/01621459.1995.10476536)), discrete, and shift schooling only near the compulsory-schooling margin, so they cannot identify a functional form over the whole range. Success means the method reports weak identification instead of a confident formula |

## 9. Deliverables and venues

- **Open-source package:** symbolic IV on top of PySR (criteria (a)–(c), MMSC selection, split-sample inference), plus the Monte Carlo benchmark suite (designs D1–D5 × laws).
- **Paper:** an ML venue (NeurIPS / ICML causality tracks) needs §8 plus Theorems 1–2. An econometrics journal (*Journal of Econometrics*, *The Econometrics Journal*) needs full proofs of Theorems 1–2, and ideally the consistency part of Theorem 3.
- **Data:** no confidential data. The Engel-curve application needs a free UK Data Service registration.

## 10. Risks

| Risk | Mitigation |
|---|---|
| Weak instruments; identification failure (completeness not holding) | Designs D4–D5; weak-ID-robust confidence sets; report the criterion gap to the runner-up; Angrist–Krueger stress test |
| Oscillatory formulas exploit ill-posedness | Bounded constants, restricted operators, nesting constraints (§6.1) |
| Criterion ties at zero with finite $K$ | $K$ much larger than the number of constants and growing with $n$, or MMR (§6.2) |
| Noisier, non-convex search (the moment criterion is flatter than MSE) | Several restarts; seed with the plain-SR front; report search failures separately (§7) |
| Library IV or NPIV → distillation match the method | Laws outside any finite library; if the one-step method does not win, reposition (§3.2) |
| Misspecification on real data | Stability across instrument bases and weights (§6.5) |
| Additive-error assumption fails | Out of scope for v1; IV quantile extension (§5) |
| Inference after the search has selected the formula ([Berk et al. 2013](https://doi.org/10.1214/12-aos1077); [Belloni et al. 2012](https://doi.org/10.3982/ecta9626); [Chernozhukov et al. 2018](https://doi.org/10.1111/ectj.12097)) | Sample splitting (§6.4) |
| Compute: exact MMR is $O(n^2)$ per evaluation | Low-rank factor (§6.2) |

## 11. Checkpoints

### Phase 0: literature and novelty
- [x] OpenAlex, arXiv, GitHub and web searches (2026-09-26)
- [x] Google Scholar queries (2026-09-27)
- [x] Read SRIT in full: independence-test pruning of inputs; assumes causal sufficiency; no instruments
- [x] Read Kuang & Lin in full: IV for coefficients only (fixed library, measurement noise); no model selection
- [x] Review: add high-dimensional IV, GMM model selection, NPIV testing and identification, distillation (2026-09-30, §3.2)
- [ ] Read Gautier & Rose (STIV) and Fan & Liao (2014); choose the sparse-IV estimator for the library baseline
- [ ] Read Andrews & Lu (2001) and Domínguez & Lobato (2004); fix the selection criterion and the rule for $K$
- [ ] Read Horowitz (2006); decide whether to implement the test or only cite it
- [ ] New searches: "sparse instrumental variables" with "dictionary", "library" or "nonlinear"; "SINDy" with "instrumental" or "endogeneity"; "symbolic distillation" with "instrumental"; retry Semantic Scholar
- [ ] Verify the 2026 references (Kuang & Lin; Zeiringer et al.; Li et al.)
- [ ] Optional: ask one nonparametric-IV researcher whether they know of related work

### Phase 1: infrastructure (done 2026-09-30; §12)
- [x] Repository skeleton: `src/symiv/{dgp, criteria, baselines}`, `experiments/`, `tests/`
- [x] DGPs D1–D5 with seeds, returning $(y, X, Z)$, the true $f_0$, and the hidden errors for checks
- [x] Criterion matrix $A$: B-spline (or polynomial) basis, orthonormalized by SVD so discrete instruments drop collinear columns, for (b); Nyström features for (c). $K$ defaults to about $n^{1/3}$
- [x] Julia `loss_function` computing $\lVert A^\top r\rVert^2/n$, with a soft penalty beyond the constant bound $C$ (the hard bound is enforced in the GMM refit). Verified to match the Python criterion to $10^{-6}$ on every Pareto-front formula
- [x] Unit test: the criterion is over 20× larger at $E[y \mid X]$ (plain SR's target) than at $f_0$, for both criteria; $J$ at the truth averages $K$ over 200 draws
- [x] MMSC selector over the Pareto front (two-step efficient GMM refit, $J_n - (K - p_s)\ln n$); picks the true form over both a wrong form and an over-parameterized form that contains it
- [x] Recovery checks: numerical form recovery (primary) and SRBench's SymPy check
- [x] Search-failure vs. statistical-failure diagnostic (tested on a search failure and on an unidentified design with $\pi = 0$)
- [x] End-to-end smoke run (`experiments/smoke_pysr.py`, D1, power law, $n = 2000$): symbolic IV selected $2.02\,x^{0.693}$ (outcome: success); relative function error 0.014 vs. 0.091 for plain PySR

### Phase 2: first Monte Carlo (one design, two laws)
- [ ] D1 with the power law $x^{0.7}$ and the log law
- [ ] Plain PySR's bias: at the D1 defaults the smoke run gave the right power form with biased constants ($2.09\,x^{0.709}$), not a spurious $\log X$ term. Report function error and constant bias, not only form recovery; add a stronger-endogeneity setting (larger $\rho$, smaller $\pi$) where the conditional mean departs visibly from $f_0$
- [ ] Select plain SR's formula with a stated rule (e.g. BIC on MSE), not PySR's default score, so both methods use comparable selection
- [ ] Symbolic IV (b) recovers $f_0$; recovery rate over 50–100 seeds
- [ ] Track the MMSC gap between the selected formula and the runner-up: in one smoke run a contrived three-constant formula came within 0.7 of the true form (a first sign of the flat criterion in §10)
- [ ] Sensitivity to $C$ and $K$

### Phase 3: baselines
- [ ] Oracle 2SLS and wrong-form 2SLS (both are `symiv.gmm.fit_gmm` on a fixed form; needs a wrapper and reporting)
- [ ] Sieve 2SLS, KIV, DeepIV or DFIV
- [ ] NPIV → PySR distillation
- [ ] Library + sparse IV
- [ ] Control-function SR with `TemplateExpressionSpec`
- [ ] SRIT

### Phase 4: full grid
- [ ] All laws × D1–D5; vary $\pi$, $n$, $\rho$, noise, $J$, $C$, $K$
- [ ] Criterion (c) vs. (b)
- [ ] Compute $\delta_L$ numerically per design; plot recovery against $n\,\delta_L^2$
- [ ] Write up the first results

### Phase 5: theory
- [ ] Formal setup and assumptions (A1)–(A4); treatment of trees that represent the same function
- [ ] Theorem 1 (i): consistency
- [ ] Theorem 1 (ii)–(iii): selection consistency; split-sample asymptotic normality
- [ ] Theorem 2: finite-sample selection bound in terms of $\delta_L$
- [ ] Theorem 3 (stretch): check the Chen–Pouzo conditions for bounded-constant formula classes
- [ ] Discrete-instrument proposition (only if time allows)

### Phase 6: applications
- [ ] Simulated demand and labour-supply environments (§8.2)
- [ ] Engel curves: data access; replicate the BCK 2007 NPIV curve; run symbolic IV; compare with Working–Leser and quadratic-in-log forms
- [ ] Gasoline demand: data access; confirm the instrument definition in BHP 2012; replicate their setup; compare
- [ ] Angrist–Krueger stress test

### Phase 7: package and paper
- [ ] Package API and documentation; release the benchmark suite
- [ ] Paper draft; choose the venue after Phase 4 and Theorem 2

## 12. Code

```
src/symiv/
  dgp/            laws and designs D1-D5 (§8.1)
  criteria/       instrument bases, Nystrom features, the criterion ||A'r||^2 / n (§6.2)
  gmm.py          two-step GMM refit with bounded constants; Hansen's J (§6.3)
  selection.py    MMSC selection over the Pareto front (§6.3)
  recovery.py     form recovery and SRBench's SymPy check (§8.1)
  diagnostics.py  success / search failure / statistical failure (§7)
  search.py       PySR wrappers; the loss is julia/moment_loss.jl (§6.6)
  baselines/      Phase 3
experiments/      smoke_pysr.py: one end-to-end run, plain PySR vs. symbolic IV
tests/            pytest; `pytest -m julia` runs the PySR tests
```

**Setup** (tested with Python 3.12, PySR 2.6.0, SymbolicRegression.jl 2.5.1, Julia 1.11.9, Windows 11):

```
python -m venv .venv
.venv\Scripts\activate            # Windows; elsewhere: source .venv/bin/activate
pip install -e ".[search,dev]"
python -c "import pysr"           # first run installs Julia and SymbolicRegression.jl (several minutes)
pytest                            # pure-Python tests, seconds
pytest -m julia                   # PySR integration, about a minute
python experiments/smoke_pysr.py --design D1 --law power --n 2000
```

If the Julia install fails with `GitError ... could not find repository at ...\.julia\registries\General`, the user-wide Julia registry is corrupt. Move that folder **outside** `registries/` (Julia reads every folder in it) and rerun; a fresh registry is downloaded.

**Usage:**

```python
from symiv import diagnose, gmm_criterion, select_mmsc, simulate
from symiv.search import fit_symbolic_iv, pareto_front

s = simulate("D1", "power", n=2000, seed=0)       # y, X, Z; s.law is the truth
crit = gmm_criterion(s.Z)                          # or mmr_criterion(s.Z)
model = fit_symbolic_iv(s.X, s.y, crit, niterations=40, maxsize=15)
exprs, complexities = pareto_front(model)
best = select_mmsc(exprs, s.X, s.y, crit, complexities=complexities).best
print(best.fitted_expr, diagnose(best, s.law, s.X, s.y, crit).outcome)
```

---

## References

**Nonparametric IV and conditional moments**
- Newey, W. & Powell, J. (2003). Instrumental variable estimation of nonparametric models. *Econometrica*. https://doi.org/10.1111/1468-0262.00459
- Hall, P. & Horowitz, J. (2005). Nonparametric methods for inference in the presence of instrumental variables. *Annals of Statistics*. https://doi.org/10.1214/009053605000000714
- Blundell, R., Chen, X. & Kristensen, D. (2007). Semi-nonparametric IV estimation of shape-invariant Engel curves. *Econometrica*. https://doi.org/10.1111/j.1468-0262.2007.00808.x
- Chen, X. & Pouzo, D. (2012). Estimation of nonparametric conditional moment models with possibly nonsmooth generalized residuals. *Econometrica*. https://doi.org/10.3982/ecta7888
- Ai, C. & Chen, X. (2003). Efficient estimation of models with conditional moment restrictions containing unknown functions. *Econometrica*. https://doi.org/10.1111/1468-0262.00470
- Chen, X. (2007). Large sample sieve estimation of semi-nonparametric models. *Handbook of Econometrics* 6B. https://doi.org/10.1016/S1573-4412(07)06076-X
- Domínguez, M. & Lobato, I. (2004). Consistent estimation of models defined by conditional moment restrictions. *Econometrica*. https://doi.org/10.1111/j.1468-0262.2004.00545.x
- Newey, W., Powell, J. & Vella, F. (1999). Nonparametric estimation of triangular simultaneous equations models. *Econometrica*. https://doi.org/10.1111/1468-0262.00037
- Horowitz, J. (2006). Testing a parametric model against a nonparametric alternative with identification through instrumental variables. *Econometrica*. https://doi.org/10.1111/j.1468-0262.2006.00670.x
- Chetverikov, D. & Wilhelm, D. (2017). Nonparametric instrumental variable estimation under monotonicity. *Econometrica*. https://doi.org/10.3982/ECTA13639
- Chernozhukov, V. & Hansen, C. (2005). An IV model of quantile treatment effects. *Econometrica*. https://doi.org/10.1111/j.1468-0262.2005.00570.x

**Identification and weak identification**
- D'Haultfœuille, X. (2011). On the completeness condition in nonparametric instrumental problems. *Econometric Theory*. https://doi.org/10.1017/s0266466610000368
- Canay, I., Santos, A. & Shaikh, A. (2013). On the testability of identification in some nonparametric models with endogeneity. *Econometrica*. https://doi.org/10.3982/ECTA10851
- Freyberger, J. & Horowitz, J. (2015). Identification and shape restrictions in nonparametric instrumental variables estimation. *Journal of Econometrics*. https://doi.org/10.1016/j.jeconom.2015.06.020
- Staiger, D. & Stock, J. (1997). Instrumental variables regression with weak instruments. *Econometrica*. https://doi.org/10.2307/2171753
- Bound, J., Jaeger, D. & Baker, R. (1995). Problems with instrumental variables estimation when the correlation between the instruments and the endogenous explanatory variable is weak. *JASA*. https://doi.org/10.1080/01621459.1995.10476536
- Stock, J. & Wright, J. (2000). GMM with weak identification. *Econometrica*. https://doi.org/10.1111/1468-0262.00151
- Andrews, D. W. K. & Cheng, X. (2012). Estimation and inference with weak, semi-strong, and strong identification. *Econometrica*. https://doi.org/10.3982/ECTA9456

**GMM: model selection, misspecification, extremum estimation**
- Newey, W. & McFadden, D. (1994). Large sample estimation and hypothesis testing. *Handbook of Econometrics* 4. https://doi.org/10.1016/S1573-4412(05)80005-4
- Andrews, D. W. K. (1999). Consistent moment selection procedures for generalized method of moments estimation. *Econometrica*. https://doi.org/10.1111/1468-0262.00036
- Andrews, D. W. K. & Lu, B. (2001). Consistent model and moment selection procedures for GMM estimation with application to dynamic panel data models. *Journal of Econometrics*. https://doi.org/10.1016/S0304-4076(00)00077-4
- Hong, H., Preston, B. & Shum, M. (2003). Generalized empirical likelihood-based model selection criteria for moment condition models. *Econometric Theory*. https://doi.org/10.1017/S0266466603196028
- Hall, A. & Inoue, A. (2003). The large sample behaviour of the generalized method of moments estimator in misspecified models. *Journal of Econometrics*. https://doi.org/10.1016/S0304-4076(03)00089-7

**High-dimensional and sparse IV**
- Gautier, E. & Rose, C. High-dimensional instrumental variables regression and confidence sets. https://arxiv.org/abs/1105.2454
- Fan, J. & Liao, Y. (2014). Endogeneity in high dimensions. *Annals of Statistics*. https://doi.org/10.1214/13-AOS1202
- Lin, W., Feng, R. & Li, H. (2015). Regularization methods for high-dimensional instrumental variables regression with an application to genetical genomics. *JASA*. https://doi.org/10.1080/01621459.2014.908125
- Caner, M. (2009). Lasso-type GMM estimator. *Econometric Theory*. https://doi.org/10.1017/S0266466608090099

**ML for IV**
- Hartford, J. et al. (2017). Deep IV. *ICML*. https://proceedings.mlr.press/v70/hartford17a.html
- Lewis, G. & Syrgkanis, V. (2018). Adversarial generalized method of moments. https://arxiv.org/abs/1803.07164
- Singh, R., Sahani, M. & Gretton, A. (2019). Kernel instrumental variable regression. *NeurIPS*. https://arxiv.org/abs/1906.00232
- Bennett, A., Kallus, N. & Schnabel, T. (2019). Deep generalized method of moments for IV analysis. *NeurIPS*. https://arxiv.org/abs/1905.12495
- Dikkala, N. et al. (2020). Minimax estimation of conditional moment models. *NeurIPS*. https://arxiv.org/abs/2006.07201
- Zhang, R. et al. (2020). Instrumental variable regression via kernel maximum moment loss. https://arxiv.org/abs/2010.07684
- Xu, L. et al. (2021). Learning deep features in instrumental variable regression. *ICLR*. https://arxiv.org/abs/2010.07154

**Symbolic regression**
- Schmidt, M. & Lipson, H. (2009). Distilling free-form natural laws from experimental data. *Science*. https://doi.org/10.1126/science.1165893
- Brunton, S., Proctor, J. & Kutz, J. N. (2016). Sparse identification of nonlinear dynamical systems (SINDy). *PNAS*. https://doi.org/10.1073/pnas.1517384113
- Udrescu, S.-M. & Tegmark, M. (2020). AI Feynman. *Science Advances*. https://doi.org/10.1126/sciadv.aay2631
- Cranmer, M. et al. (2020). Discovering symbolic models from deep learning with inductive biases. *NeurIPS*. https://arxiv.org/abs/2006.11287
- Petersen, B. et al. (2021). Deep symbolic regression. *ICLR*. https://arxiv.org/abs/1912.04871
- La Cava, W. et al. (2021). Contemporary symbolic regression methods and their relative performance (SRBench). https://arxiv.org/abs/2107.14351
- Cranmer, M. (2023). Interpretable machine learning for science with PySR and SymbolicRegression.jl. https://arxiv.org/abs/2305.01582
- Kronberger, G. et al. (2022). Shape-constrained symbolic regression. *Evolutionary Computation*. https://arxiv.org/abs/2103.15624
- Cornelio, C. et al. (2023). AI-Descartes. *Nature Communications*. https://www.nature.com/articles/s41467-023-37236-y
- Cory-Wright, R. et al. (2024). AI Hilbert. *Nature Communications*. https://www.nature.com/articles/s41467-024-50074-w
- Russeil, E. et al. (2024). Multi-view symbolic regression. https://arxiv.org/abs/2402.04298
- Balla, J. et al. (2025). AI-assisted discovery of quantitative and formal models in social science. *Humanities and Social Sciences Communications*. https://doi.org/10.1057/s41599-025-04405-x
- Camps-Valls, G. et al. (2023). Discovering causal relations and equations from data. *Physics Reports*. https://doi.org/10.1016/j.physrep.2023.10.005

**Inference after selection**
- Leeb, H. & Pötscher, B. (2005). Model selection and inference: facts and fiction. *Econometric Theory*. https://doi.org/10.1017/S0266466605050036
- Berk, R. et al. (2013). Valid post-selection inference. *Annals of Statistics*. https://doi.org/10.1214/12-aos1077
- Belloni, A., Chen, D., Chernozhukov, V. & Hansen, C. (2012). Sparse models and methods for optimal instruments. *Econometrica*. https://doi.org/10.3982/ecta9626
- Chernozhukov, V. et al. (2018). Double/debiased machine learning. *Econometrics Journal*. https://doi.org/10.1111/ectj.12097

**Applications and test environments**
- Angrist, J. & Krueger, A. (1991). Does compulsory school attendance affect schooling and earnings? *QJE*. https://doi.org/10.2307/2937954
- Banks, J., Blundell, R. & Lewbel, A. (1997). Quadratic Engel curves and consumer demand. *Review of Economics and Statistics*. https://doi.org/10.1162/003465397557015
- Blundell, R., Horowitz, J. & Parey, M. (2012). Measuring the price responsiveness of gasoline demand: economic shape restrictions and nonparametric demand estimation. *Quantitative Economics*. https://doi.org/10.3982/QE91
- Hausman, J. & Newey, W. (1995). Nonparametric estimation of exact consumers surplus and deadweight loss. *Econometrica*. https://doi.org/10.2307/2171777
- Kaplan, G. & Violante, G. (2010). How much consumption insurance beyond self-insurance? *AEJ: Macroeconomics*. https://www.aeaweb.org/articles?id=10.1257%2Fmac.2.4.53
- Halvorsen, E., Holter, H., Ozkan, S. & Storesletten, K. (2024). Dissecting idiosyncratic earnings risk. *JEEA*. https://academic.oup.com/jeea/article-abstract/22/2/617/7251473

**Neighbouring IV, causal SR and system identification**
- Kuang, S. & Lin, X. (2026). Instrumental variables system identification with $L^p$ consistency. *Proceedings of Machine Learning Research*, 331. https://arxiv.org/abs/2511.09024
- Kacprzyk, K. et al. (2024). ODE discovery for longitudinal heterogeneous treatment effects inference. *ICLR*. https://arxiv.org/abs/2403.10766
- Yan, B., Yang, G., Wang, J. & Lu, D. Causally constrained symbolic regression for mining interpretable functions from observational data. SSRN 6879831. https://papers.ssrn.com/sol3/papers.cfm?abstract_id=6879831
- Zeiringer, T., Garnier, H. & Horn, M. (2026). Instrumental variable framework for nonlinear continuous-time system identification. *J. Franklin Institute*. https://doi.org/10.1016/j.jfranklin.2026.108619
- Li, R., Feng, Q. & Cui, Y. (2026). Causally guided symbolic regression for basin-scale water balance change. *J. Hydrology: Regional Studies*. https://doi.org/10.1016/j.ejrh.2026.103355
