# Symbolic IV: Discovering Structural Equations under Endogeneity

Symbolic regression that recovers the **structural** relation $f(X)$ rather than the conditional mean $E[y \mid X]$, by scoring the formula search with instrumental-variable moment conditions.

Results so far: §12 (Phase 2 Monte Carlo; Phase 3 baselines; Phase 4 full grid; Phase 5 simulations of the theory). Theory, with proofs and a review log: [THEORY.md](THEORY.md) (Phase 5). Code layout and setup: §13.

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
- **Nonparametric IV followed by symbolic distillation** (fit $\hat f$ with KIV or DeepIV, then run SR on $(X, \hat f(X))$) does produce a formula, but inherits the instability of the NPIV fit and has no selection theory. Phase 3 (§12.2) makes this precise:
  - with SR's own choice of formula, distillation rarely recovers the law;
  - with the formula chosen by our moment criterion on the original data, it recovers the law more often than the one-step search.

  Phase 4 (§12.3) goes further: even plain SR's own list of candidates, scored by the moment criterion, usually contains and selects the law. The missing piece is IV-based *selection* among formulas, and its theory.

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
| **NPIV, then symbolic distillation** (the pattern of [Cranmer et al. 2020](https://arxiv.org/abs/2006.11287), applied to an NPIV fit) | Fit $\hat f$ by sieve IV, KIV or DeepIV; run plain SR on $(X, \hat f(X))$ | The obvious two-step alternative built from existing tools | Main baseline. Hypothesis: one-step wins when the NPIV fit is unstable (weak instruments, small $n$, extrapolation). If it does not, reposition the paper around distillation plus the selection theory of §7. **Phase 3: it did not.** With PySR's own pick, distillation recovered the form in 2–52% of runs. Scored by MMSC on the original data, the same candidates recovered it in 74–100%, more often than the one-step search (paired $p < 0.001$). Repositioned accordingly (§4) |
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
| Web search (2026-10-01), the Phase 0 queries left open: `"symbolic regression" "instrumental variable(s)"`, `... endogeneity OR "unobserved confounders"`, `... "method of moments" OR GMM`; `SINDy "instrumental variables"`; `"sparse instrumental variables" dictionary OR library`; `"equation discovery" "instrumental variables" confounding` | General web | Nothing new. The 2026 references of §3.1 verified against their publishers |

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

**Revised after Phase 3 (§12.2).**
- **The core of the method is the selection rule.** It is MMSC, on the original data, over free-form candidate formulas, together with its theory (§7) and the failure diagnostics. The candidates can come from any generator: the one-step search, or PySR distilling an NPIV fit.
- **Distilling a sieve-2SLS fit gave better candidates than the one-step search.** Scored by the same rule, they recovered the true form in 74–100% of runs against 66–92%.
- **The selection rule is what beats the literature.** Distillation with PySR's own choice (the literature's version) recovered the form in 2–52% of runs; library IV and SRIT-style did no better.
- **The method to present:** pool the candidates from several generators and score all of them by MMSC (tested in Phase 4).
- **Unchanged:** the theorems of §7 are about the selection rule, so they apply to any generator whose candidates include the true form.

**Revised after Phase 4 (§12.3).**
- **The instrument does its work when formulas are scored, not when they are generated.** Plain PySR's squared-error front, scored by MMSC, recovered the law as often as the IV-specific generators in designs D1, D2 and D4. In the strong-endogeneity power-law cell, PySR's own pick never recovered the form (0/12 at every $n$), yet its front contained the form in every run and MMSC selected it in 67–100% of runs. IV-specific generators matter where endogeneity changes the shape of $E[y \mid X]$ (simultaneity, D3).
- **Pooling did not beat the distilled front alone.** It adds coverage, but also wrong formulas that outscore the truth.
- **The selection rule needs a structure term.** Plain BIC lets near-duplicates of the law win even at $n = 50\,000$. Adding $w \cdot \text{nodes} \cdot \ln m$ (a per-node version of Theorem 2's $\log\lvert\mathcal S_L\rvert$) raised recovery from 51% to 60% and gave 100% from $n = 5000$ in the $n$-scaling cells.
- **The method to present:** generate candidates cheaply (plain PySR, and PySR distilled from a sieve-2SLS curve), then select by MMSC with the structure term. Contribution: the selection rule, its theory (§7) and diagnostics.

## 5. Model and identification

- **Model:** $y = f_0(X) + u$ with $E[u \mid Z] = 0$; the target is $f_0$. The error is **additive**. Non-separable models (random coefficients, e.g. $y = w \cdot h$ with heterogeneous $w$) violate this and are out of scope for the paper; IV quantile regression ([Chernozhukov & Hansen 2005](https://doi.org/10.1111/j.1468-0262.2005.00570.x)) is the route to an extension *(beyond the paper)*.
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
- Phase 2 (§12): BIC recovered the true form most often (66–92%), then HQIC (52–68%), then AIC (28–40%). Even BIC lets contrived formulas with one extra constant through, because it does not account for the search over formula structures (§7).
- Phase 4 (§12.3):
  - **Add a structure term.** BIC plus $w \cdot \text{nodes} \cdot \ln m$, with $m$ the number of symbols and $w = 0.5$, is the best rule tested: 60% recovery against 51% for BIC on the pooled candidates (46 runs won, 8 lost; $p < 0.001$). It removes the near-duplicates that BIC admits at any $n$. It costs recovery on the saturation law, whose true form is long.
  - **What did not help:** the cross-fitted moment criterion (28%), because over-parameterized formulas that contain the truth tie on held-out moments; doubling $K$ (no change).
  - **Kernel instruments (criterion (c))** were slightly better than splines (54% vs. 51%, $p = 0.015$).

### 6.4 Inference after selection

Selection and inference use different data:

1. Split the sample: part A for search and selection, part B for everything reported.
2. On B: refit the selected formula's constants by efficient GMM; standard errors; Hansen $J$ test; weak-identification-robust (Anderson–Rubin type, [Stock & Wright 2000](https://doi.org/10.1111/1468-0262.00151)) confidence sets for the constants; [Horowitz (2006)](https://doi.org/10.1111/j.1468-0262.2006.00670.x) test of the selected formula against the nonparametric alternative.
3. This is valid conditional on the selected formula. Uniformly valid inference after selection without splitting is not claimed ([Leeb & Pötscher 2005](https://doi.org/10.1017/S0266466605050036); [Berk et al. 2013](https://doi.org/10.1214/12-aos1077)) *(beyond the paper)*.
4. **Identification diagnostic** (Phase 5; `symiv.identification`; [THEORY.md](THEORY.md) Proposition 5). After selection, report the first-stage $F$ of $X$ on the instruments, Anderson–Rubin intervals for the constants, and the **formula confidence set**: the candidate formulas whose Stock–Wright $S$ statistic the data do not reject. It contains the true form with probability at least $1 - \alpha$ whatever the instrument strength, so when a wrong formula is selected while the true form was a candidate, the set shows a second formula with probability at least $1 - \alpha$. The verdict is "identified", "weakly identified" (listing the formulas the data also allow) or "rejected" (no candidate of the selected form fits the moments). Under the weak instrument (D5) the method then reports weak identification instead of a formula (§12.4).

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
- **Optional RL version** *(beyond the paper)*: Deep Symbolic Regression ([Petersen et al. 2021](https://arxiv.org/abs/1912.04871)), with reward $= -$ criterion.

## 7. Theory plan

> **Phase 5 status ([THEORY.md](THEORY.md); three passes: the author's two, then two fresh-context referees, with a review log of what each pass found).**
> - **Theorem 1 (i)–(iii) is proved.** It holds for any candidate generator whose candidates contain a minimal true formula. Corollary 1.1 gives the parametric rate when the law is in the class. The split-sample intervals, $J$ test and AR sets of (iii) were simulated (§12.4): nominal on fresh samples, distorted on the selection sample, and only the AR sets survive the weak instrument.
> - **Theorem 2 is proved with explicit constants**, for GMM with orthonormal instruments, sub-Gaussian errors and a bounded Lipschitz class, with two failure channels:
>   - a separation margin $n\delta_s/\sigma^2 - (p_0 - p_s)\kappa_n$, plus deviation terms of the same order $\log n$, for wrong formulas;
>   - a complexity condition for longer or more heavily parameterized formulas.
>
>   A per-node structure penalty makes the bound uniform in $L$ (Corollary 2.2; the theory's $w \approx 5$ is conservative against the empirical $0.5$). Proposition 2.4 extends the bound to the code's sample-orthonormalized criterion and an estimated scale. Corollary 2.3 (candidates from an independent sample) was simulated: the mechanism holds, but the structure term on the full sample does better (§12.4).
> - **Proposition 5** (new): an Anderson–Rubin confidence set for the formula, valid whatever the instrument strength, is the identification diagnostic of §6.4. On the Phase 4 runs it flags every weak-instrument run and 4% of the strong-instrument runs whose selection was right, and covers the true form in 99% of the runs where it was a candidate (§12.4).
> - **Discrete instruments** (Proposition 4, parts (a)–(b)): formulas with $J$ or more constants can zero the criterion. Part (c) is a conjecture with its transversality hypothesis stated.
> - **Theorem 3(a)** (fixed $L$, misspecified) and **Theorem 3(b)** (growing $L$, compact support, any number of regressors) are proved; `max` gives a spline sieve for one regressor and Bernstein polynomials give one for several. Proposition 3.3 reduces rates to a modulus of continuity on the formula sieve; bounding it is open.
>
> The plan below is kept as written.

**Setting.** $\mathcal S_L$ is the finite set of expression trees with at most $L$ nodes over the operator set. Tree $s$ has $p_s$ constants in $\Theta_s = [-C, C]^{p_s}$, and $\mathcal F_L = \{f_s(\cdot\,;\theta)\}$. The estimator is

$$(\hat s, \hat\theta) \in \arg\min_{s,\,\theta}\; Q_n\big(f_s(\cdot\,;\theta)\big) + \mathrm{pen}_n(s), \qquad \mathrm{pen}_n(s) \propto p_s \ln n / n.$$

Let $T h = E[h(X) \mid Z]$.

**Assumptions.** (A1) $E[u \mid Z] = 0$ with finite second moments. (A2) Restricted identification (§5). (A3) Each $f_s(x;\theta)$ is continuous in $\theta$ with a square-integrable envelope (protected operators, bounded support). (A4) For (c), a bounded ISPD kernel; for (b), $K_n \to \infty$, $K_n/n \to 0$, with a basis whose span is dense.

| Result | Target statement | Tools | Feasibility |
|---|---|---|---|
| **Theorem 1: consistency and selection (well-specified)** | If $f_0 \in \mathcal F_L$ with $L$ fixed, $\mathrm{pen}_n \to 0$ and $n\,\mathrm{pen}_n \to \infty$: (i) $\lVert \hat f - f_0\rVert_{L^2} \to_p 0$; (ii) with probability $\to 1$, the selected tree represents $f_0$ with the fewest constants; (iii) on the split sample, $\sqrt n(\hat\theta - \theta_0)$ is asymptotically normal under the usual rank condition (pointwise, not uniform) | Extremum-estimator consistency ([Newey & McFadden 1994](https://doi.org/10.1016/S1573-4412(05)80005-4)); consistent GMM model selection (Andrews & Lu 2001); degenerate $U$-statistics for MMR at the truth; [Andrews & Cheng (2012)](https://doi.org/10.3982/ECTA9456) for over-parameterized trees whose extra constants are unidentified | **High.** Mostly known tools; the work is careful bookkeeping (trees that represent the same function, nested trees) |
| **Theorem 2: finite-sample selection bound** (the "short formulas regularize" claim, made precise) | Separation $\delta_L = \min_{s:\, f_0 \notin f_s(\cdot;\Theta_s)}\ \min_{\theta}\ \lVert T(f_s(\cdot\,;\theta) - f_0)\rVert^2$. By (A2) and compactness, $\delta_L > 0$ even though $T^{-1}$ is unbounded. Target form: $P(\text{wrong tree}) \le \exp\{\log\lvert\mathcal S_L\rvert + p_{\max}\ln n - c\,n\,\delta_L^2\}$ | Uniform concentration over a finite union of Lipschitz-parameterized classes (bounded kernel or envelope); covering numbers | **Medium-high.** The main new result. It predicts that recovery tracks $n\,\delta_L^2$, and that $\delta_L$ shrinks with weaker instruments, larger $C$ and larger $L$. These predictions are testable in the Monte Carlo, where $\delta_L$ can be computed |
| **Theorem 3: misspecified, growing $L_n$** (consistency proved in THEORY.md on a compact support; rates and unbounded supports *beyond the paper*) | $\bigcup_L \mathcal F_L$ as a nonlinear sieve in penalized sieve minimum distance (Chen & Pouzo 2012; Chen 2007): consistency of $\hat f$ when $f_0 \notin \mathcal F_L$ for every fixed $L$ | Nested classes ($\mathcal F_L \subseteq \mathcal F_{L+1}$); lower-semicompact penalty from bounded constants; approximation inherited from the polynomial sub-sieve contained in $\mathcal F_L$ | **Consistency: medium. Rates: low.** The ill-posedness measure of a nonlinear, non-convex sieve is not standard; possibly a separate paper |
| Proposition (conjecture): discrete instruments | With $Z$ taking $J$ values, restricted identification holds generically in the distribution of $X \mid Z$ when $J > p_{\max}$ | Transversality for analytic families | Parts (a)–(b) proved in THEORY.md (formulas with $\ge J$ constants can zero the criterion); the generic part is Conjecture 4 (c), *beyond the paper* |

**Not claimed:**

- Guarantees for the genetic-programming search itself. The theorems concern the global minimizer, or any near-minimizer within $o_p(\mathrm{pen}_n)$. The Monte Carlo separates **search failures** (the true formula has a lower penalized criterion than the one found) from **statistical failures** (the estimator itself prefers a wrong formula).
- Uniformly valid inference after selection without sample splitting.

**Phase 2 evidence (§12).** Failures were statistical, not search failures (2 of 200 runs). Both kinds of error that Theorem 2 has to cover appeared:
- a simpler wrong formula winning when separation is small ($x + c$ against $2x^{0.7}$ with $\pi = 0.7$, $n = 2000$);
- a contrived formula with one extra constant winning because it fits the moments slightly better. The best of many structures beats a per-constant $\ln n$ penalty, which is why the bound carries a $\log\lvert\mathcal S_L\rvert$ term.

**Phase 3 evidence (§12.2).** The theorems are about the selection rule, not the search. Phase 3 shows that is where the value lies: the same rule applied to candidates from a distilled NPIV fit did better than the one-step search. For the theory, the candidate set can come from any generator; what matters is whether it contains the true form and how many competitors it adds (the $\lvert\mathcal S\rvert$ in Theorem 2).

**Phase 4 evidence (§12.3).**
- **Theorem 1 holds in the data only with a structure term.**
  - With BIC + structure, recovery reached 100% from $n = 5000$ to $50\,000$ for every generator in the $n$-scaling cells.
  - With BIC alone, 1–3 of 12 runs still chose a near-duplicate at every $n$. These formulas have the same number of constants as $f_0$ but more nodes. An example is $(x\,e^{x/\max(c,\,x)})^{\theta}$, which equals $e^{\theta}x^{\theta}$ wherever $x > c$.
- **The separation that predicts selection is not $\delta_L$ over all wrong trees.** Measured that way it was about 0 in every cell, and unrelated to recovery (Spearman 0.10), for two reasons:
  - trees with more constants than $f_0$ approximate it arbitrarily well;
  - with a 4-point instrument (D4), any tree with 4 constants sets the criterion to zero, as the discrete-instrument conjecture predicts.
- **The quantity that matters is a penalty-adjusted margin:** $\min_s\,[\,n\delta_s/\sigma_u^2 - (p_0 - p_s)\ln n\,]$ over wrong trees with $p_s \le p_0$. Across 32 cells it tracked recovery given coverage (Spearman 0.56, $p < 0.001$): 74% when positive, 23% when not.
- **Revised target for Theorem 2.** The bound should have two terms:
  - a separation term over wrong trees with $p_s \le p_0$, using this margin;
  - a complexity term ($\log\lvert\mathcal S_L\rvert$) for the noise-fitting channel of trees with more constants.

  Near-duplicates make $\delta_s$ arbitrarily small at a fixed size, so the structure penalty belongs in the estimator, not only in the bound.

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

**Expected results** (stated so that they can fail), with outcomes from Phases 2–4 (§12):

- Plain SR returns a wrong formula or the right form with biased constants, depending on how large the endogeneity term is relative to $f_0$. **Confirmed.**
  - Its bias matches $\rho/(1+\pi^2)$.
  - Phase 4: wherever it finds the log-law form, its slope is 2.38–2.80 against a true value of 2; under simultaneity (D3) it never finds the form.
- Library IV matches symbolic IV on the log law and fails on power, kink and saturation. **Confirmed once the library is scored by MMSC.**
  - Its Lasso path scored by MMSC recovers the log law in 75–100% of runs in D1–D4.
  - Cross-validated Lasso managed only 28–52% (Phase 3).
  - It never recovers the other laws.
- One-step symbolic IV beats NPIV → distillation when the NPIV fit is unstable (weak instruments, small $n$, extrapolation). If it does not, the paper is repositioned (§3.2). **Refuted when the distilled candidates are scored by MMSC; repositioned (§4).** In Phase 4, even plain SR's candidates did as well when scored by MMSC.
- Control-function SR wins on D1 and loses on D2 (§8.1 baselines table). **Confirmed.**
  - It gives the lowest errors on D1; on D2 its form recovery falls to 0% (power law) and 42% (log law).
  - Raising $\gamma$ did not make it fail more, because $\gamma$ also strengthens the first stage (§12.3).
- Recovery tracks $n\,\delta_L^2$. **Supported in a corrected form (§7, §12.3):** recovery tracks a penalty-adjusted margin over wrong formulas with at most $p_0$ constants, not $\delta_L$ over all trees.
- Degradation under weak instruments is documented as part of the contribution. **Documented.** With $\pi = 0.1$ (D5), recovery is 0% for every law, and selected formulas err by 0.2–1.2 sd in sample. Since Phase 5 the identification diagnostic (§6.4) flags every D5 run, so the method reports weak identification there instead of a formula (§12.4).

### 8.2 Simulated economic environments

- **Supply and demand with endogenous prices** (D3): in the simulation the target is the supply curve, identified by a demand shifter. **Phase 6** adds the mirror image, design **D6**: quantity $= f_0(p) + u$ is a decreasing demand curve, the supply equation $q = \kappa\log p + \gamma Z + e$ is shifted by a cost shifter $Z$, and the price is set by equilibrium. Demand laws: constant elasticity $3p^{-0.5}$, log-linear $6 - 1.5\log p$ (in the library), hyperbolic $6/(1 + p)$. Results in §12.5.
- **Labour supply:** hours $= f_0(w) + u$ with a backward-bending $f_0$. The wage is endogenous because unobserved taste for work is correlated with productivity; the instrument is an exogenous wage shifter (e.g., a simulated tax reform). **Phase 6:** design D1 with $\pi = 0.5$ and the laws $8w\,e^{-0.5w}$ (a hump) and $5 + 2\log w - 0.6(\log w)^2$ (the textbook quadratic in logs, in the library); neither shape was in the Phase 4 grid. Results in §12.5.
- *Dropped:* earnings $=$ wage $\times$ hours with heterogeneous wages. It is not additive: $u = (w - \bar w)\,h$, and $E[u \mid Z] \neq 0$ because hours respond to $w$. In logs it becomes additive, but then the "law" is an identity with coefficient 1. The motivation that earnings risk partly reflects hours choices ([Halvorsen et al. 2024](https://academic.oup.com/jeea/article-abstract/22/2/617/7251473); [Kaplan & Violante 2010](https://www.aeaweb.org/articles?id=10.1257%2Fmac.2.4.53)) belongs to the non-separable extension (§5).

### 8.3 Real applications with known answers

| Application | Data | Instrument | Known answer | Role |
|---|---|---|---|---|
| **Engel curves** ([Blundell, Chen & Kristensen 2007](https://doi.org/10.1111/j.1468-0262.2007.00808.x)) | Public: BCK's own FES 1995 extract, the `Engel95` data frame shipped with the R package [`np`](https://cran.r-project.org/package=np) (1,655 married couples with an employed head aged 25–55; 7 budget shares, log total expenditure, the head's log earnings, a children indicator). No registration or affiliation is needed: extract `np/data/Engel95.rda` from the CRAN tarball and convert it with `pyreadr` into `data/engel95.csv` (git-ignored) | Household head's earnings, for log total expenditure | Budget shares linear in log expenditure (Working–Leser) for food; quadratic in log expenditure for some goods ([Banks, Blundell & Lewbel 1997](https://doi.org/10.1162/003465397557015)) | **Primary:** continuous instrument and a formula-shaped answer |
| **Gasoline demand** ([Blundell, Horowitz & Parey 2012](https://doi.org/10.3982/QE91); earlier nonparametric estimates in [Hausman & Newey 1995](https://doi.org/10.2307/2171777)) | US National Household Travel Survey 2001 (public) | Distance from the Gulf of Mexico (price shifter) | Price responsiveness that varies with price and income | **Secondary:** comparison with shape-restricted NPIV |
| Returns to schooling ([Angrist & Krueger 1991](https://doi.org/10.2307/2937954)) | Public: the Mastering 'Metrics extract `ak91.dta` (329,509 men born 1930–39), downloaded by hand into `data/` | Quarter of birth | None usable for functional form | **Stress test only.** The instruments are weak ([Bound, Jaeger & Baker 1995](https://doi.org/10.1080/01621459.1995.10476536)), discrete, and shift schooling only near the compulsory-schooling margin, so they cannot identify a functional form over the whole range. Success means the method reports weak identification instead of a confident formula |

## 9. Deliverables and venues

- **Open-source package:** symbolic IV on top of PySR (criteria (a)–(c), MMSC selection, split-sample inference), plus the Monte Carlo benchmark suite (designs D1–D5 × laws).
- **Paper:** an ML venue (NeurIPS / ICML causality tracks) needs §8 plus Theorems 1–2. An econometrics journal (*Journal of Econometrics*, *The Econometrics Journal*) needs full proofs of Theorems 1–2, and ideally the consistency part of Theorem 3.
- **Data:** no confidential data and no institutional access. Both applications use public extracts (the `Engel95` data of the R package `np` for the Engel curves; the Mastering 'Metrics extract for Angrist–Krueger), downloaded by the user into `data/` and not redistributed. The full FES/LCF files at the UK Data Service are not needed.

### 9.1 Scope of the paper

**In the paper:** the selection rule with the structure term and its diagnostics (§6.3–§6.4); Theorems 1 and 2 with their corollaries, Proposition 5, Theorem 3 (a) and (b) on a compact support, and Proposition 4 (a)–(b) ([THEORY.md](THEORY.md)); the Monte Carlo of Phases 2–5 (§12); one application with a known answer (Phase 6).

**Beyond the paper**, stated there as open problems or future work and marked *(beyond the paper)* wherever they appear in this file and in THEORY.md:
- rates of convergence for growing formula size (THEORY.md Proposition 3.3 reduces them to a sieve modulus; bounding it is open);
- Theorem 3 (b) on an unbounded support;
- Theorem 2 for the exact kernel criterion, and for the estimation error of an efficient weight under heteroskedasticity;
- Conjecture 4 (c), generic identification with fewer constants than instrument support points;
- the reinforcement-learning search variant (§6.6);
- non-separable models and the IV-quantile extension (§5, §10);
- uniformly valid inference after selection without sample splitting (§6.4);
- the remaining Phase 4 variations ($\rho$, the noise level, $J$ in D4, the bound $C$): a robustness appendix if cheap, not a requirement.

## 10. Risks

| Risk | Mitigation |
|---|---|
| Weak instruments; identification failure (completeness not holding) | Designs D4–D5; weak-ID-robust confidence sets; report the criterion gap to the runner-up; Angrist–Krueger stress test. **Phase 5:** the identification diagnostic of §6.4 flags every D5 run and 4% of the strong-instrument runs whose selection was right (§12.4) |
| Oscillatory formulas exploit ill-posedness | Bounded constants, restricted operators, nesting constraints (§6.1) |
| Criterion ties at zero with finite $K$ | $K$ much larger than the number of constants and growing with $n$, or MMR (§6.2) |
| Noisier, non-convex search (the moment criterion is flatter than MSE) | Several restarts; seed with the plain-SR front; report search failures separately (§7). Phase 2: only 2 of 200 failures were search failures at $n = 2000$ |
| Selection, not search, is the bottleneck: a penalty too weak for the size of the search space (contrived formulas win) or too strong for weak separation (simpler wrong formulas win) | **Phase 4:** a structure term fixes the first failure (60% vs. 51% recovery; 100% from $n = 5000$). The cross-fitted criterion, larger $K$ and dropping `max` did not help. The second failure is what the separation margin measures (§12.3) |
| The search never proposes the law (laws with a threshold or a ratio) | **Realized in Phase 4:** no generator produced the kink law in more than 33% of runs, and the saturation law appeared in 8–58% of runs. Next steps: templates such as $a x + b\max(x - c, 0)$, a larger search budget, and reporting a search failure (§7) instead of a wrong formula |
| Library IV or NPIV → distillation match the method | Laws outside any finite library; if the one-step method does not win, reposition (§3.2). **Realized for distillation (Phase 3):** distillation + MMSC beat the one-step search, so the contribution was repositioned to IV-scored selection over candidates (§4) |
| Misspecification on real data | Stability across instrument bases and weights (§6.5) |
| Additive-error assumption fails | Out of scope for the paper; IV quantile extension (§5) *(beyond the paper)* |
| Inference after the search has selected the formula ([Berk et al. 2013](https://doi.org/10.1214/12-aos1077); [Belloni et al. 2012](https://doi.org/10.3982/ecta9626); [Chernozhukov et al. 2018](https://doi.org/10.1111/ectj.12097)) | Sample splitting (§6.4) |
| Compute: exact MMR is $O(n^2)$ per evaluation | Low-rank factor (§6.2) |

## 11. Checkpoints

### Phase 0: literature and novelty
- [x] OpenAlex, arXiv, GitHub and web searches (2026-09-26)
- [x] Google Scholar queries (2026-09-27)
- [x] Read SRIT in full: independence-test pruning of inputs; assumes causal sufficiency; no instruments
- [x] Read Kuang & Lin in full: IV for coefficients only (fixed library, measurement noise); no model selection
- [x] Review: add high-dimensional IV, GMM model selection, NPIV testing and identification, distillation (2026-09-30, §3.2)
- [x] Sparse-IV estimator for the library baseline: settled in Phases 3–4 by the instrument-projected Lasso path scored by MMSC (§12.2–§12.3), in the spirit of Lin, Feng & Li (2015); STIV (Gautier & Rose) and Fan & Liao (2014) are cited as the alternatives, not implemented
- [x] Selection criterion and the rule for $K$: settled by Phases 2–4 (MMSC-BIC with the structure term; $K \approx n^{1/3}$, and doubling $K$ at selection changes nothing, §12.3); Andrews & Lu (2001) is the reference for MMSC
- [x] Horowitz (2006): cite only. The specification-test role is played by Hansen's $J$ and the $S$ tests of Proposition 5 (§6.4)
- [x] New searches (web, 2026-10-01): "symbolic regression" with "instrumental variable(s)", endogeneity, "unobserved confounders" or "method of moments"; SINDy with "instrumental variables"; "sparse instrumental variables" with dictionary or library; "equation discovery" with instrumental variables and confounding. Nothing new: no symbolic-regression or equation-discovery method scores formulas by instrument moments; the neighbours of §3.1 stand
- [x] 2026 references verified (2026-10-01): Kuang & Lin (arXiv 2511.09024, to appear at L4DC 2026); Zeiringer, Garnier & Horn (*J. Franklin Institute* 363(7), May 2026); Li, Feng & Cui (*J. Hydrology: Regional Studies* 65, June 2026)
- [ ] Optional: ask one nonparametric-IV researcher whether they know of related work

### Phase 1: infrastructure (done 2026-09-30; §13)
- [x] Repository skeleton: `src/symiv/{dgp, criteria, baselines}`, `experiments/`, `tests/`
- [x] DGPs D1–D5 with seeds, returning $(y, X, Z)$, the true $f_0$, and the hidden errors for checks
- [x] Criterion matrix $A$: B-spline (or polynomial) basis, orthonormalized by SVD so discrete instruments drop collinear columns, for (b); Nyström features for (c). $K$ defaults to about $n^{1/3}$
- [x] Julia `loss_function` computing $\lVert A^\top r\rVert^2/n$, with a soft penalty beyond the constant bound $C$ (the hard bound is enforced in the GMM refit). Verified to match the Python criterion to $10^{-6}$ on every Pareto-front formula
- [x] Unit test: the criterion is over 20× larger at $E[y \mid X]$ (plain SR's target) than at $f_0$, for both criteria; $J$ at the truth averages $K$ over 200 draws
- [x] MMSC selector over the Pareto front (two-step efficient GMM refit, $J_n - (K - p_s)\ln n$); picks the true form over both a wrong form and an over-parameterized form that contains it
- [x] Recovery checks: numerical form recovery (primary) and SRBench's SymPy check
- [x] Search-failure vs. statistical-failure diagnostic (tested on a search failure and on an unidentified design with $\pi = 0$)
- [x] End-to-end smoke run (`experiments/smoke_pysr.py`, D1, power law, $n = 2000$): symbolic IV selected $2.02\,x^{0.693}$ (outcome: success); relative function error 0.014 vs. 0.091 for plain PySR

### Phase 2: first Monte Carlo (done 2026-09-30; results in §12)
- [x] D1 with the power law $2x^{0.7}$ and the log law $1 + 2\log x$, $n = 2000$, 50 seeds, in a default setting ($\pi = 1$, $\rho = 0.8$) and a strong-endogeneity setting ($\pi = 0.7$, $\rho = 1.2$)
- [x] Plain PySR's bias measured as function error, extrapolation error, elasticity and implied constants, not only form recovery. Its slope bias matches $\rho/(1+\pi^2)$ to two decimals
- [x] Plain SR selected with a stated rule: least-squares refit, then $n\log(\mathrm{RSS}/n) + p\,\kappa_n$ with the same $\kappa_n$ as MMSC; PySR's own pick reported alongside
- [x] Symbolic IV recovery rate over 50 seeds: 66–92% with BIC; errors within about 1.5× of the true-form IV fit
- [x] MMSC gap to the runner-up tracked: median 2.2–4.7 under BIC, 0.8–0.9 under AIC
- [x] Sensitivity to $C$ and $K$ (20 seeds, power law, strong setting): $K$ matters (30% at $K = 8$, 70% at $K = 25$); $C$ does not, with this operator set

### Phase 3: baselines (done 2026-10-01; results in §12.2)
- [x] Oracle 2SLS and wrong-form 2SLS (linear, log, power forms)
- [x] Sieve 2SLS (B-splines in log x, J by held-out moment criterion), KIV (Singh et al.'s split-sample tuning), DeepIV (torch; first 20 seeds)
- [x] NPIV → PySR distillation from each NPIV fit, with PySR's own pick and with MMSC on the original data
- [x] Library + sparse IV (9-term library, instrument-projected cross-validated Lasso, GMM refit; in the spirit of Lin, Feng & Li 2015)
- [x] Control-function SR with `TemplateExpressionSpec` f(x) + g(v̂)
- [x] SRIT: the original is not runnable (its code link returned 404 on 2026-09-30; it used the commercial Eureqa engine). Replaced by a simplified SRIT-style reimplementation with PySR and HSIC pruning, clearly labelled
- [x] Run on the Phase 2 D1 cells (same data) and on D2, 50 seeds each: 300 runs, 0 method errors

### Phase 4: full grid (done 2026-10-01; results in §12.3)
- [x] Pooled candidates: pooling raised coverage (79% vs. 74% for the distilled front) but brought about three times as many wrong formulas that beat the truth. Recovery: 51% pooled vs. 58% distilled (BIC)
- [x] Why distilled candidates select better: their fronts hold fewer formulas that outscore the truth (1.0 vs. 1.6 per run) and contain the true form more often (74% vs. 65%), as hypothesized
- [x] Library + MMSC: the Lasso path scored by MMSC recovers the log law in 75–100% of runs (D1–D4), against 28–52% with cross-validation. The Phase 3 failures were the tuning; the library's limit is coverage
- [x] Control-function SR on D2 with $\gamma \in \{0.45, 0.6\}$: power-law recovery stays at 0%; log-law recovery rises (83%, 100%), because $\gamma$ also strengthens the first stage. Inconclusive by design
- [x] All laws × D1–D5 at $n = 2000$ (5 laws, 24 cells, 12 seeds)
- [x] Recovery as $n$ grows ($1\,000 \to 50\,000$), strong setting: 100% from $n = 5000$ with the structure term; BIC alone plateaus at 75–92% (near-duplicates)
- [x] Selection rules: structure term (best: +9 points); cross-fitted criterion (worst: −23 points)
- [x] Default $K$: doubling $K$ at the selection stage changes nothing (51% vs. 51%); keep $n^{1/3}$
- [x] Operator ablation without `max`: no gain (all paired differences within 3 runs, $p \ge 0.25$); contrived winners use other operators
- [x] Criterion (c) vs. (b): kernel instruments slightly better at selection (54% vs. 51%, $p = 0.015$)
- [x] Separation: $\delta_L$ over all wrong trees is uninformative; a penalty-adjusted margin over wrong trees with $\le p_0$ constants tracks recovery (Spearman 0.56)
- [x] Write up the first results (§12.3)
- [ ] Remaining variations: $\rho$, noise level, $J$ in D4, the bound $C$, and 20 seeds instead of 12
- [ ] Control function: a design that breaks its assumption without strengthening the instrument (e.g. vary $\gamma$ at a fixed variance of $X$ given $Z$)
- [ ] Search coverage for the kink and saturation laws: templates, a larger budget, more restarts
- [ ] Structure term: tune $w$ and the per-node cost; check the loss on long true forms (saturation)
- [x] Weak-identification warning: done in Phase 5 (`symiv.identification`, §6.4, §12.4): first-stage strength, AR intervals and the formula confidence set

### Phase 5: theory (three passes done 2026-10-01; [THEORY.md](THEORY.md), simulations in §12.4)
- [x] Formal setup and assumptions: (A0)–(A3), (A2$_K$) and (A5). Trees that represent the same function are handled through the set of minimal true trees $\mathcal S_0^{\min}$; recovering the form means selecting any of them. Second pass: parameter sets made compact where a formula can be undefined
- [x] Theorem 1 (i): consistency, for any generator whose candidates contain a true tree; Corollary 1.1: parametric rate when the law is in the class
- [x] Theorem 1 (ii)–(iii): selection consistency (needs only $nQ_n(f_0) = O_p(1)$ and $\kappa_n \to \infty$); split-sample normality, $J$, and Anderson–Rubin sets
- [x] Theorem 2: finite-sample bound with a separation channel and a complexity channel, **all constants explicit** (second pass: the chaining step with an unknown constant was replaced by a projection bound). Corollary 2.2: a per-node structure penalty makes it uniform in $L$; the condition on $w$ is explicit
- [x] Theorem 2 extensions: the code's sample-orthonormalized criterion and an estimated scale (Proposition 2.4, Corollary 2.5); general weights and the Nyström kernel criterion by a substitution rule
- [x] Discrete-instrument proposition: parts (a)–(b) proved (formulas with $\ge J$ constants can zero the criterion; checked numerically on D4); part (c) is a conjecture with its transversality hypothesis stated
- [x] Theorem 3 (a): fixed $L$, misspecified law, convergence to the pseudo-true set
- [x] Theorem 3 (b): consistency as $L$ grows, proved directly on a compact support; approximation within a Lipschitz ball by `max` hinges (one regressor) and by Bernstein polynomials (any number of regressors)
- [x] Simulated Theorem 1 (iii) on the Phase 4 fronts: nominal coverage on fresh samples; 83–90% on the selection sample; under the weak instrument only AR sets keep their coverage
- [x] Tested Corollary 2.3: fewer wrong candidates beat the truth when selection uses an independent sample, but full-sample selection with the structure term recovers more
- [x] Proposition 5: an identification-robust confidence set for the formula, the diagnostic built on it (`symiv.identification`, §6.4), and its evaluation on all 288 Phase 4 breadth runs: every D5 run flagged, 4% false alarms, 99% coverage of the true form
- [x] Rates: parametric when the law is in the class (Corollary 1.1); for growing $L$, reduced to a modulus of continuity on the formula sieve (Proposition 3.3)
- [ ] Bound that modulus for formula sieves (the open rate problem; $\mathcal F_L - f_0$ is not a linear space)
- [ ] Theorem 3 (b) on unbounded supports: envelope-respecting approximants and a deviation bound with an unbounded envelope
- [ ] Theorem 2 for the exact kernel criterion (degenerate U-processes) and for the estimated efficient weight under heteroskedasticity
- [ ] Conjecture 4 (c): a design family of dimension $\ge J - p_s$ for which the regular-value condition can be verified
- [x] Third pass (2026-10-01): two fresh-context referees (separate model instances, one per half of THEORY.md) read the proofs cold. The theorem statements and proofs stood; they found one error in an informal reading of Theorem 2 ($k_s \le p_s$ fails for trees nonlinear in their constants), three errors in Proposition 5 (the sample envelope needs a stated condition, part (b) was a conditional claim, one $O_p(1)$ step), a missing probability in Corollary 2.5, and that Corollary 2.2's constants certify nothing at $n = 2000$. All fixed; THEORY.md §9 lists them. A human reading before submission remains advisable, not a blocker

### Before the paper (required)
- [x] Weak-identification diagnostic (2026-10-01): first-stage $F$, AR intervals for the constants and the formula confidence set of THEORY.md Proposition 5, in `symiv.identification`; evaluated on every Phase 4 breadth run (§12.4)
- [ ] **More seeds in the headline cells.** Twelve seeds give recovery rates with intervals about 25 points wide, too wide for the comparisons the paper rests on (pooled vs. distilled candidates, BIC vs. BIC + structure, recovery as $n$ grows). Raise the cells the paper leans on to 50 seeds, as in Phase 2: D1 default and strong × log and power; D3 × log and power; D5 × all five laws; the $n$-scaling cells at $n \in \{1000, 2000, 5000\}$. About 650 extra searches, roughly a day of compute at the Phase 4 rates; the scripts resume, so this can run in the background. **In progress:** the 570 searches (`phase4.py --grid headline`) were launched on 2026-10-01 as a detached job of about 15 hours; the Phase 4 re-analysis and report, the identification diagnostic on the new runs and the budget experiment below are queued behind it
- [x] The simulated economic environments (demand with a cost shifter; labour supply) and the Angrist–Krueger stress test are done (§12.5)
- [x] One real application with a known functional form (2026-10-01): the Engel curves on BCK 2007's public FES 1995 extract (§12.5). The food share is compatible with Working–Leser in all three samples, the motor share needs a quadratic term, and on 628–1,655 households the method reports weak identification rather than a confident formula
- [ ] **A search budget that reaches three-constant formulas.** Selection chose the true form whenever it was a candidate, but the search proposed the quadratic-in-logs labour law in only 20–45% of runs, the kink law in at most 33% and the saturation law in 8–58% (§12.3, §12.5): the Phase 2–6 budget (40 iterations, maximum size 15, default operators) is what every result so far was obtained with. Before the paper, rerun the cells with a three-constant or threshold law under a larger budget (more iterations and populations, size up to 25, restarts with different seeds) and with templates for the economic shapes (`a + b log w + c (log w)^2`, `a x + b max(x − c, 0)`); report coverage before and after, since coverage, not selection, is the binding constraint in those cells. **In progress** (`experiments/phase7_budget.py`, §12.6): the template library is built (`symiv.templates`) and the base-budget arms are analysed; on the saved fronts, templates give 100% coverage but recover the kink law in 0 of 24 runs and the quadratic labour law in 0 of 20, so for those laws the binding constraint is separation, not coverage. The large-budget searches run after the seeds job
- [x] Reading of the proofs by fresh-context referees (2026-10-01; Phase 5 list above, THEORY.md §9). A human reading before submission is advisable but not required to finish the paper

### Beyond the paper
See §9.1: listed there so they do not read as blockers, and marked *(beyond the paper)* in place.

### Phase 6: applications
- [x] Simulated demand and labour-supply environments (2026-10-01; §12.5): design D6 and five new laws; demand curves recovered in 70–100% of runs with oracle-level error and the right elasticity; the backward-bending laws show the limits (the bend must be inside the data and the instrument's reach; 3-constant forms are proposed by the search in only 20–45% of runs)
- [x] Engel curves, pipeline (2026-10-01): `phase6_engel.py` selects the formula, tests the Working–Leser and quadratic forms, and runs the identification report; self-tested on synthetic FES-like data (§12.5)
- [x] Engel curves, data (2026-10-01): BCK 2007's own FES 1995 sample is public (the `Engel95` data of the R package `np`; `fetch_data.py`), so no registration was needed. Seven budget shares × three samples (all couples, without children, with children), 21 runs; results in §12.5. The NPIV curve itself is not replicated (BCK's sieve and ours differ); the Working–Leser and quadratic forms are tested by their S tests and the quadratic term's AR interval
- [ ] Gasoline demand (secondary; after the Engel curves): the NHTS 2001 household file is public but the price variable must be merged from an external source and the instrument definition confirmed in BHP 2012 before anything can be run
- [x] Angrist–Krueger stress test (2026-10-01): replicates $F = 4.9$, OLS 0.071, 2SLS 0.089; with both instrument sets the method reports weak identification instead of a formula, and the AR interval for the return includes zero (§12.5)

### Phase 7: package and paper
- [ ] Package API and documentation; release the benchmark suite
- [ ] Paper draft; choose the venue after Phase 4 and Theorem 2

## 12. Results

### 12.1 Phase 2 Monte Carlo

Design D1, $n = 2000$, 50 seeds per cell; the same PySR budget and operators for both methods; formulas selected by BIC-type rules after refitting constants (§6.3). Full tables, including HQIC and AIC, oracle fits and outcome counts: [`experiments/phase2/summary.md`](experiments/phase2/summary.md). Errors are RMS$(\hat f - f_0)$ in units of the in-sample sd of $f_0$; extrapolation is on $[q_{99}, 3q_{99}]$ of $X$.

| Law, setting | True form recovered: plain PySR (own pick / BIC) | True form recovered: symbolic IV (BIC), 95% CI | In-sample error: plain / symbolic IV / oracle IV | Extrapolation error: plain / symbolic IV | Constant (truth): plain / symbolic IV |
|---|---|---|---|---|---|
| $2x^{0.7}$, default | 100% / 10% | 86% (74–93) | 0.088 / 0.013 / 0.013 | 0.55 / 0.09 | $a$ (2): 2.12 / 2.00 |
| $2x^{0.7}$, strong | 0% / 6% | 66% (52–78) | 0.330 / 0.039 / 0.027 | 0.74 / 0.30 | $a$ (2): 2.15 / 1.98 |
| $1 + 2\log x$, default | 100% / 88% | 92% (81–97) | 0.202 / 0.020 / 0.012 | 0.55 / 0.03 | $b$ (2): 2.40 / 2.00 |
| $1 + 2\log x$, strong | 100% / 88% | 80% (67–89) | 0.406 / 0.033 / 0.023 | 1.12 / 0.06 | $b$ (2): 2.81 / 2.01 |

"Plain" errors and constants are for PySR's own pick; constants are medians of those implied in the true form. Default: $\pi = 1$, $\rho = 0.8$; strong: $\pi = 0.7$, $\rho = 1.2$.

**Findings**

1. **Plain SR estimates the conditional mean, as §5 predicts, and quantitatively so.**
   - Its log-law slope is 2.40 and 2.81, against $2 + \rho/(1+\pi^2) = 2.40$ and $2.81$.
   - For the power law, the BIC pick has the conditional-mean shape (e.g. $2.06\,x^{0.69} + 0.39\log x$ against $E[y \mid X] = 2x^{0.7} + 0.40\log X$). PySR's default pick drops the small term, which is why it "recovers" the form with $a$ biased by 6%.
   - Under strong endogeneity PySR's default pick never finds the form (0/50).
   - Form recovery alone would have hidden this bias.
2. **Symbolic IV is close to the oracle IV fit of the true form.** Its errors are within about 1.5× of that fit and its constants are unbiased. Its errors are 7–12× smaller than plain SR in sample and 2.5–18× smaller in extrapolation.
3. **Symbolic IV recovers the true form in 66–92% of runs. The failures come from selection, not search:** only 2 of 200 were search failures. The rest are of two opposite kinds:
   - a simpler wrong formula when separation is weak (7 of the 17 power-law failures in the strong setting are $x + c$);
   - a contrived formula, often built with `max`, whose extra constant fits the moments slightly better.
4. **The penalty matters.** Recovery was 66–92% with BIC, 52–68% with HQIC and 28–40% with AIC; the median MMSC gap to the runner-up shrinks from 2–5 to below 1. Even BIC ignores the search over structures (§7), so the next step is a structure-aware penalty (Phase 4).
5. **Sensitivity** (power law, strong setting, 20 seeds):
   - More instruments help: recovery was 30% at $K = 8$, 60% at $K = 13$ and 70% at $K = 25$ (Fisher $p = 0.03$ for 8 vs. 25, one comparison of several).
   - The bound $C \in \{3, 10, 100\}$ made no detectable difference ($p = 0.75$), as expected without oscillatory operators.
6. **Cost:** median 26 s per symbolic-IV search against 4 s for plain PySR ($n = 2000$, 8 threads).

### 12.2 Phase 3: baselines

The Phase 2 D1 cells (same data) plus design D2, where the control-function assumption fails but the IV condition holds. There are 50 seeds per cell ($n = 2000$), except DeepIV (20). Full tables, including oracle and wrong-form IV, elasticities, extrapolation, runtimes, and each method's paired win rate against symbolic IV: [`experiments/phase3/summary.md`](experiments/phase3/summary.md).

Each formula entry is: true form recovered, then median in-sample error (units of sd of $f_0$). Curves give no formula, so only their error is shown.

| Cell | $f_0$ | Symbolic IV | Sieve 2SLS → PySR, MMSC | KIV / DeepIV → PySR, MMSC | Sieve 2SLS → PySR, PySR's pick | Control-function SR | Library + sparse IV | SRIT-style | Curves: sieve / KIV / DeepIV |
|---|---|---|---|---|---|---|---|---|---|
| D1 default | $2x^{0.7}$ | 86%, 0.013 | 90%, 0.014 | 64% / 90% | 16%, 0.052 | 84%, 0.006 | 0%, 0.037 | 0%, 0.282 | 0.076 / 0.721 / 0.395 |
| D1 default | $1 + 2\log x$ | 92%, 0.020 | 98%, 0.016 | 64% / 95% | 8%, 0.032 | 100%, 0.011 | 36%, 0.024 | 98%, 0.400 | 0.032 / 0.375 / 0.126 |
| D1 strong | $2x^{0.7}$ | 66%, 0.039 | 74%, 0.036 | 62% / 80% | 4%, 0.101 | 72%, 0.015 | 0%, 0.054 | 0%, 0.505 | 0.110 / 0.765 / 0.447 |
| D1 strong | $1 + 2\log x$ | 80%, 0.033 | 86%, 0.030 | 42% / 80% | 2%, 0.072 | 100%, 0.021 | 28%, 0.051 | 86%, 0.599 | 0.076 / 0.436 / 0.201 |
| D2 | $2x^{0.7}$ | 86%, 0.006 | 100%, 0.005 | 56% / 90% | 52%, 0.039 | 0%, 0.014 | 0%, 0.082 | 0%, 0.123 | 0.106 / 0.936 / 0.671 |
| D2 | $1 + 2\log x$ | 88%, 0.020 | 100%, 0.016 | 78% / 100% | 12%, 0.029 | 42%, 0.034 | 52%, 0.017 | 40%, 0.369 | 0.031 / 0.333 / 0.127 |

**Findings**

1. **Selection is what works.**
   - Distilling a sieve-2SLS fit and scoring the resulting formulas by MMSC on the original data recovered the true form in 74–100% of runs. That is more often than the one-step search in every cell: on the same data, 37 runs were recovered only by distillation + MMSC and 12 only by the one-step search (exact McNemar $p = 0.0005$).
   - The same distilled candidates with PySR's own pick, the version in the literature, recovered the form in 2–52%.
   - Even the poor KIV curve gives 42–78% once its candidates are scored by MMSC.
   - Hypothesis for Phase 4: fronts fitted to a smooth curve contain fewer contrived formulas that fit moment noise. This led to the repositioning in §4.
2. **Control-function SR wins when its assumption holds and fails when it does not, as §8.1 predicted.**
   - On D1 it has the lowest errors of any method (0.006–0.021).
   - On D2 its recovery falls to 0% (power law) and 42% (log law); it gets the curve's shape wrong while staying close in sample. There it beats symbolic IV on error in only 30% of seeds.
   - IV-based selection works in both designs.
3. **Library + sparse IV approximates well but rarely recovers exact laws.** It has competitive in-sample errors (0.017–0.082). It never recovers the power law, which is not in its library. For the log law, which is, cross-validated Lasso usually adds terms (28–52% recovery).
4. **Black-box NPIV curves are less accurate and extrapolate badly.**
   - Sieve 2SLS is the best of them (0.03–0.11).
   - KIV struggles at these instrument strengths (0.33–0.94); with $\pi = 3$ its error is about 0.05, so this is ill-posedness, not a bug.
   - Beyond the data, curves err by 0.1–4.7, against 0.02–0.30 for the selected formulas.
5. **Guessing the form is costly.** IV fits of an assumed linear, log or power form have in-sample errors of 0.3–2.4 and extrapolation errors of 1.9–9.3.
6. **SRIT-style pruning does not fix endogeneity.** It keeps Z in all 300 runs, because Z is informative about $y$ given $X$ when $X$ is confounded. Its implied $f$ carries the confounding term, with errors of 0.12–0.60: usually worse than plain SR.

### 12.3 Phase 4: full grid

**Searches:** 528, with 12 seeds per cell (20 were planned; cut for compute), for about 12 hours of search time. Every Pareto front was saved, and the selection rules were applied afterwards to the same fronts. The grids:
- **Breadth:** five laws × designs D1–D5 at $n = 2000$.
- **$n$-scaling:** power and log laws in the D1 strong setting, $n = 1000$ to $50\,000$.
- **Operator ablation:** no `max`.
- **Control function:** D2 with larger $\gamma$.

**Candidate sets:**
- PySR's squared-error front ("plain");
- the one-step IV front;
- PySR distilled from a sieve-2SLS curve;
- the projected-Lasso library path;
- all of these pooled.

**Selection rules:**
- MMSC with BIC, HQIC and AIC penalties;
- BIC plus a structure term $w \cdot \text{nodes} \cdot \ln m$, with $m$ the number of symbols;
- BIC with $2K$ instruments;
- BIC with kernel (Nyström) instruments;
- a two-fold cross-fitted criterion.

Full tables, including per-cell errors, the operator ablation and the separation table: [`experiments/phase4/summary.md`](experiments/phase4/summary.md).

**Breadth: true form recovered by the pooled candidates with BIC + structure ($w = 0.5$); in brackets, the share of runs whose candidates contain the true form** (12 seeds per cell, $n = 2000$):

| Law | D1 confounding | D2 heterosk. first stage | D3 simultaneity | D4 discrete $Z$ ($J = 4$) | D5 weak $Z$ ($\pi = 0.1$) |
|---|---|---|---|---|---|
| $1 + 2\log x$ | 100% (100%) | 100% (100%) | 100% (100%) | 92% (100%) | 0% (100%) |
| $2x^{0.7}$ | 100% (100%) | 100% (100%) | 33% (67%) | 67% (100%) | 0% (100%) |
| $x - 0.8\max(x - 1.5, 0)$ | 0% (8%) | 0% (33%) | 0% (0%) | 0% (0%) | 0% (0%) |
| $3x/(1 + x)$ | 25% (58%) | 25% (33%) | 8% (42%) | 0% (25%) | 0% (8%) |
| $1.5\,x_1^{0.3}x_2^{0.5}$ | 100% (100%) | 92% (100%) | – | 83% (100%) | 0% (0%) |

**Selection rules × candidate sets** (all 456 runs with $n \le 5000$; recovery rate):

| Rule | Plain PySR front | One-step IV front | Distilled front | Library path | All pooled |
|---|---|---|---|---|---|
| MMSC-BIC | 52% | 48% | 58% | 31% | 51% |
| MMSC-HQIC | 52% | 41% | 55% | 27% | 44% |
| MMSC-AIC | 43% | 23% | 40% | 19% | 24% |
| **BIC + structure ($w = 0.5$)** | 51% | 54% | **63%** | 32% | **60%** |
| BIC, $2K$ instruments | 53% | 49% | 59% | 31% | 51% |
| BIC, kernel instruments | 53% | 51% | 59% | 32% | 54% |
| Cross-fitted criterion | 36% | 31% | 41% | 20% | 28% |

The columns cover different runs: the plain front exists only up to $n = 10\,000$, and the one-step front is absent from the control-function grid. Same-run comparisons are in the findings.

<picture><source media="(prefers-color-scheme: dark)" srcset="experiments/phase4/fig_nscale_dark.png"><img alt="Recovery rate against sample size in the D1 strong setting, for the distilled, plain-PySR and one-step candidates scored by MMSC with the structure term, and for plain PySR's own pick. The numbers are in experiments/phase4/summary.md, section 4." src="experiments/phase4/fig_nscale_light.png"></picture>

**Findings**

1. **The instrument does its work when formulas are scored, not when they are generated.**
   - On the same runs (breadth, D1–D4), MMSC-BIC recovered the law from plain PySR's front about as often as from the IV-specific fronts: 52%, against 47% (one-step), 52% (distilled) and 48% (pooled).
   - In the strong-endogeneity $n$-scaling cells, PySR's own pick never recovered the power law (0/12 at every $n$). Yet its front contained the true form in every run, and MMSC selected it in 67–100% of runs.
   - Where PySR's own pick does get the form, its constants are biased: the log-law slope is 2.38–2.41 in D1, D2 and D4 against 2.00 with MMSC, and its in-sample errors are 5–16× larger.
   - IV-specific generators matter where endogeneity changes the shape of $E[y \mid X]$. Under simultaneity (D3), the plain front contains the true form in 25% of runs, against 44–48% for the one-step and distilled fronts.
   - The cheap generators are also faster: median 9 s per plain or distilled search against 61 s for the one-step search.
2. **A structure term is needed, as Theorem 2's $\log\lvert\mathcal S_L\rvert$ suggests.**
   - BIC + $0.5 \cdot \text{nodes} \cdot \ln m$ raised pooled recovery from 51% to 60% (46 runs won, 8 lost; McNemar $p < 0.001$).
   - In the $n$-scaling cells it gave 100% recovery from $n = 5000$ for every generator.
   - With BIC alone, 1–3 of 12 runs still chose a near-duplicate of $2x^{0.7}$ at every $n$ up to $50\,000$, for example $(x\,e^{x/\max(c,\,x)})^{0.7}$ or $x^{0.75}(x e^{-x} + 1.74)$. These have the same number of constants as the truth, differ from it only at small $x$, and are separated by their size, not by the moments.
   - The term costs recovery on the saturation law, whose true form $ax/(b + x)$ is long: pooled recovery in D1 fell from 42% to 25%.
3. **Other rules:**
   - HQIC (44%), AIC (24%) and the cross-fitted criterion (28%) are worse than BIC. Cross-fitting fails because over-parameterized formulas that contain the truth tie with it on held-out moments.
   - Doubling $K$ at the selection stage changed nothing (16 runs won, 17 lost).
   - Kernel instruments (criterion (c)) were slightly better than splines (54% vs. 51%; 19 won, 6 lost; $p = 0.015$).
4. **Why distilled fronts select better** (the Phase 3 hypothesis, confirmed):
   - They contain the true form more often than one-step fronts (74% vs. 65%).
   - They hold fewer wrong formulas that outscore the truth under BIC (1.0 vs. 1.6 per run; at least one in 32% vs. 44% of runs).
   - **Pooling** raises coverage to 79%, but nearly triples these wrong formulas (2.9 per run). Recovery given coverage falls from 84% to 72%, so the pooled set does not beat the distilled front alone.
5. **The library baseline's limit is coverage, not the IV logic.**
   - Its Lasso path scored by MMSC recovers the log law in 100/100/92/75% of runs in D1–D4, against 28–52% with cross-validated Lasso (Phase 3).
   - Given coverage it recovers 96% of the time.
   - It contains the true form in only 35% of runs, because only the log law is in its library.
6. **Dropping `max` does not help.** In paired comparisons on the same data, no difference exceeded 3 runs ($p \ge 0.25$); without `max`, contrived winners use other operators.
7. **Separation explains the selection failures, in a corrected form (§7).**
   - $\delta_L$ over all wrong trees was about 0 in every cell and unrelated to recovery (Spearman 0.10).
   - The penalty-adjusted margin $\min_s [n\delta_s/\sigma_u^2 - (p_0 - p_s)\ln n]$, over wrong trees with $p_s \le p_0$, tracked recovery among runs whose candidates contained the true form: Spearman 0.56 ($p < 0.001$) across 32 cells; 74% recovery when the margin is positive, 23% when it is not.
   - **Caveat:** the margin is a worst case over the wrong formulas that any run produced.
8. **Where it fails:**
   - **Search failures:** the kink law was recovered in no pooled run; no generator produced it in more than 33% of runs. The saturation law appeared in 8–58% of runs.
   - **Weak instruments (D5):** recovery is 0% for every law. Selected formulas err by 0.2–1.2 sd in sample and 2.2–6.3 out of sample. Plain PySR is more accurate for two of the five laws in sample and for four of five out of sample. The method should report weak identification here rather than a formula (§6.4).
9. **The control-function test was inconclusive.**
   - With $\gamma = 0.45$ and $0.6$, control-function SR still never recovered the power law (0%). Its in-sample error fell to 0.003, and its log-law recovery rose to 83% and 100%.
   - In D2, a larger $\gamma$ also increases the variance of $X$ given $Z$, so the design does not isolate the failure of the control-function assumption.
10. **Accuracy** (breadth, D1–D4, pooled + structure):
    - Median in-sample error is 0.040, against 0.129 for the sieve-2SLS curve.
    - Out of sample, the error is 0.074 when the form is recovered, 0.85 when it is not, and 0.76 for the sieve curve.

<picture><source media="(prefers-color-scheme: dark)" srcset="experiments/phase4/fig_separation_dark.png"><img alt="Recovery given coverage against the penalty-adjusted separation margin, one point per cell. Cells with a positive margin mostly recover the law; cells with a negative margin mostly do not. The numbers are in experiments/phase4/summary.md, section 7." src="experiments/phase4/fig_separation_light.png"></picture>

### 12.4 Phase 5: simulations of the theory

Three experiments on the saved Phase 4 fronts, no new searches. Full tables: [`experiments/phase5/summary.md`](experiments/phase5/summary.md); details and interpretation: [THEORY.md §7.1](THEORY.md).

**Inference after selection (Theorem 1 (iii)).** For each breadth run, the law's own form and the formula selected by pooled candidates + BIC + structure (when it has the true form) were estimated by two-step GMM on 10 fresh samples and on the selection sample itself; 4,500 fits.

| | Constants covered (95% nominal) | $f$(median) | Elasticity | $J$ rejects (5%) | AR covers |
|---|---|---|---|---|---|
| D1–D4, selected tree, fresh samples | 92–98% | 94–95% | 92–94% | 3–7% | 93–97% |
| D1–D4, selected tree, same sample | 83–94% | 87–100% | 88–96% | 0–6% | 94–97% |
| D5 weak $Z$, true form, fresh samples | 76% | 68% | 64% | 10% | 97% |

- On independent samples, intervals, $J$ and AR sets are nominal, and the standard errors are calibrated.
- On the selection sample, coverage of the constants drops to 83–90% in D1–D3: the post-selection distortion that splitting avoids.
- Under the weak instrument, Wald intervals fail and AR sets do not, as the theorem says.

**Candidates from one sample, selection on another (Corollary 2.3).** D1 strong, the $n = 1000$ fronts, 12 seeds: wrong candidates that outscore the truth fall from 1.9 to 1.4 per run (power law) and from 0.4 to 0.1 (log law), and recovery at equal selection size rises by 10–25 points. But same-sample selection on the full $n = 2000$ with the structure term recovers more (67% vs. 47% for the power law, pooled), because halving the sample halves the separation. Splitting is the right tool for inference, not for selection.

**The identification diagnostic (THEORY.md Proposition 5; `symiv.identification`).** On every breadth run, with the pooled candidates and the BIC + structure selection, on the run's own data ($\tau = 0.2$):

| | Runs | Flagged as weakly identified or rejected | True form in the confidence set |
|---|---|---|---|
| D5 weak instrument, all runs | 60 | **100%** | 100% |
| D1–D4, form recovered | 123 | 4% | 99% |
| D1–D4, statistical failure | 29 | 45% | 100% |
| D1–D4, search failure | 76 | 57% | – |

- The method now reports weak identification on every D5 run instead of a formula: the median first-stage $F$ is 2, and the data allow formulas 0.7 sd away from the selected one (median of the farthest).
- Where the instrument is strong and the selection right, 4% of runs are flagged: the AR level.
- The confidence set covers the true form in 99% of the runs where it was a candidate (nominal $\ge 95\%$).
- It cannot detect a search failure whose wrong formula fits the moments: 43% of the search failures pass as identified, mostly D3 with the kink and saturation laws.

### 12.5 Phase 6: applications

**Simulated economic environments (§8.2).** 20 seeds per law, $n = 2000$; candidates from plain PySR, PySR distilled from a sieve-2SLS curve and the library path, pooled; selection by BIC + structure. Full table: [`experiments/phase6/summary.md`](experiments/phase6/summary.md).

| Environment | Law | Plain PySR, own pick: recovered / error | Pooled + BIC | **Pooled + BIC + structure** | Error: selected / oracle IV | Elasticity at the median: truth / selected | First-stage $F$ |
|---|---|---|---|---|---|---|---|
| Demand, D6 | $3p^{-0.5}$ | 0% / 0.43 | 95% | **100%** | 0.029 / 0.029 | −0.50 / −0.49 | 332 |
| Demand, D6 | $6 - 1.5\log p$ | 0% / 0.33 | 90% | **100%** | 0.024 / 0.024 | −0.62 / −0.62 | 338 |
| Demand, D6 | $6/(1 + p)$ | 0% / 0.57 | 65% | **70%** | 0.041 / 0.025 | −0.78 / −0.77 | 330 |
| Labour, $\pi = 0.5$ | $8w\,e^{-0.5w}$ | 0% / 0.42 | 60% | **75%** | 0.040 / 0.033 | 0.50 / 0.49 | 40 |
| Labour, $\pi = 0.5$ | $5 + 2\log w - 0.6(\log w)^2$ | 0% / 0.30 | 10% | **0%** | 0.347 / 0.051 | 0.40 / 0.29 | 40 |
| Labour, $\pi = 1$ (control) | $8w\,e^{-0.5w}$ | 60% / 0.21 | 75% | **75%** | 0.027 / 0.025 | 0.50 / 0.51 | 161 |
| Labour, $\pi = 1$ (control) | $5 + 0.5\log w - 0.6(\log w)^2$ | 10% / 0.37 | 20% | **20%** | 0.190 / 0.032 | 0.10 / 0.10 | 161 |

- **Demand curves are recovered.** With a cost shifter, the constant-elasticity and log-linear demand curves are recovered in every run, with the oracle's error and the right price elasticity; plain PySR never recovers them (its picks carry the simultaneity bias, errors 0.3–0.6 sd). The hyperbolic demand $6/(1 + p)$ is recovered in 70% of runs; the misses are near-duplicates such as $3.3p^{-0.74}$, with the elasticity still right.
- **Backward-bending labour supply exposes a limit.** With $\pi = 0.5$ only 7% of wages lie past the peak of the quadratic-in-logs law, and the law is never recovered: in 7 of the 9 runs where it was a candidate, a simpler wrong formula beat it (Theorem 2's separation channel), and the selected formulas are worse in sample than plain PySR's (0.35 vs. 0.30 sd). The hump law, whose peak sits inside the data, is recovered in 75% of runs with near-oracle error.
- **The control shows what identification needs.** With $\pi = 1$ and the quadratic's peak at the median wage, recovery rises only to 20%, and now every miss is a search failure: the 3-constant form was a candidate in just 20% of runs, and whenever it was, it was selected. The hump stays at 75%, again equal to its coverage. So for these shapes the binding constraint is the search's coverage of 3-constant forms, not selection.
- **What the identification diagnostic says.** Every demand run is "identified". The hump runs are "weakly identified" in 85% of cases at $\pi = 0.5$ and in 95% at $\pi = 1$, even where the form was recovered: candidates 0.2–0.4 sd away fit the moments as well as the truth (in one run better: $S = 3.5$ against 11.1), because a bump is a feature that the smoothing of $E[\cdot \mid Z]$ nearly erases. So the recovered hump is correct but not pinned down by the data, and the method says so. For the quadratic at $\pi = 0.5$, 45% of the wrong selections fail their own S test and another 30% are flagged as weakly identified; 25% pass as identified. Building this environment also exposed a weakness of the S test, a formula that misfits 2% of the sample badly inflates its own robust weight and escapes rejection, which is now handled by winsorizing the residuals inside the weight (THEORY.md §3.2).

**Engel curves (§8.3): the method reports shapes and tests, not a confident formula.** Blundell, Chen & Kristensen's FES 1995 sample (1,655 married couples; 628 without children, 1,027 with; `experiments/phase6_engel.py`; full output in [experiments/phase6/engel.md](experiments/phase6/engel.md)): budget share on log total expenditure, instrumented by the head's log earnings ($K = 9$–$12$ spline instruments; first-stage $F$ = 31–59). Candidates from plain PySR, distillation, the library path and the template library, pooled; selection by BIC + structure; then the identification report, and the S tests of the Working–Leser (linear in log expenditure) and quadratic forms with an AR interval for the quadratic term. On synthetic FES-like data with a planted Working–Leser share the same pipeline recovers `0.452 − 0.060 log x` from `0.45 − 0.06 log x` and reports "identified".

| Share | Selected, all couples | Shape | Verdict: all / no children / with children | Working–Leser rejected | Quadratic term's AR interval excludes 0 |
|---|---|---|---|---|---|
| food | `0.747^x` (share ∝ expenditure$^{-0.29}$) | decreasing | weak / weak / weak | no / no / no | no / no / no |
| catering | constant 0.080 | flat | weak / weak / weak | no / no / no | no / no / no |
| alcohol | `0.19 − 0.025 log x` (a template) | decreasing | weak / weak / weak | no / no / no | no / no / no |
| fuel | `(log x)^{-5.3}` | decreasing | weak / weak / weak | no / no / at the margin (18.4 vs 18.3) | no / no / at the margin ([0.000, 0.084]) |
| motor | `0.693^x`; within the confidence set: `0.025 / max(0.17, x − 5.74)` | decreasing | **rejected** / weak / **rejected** | **yes** / no / **yes** | **yes** / **yes** / **yes** |
| fares | constant 0.015; within the set: `0.0028 x` | flat | **rejected** / weak / weak | no / no / no | no / no / no |
| leisure | `0.00051 e^x` (share ∝ expenditure) | increasing | weak / weak / weak | no / no / no | no / no / no |

- **The known answers hold.** The food share is compatible with Working–Leser in all three samples: the linear-in-log-expenditure form is never rejected and the quadratic term's AR interval always contains zero. The motor share needs a quadratic term: its AR interval excludes zero in all three samples and the Working–Leser form is rejected in two, the case Banks, Blundell & Lewbel (1997) make for some goods. Fuel sits at the margin in the with-children sample. Leisure is a luxury (increasing), food and fuel necessities (decreasing); catering and fares are flat within the data's power.
- **No share is "identified".** With 628–1,655 households and shares whose noise dwarfs their structural variation, 24–40 candidates per share pass the S test, up to 0.25–2.8 sd of the selected curve apart; the report lists them instead of claiming one formula. The selection itself fails its own S test three times (motor twice, fares once); the pick restricted to the confidence set is then reported, a kinked hyperbola for motor and a line through the origin for fares.
- **Plain PySR's own pick coincides with the IV selection** for food, fuel and motor in the full sample (`0.747^x`, `0.60^x`, `0.69^x`): on these data the conditional-mean and the structural shapes are close in the bulk of the sample, so the instrument's work shows in the tests and the set, not in the pick. The templates changed one pick (alcohol, all couples: the Working–Leser template replaced a quadratic in the level of log expenditure).
- Cost: 21 runs in about 45 minutes, searches included.

**Angrist–Krueger (1991) stress test (§8.3): the method reports weak identification, as it should.** 329,509 men born 1930–39; log weekly wage demeaned within birth year; schooling instrumented by quarter of birth (`experiments/phase6_ak.py`; full output in [experiments/phase6/ak.md](experiments/phase6/ak.md)).
- *Replication.* With the 30 within-cohort quarter-of-birth contrasts (AK's Table V), the first-stage $F$ is 4.9 (Bound, Jaeger & Baker report 4.7–4.9), the OLS return 0.071 and the 2SLS return 0.089 (AK: 0.071 and 0.089). With the 3 overall contrasts, $F = 34$ and 2SLS gives 0.103.
- *Selection.* Both instrument sets select `log(0.075 (s + 1))`, a concave return profile (0.10 per year at 9 years of schooling, 0.07 at 13, 0.06 at 17), which is also plain PySR's own pick: the moments do not move the formula away from the conditional-mean shape.
- *The diagnostic says "weakly identified" with both sets.* Every other candidate survives its S test (25 of 25 with 30 instruments; 23 of 23 with 3), the farthest 1.1–1.3 sd from the selected formula. The identification-robust AR interval for the linear return is $[-0.01, 0.44]$ against the Wald interval $[0.06, 0.16]$ with 30 instruments, and $[-0.01, 0.26]$ against $[0.03, 0.18]$ with 3: 2–5 times wider, and including zero. With 3 instruments ($K = 4$) any formula with four constants fits the moments exactly (Proposition 4); with 30, the compulsory-schooling variation is too small to tell shapes apart. A confident formula would have been wrong here; the method does not give one.
- The sieve-2SLS curve shows the NPIV instability the plan anticipated: with 3 instruments it moves by $-1.0$ log points between 8 and 12 years and by $+2.5$ between 12 and 16.

### 12.6 Before the paper: search budget and templates (in progress)

The cells where the Phase 2–6 search rarely proposed the law (§11, "Before the paper"): D1 and D3 × the kink and saturation laws (seeds 0–11, paired with the Phase 4 runs) and the two quadratic labour-supply laws (seeds 0–19, paired with Phase 6). Four arms per run: the base budget (40 iterations, size ≤ 15, from the saved fronts), base + the template library (`symiv.templates`: 11 textbook shapes with free constants, scored like any candidate), a large budget (200 iterations, 40 populations, size ≤ 25, two restarts pooled), and large + templates. Plain PySR and distillation only, plus the library path; the one-step front is left out so the arms compare. Script `experiments/phase7_budget.py`; tables in [experiments/phase7/budget.md](experiments/phase7/budget.md). **The large-budget searches run after the seeds job; the base arms are done:**

| Cell | Law | Base: coverage → recovery | Base + templates: coverage → recovery |
|---|---|---|---|
| D1 | $x - 0.8\max(x - 1.5, 0)$ | 0% → 0% | 100% → **0%** |
| D1 | $3x/(1 + x)$ | 50% → 42% | 100% → **67%** (+3 / −0) |
| D3 | $x - 0.8\max(x - 1.5, 0)$ | 0% → 0% | 100% → **0%** |
| D3 | $3x/(1 + x)$ | 25% → 0% | 100% → 8% |
| Labour, $\pi = 0.5$ | $5 + 2\log w - 0.6(\log w)^2$ | 45% → 0% | 100% → **0%** |

- **Templates solve coverage and expose separation.** With the true form guaranteed to be a candidate, the kink law is still never selected: a one- or two-constant formula such as $x^{0.54}$ beats the three-constant kink under BIC + structure, because the moments barely distinguish them (the kink pays about 22 more in penalty than $x^{c}$ and gains less than that in $J$). In D3 only 6% of the regressor's mass lies past the kink, and the identity $x$ wins 6 of 12 runs. The quadratic labour law at $\pi = 0.5$ loses the same way (Theorem 2's channel (I)). The saturation law, whose shape the moments do see, gains: 42% → 67% in D1.
- So for the threshold and quadratic laws at $n = 2000$ the binding constraint is separation, not search; a larger budget cannot fix it, and the paper should say so. Whether the large budget raises coverage without templates, and whether it helps the saturation law, is what the running arm will show.

## 13. Code

```
src/symiv/
  dgp/            laws and designs D1-D6 (§8.1, §8.2)
  criteria/       instrument bases, Nystrom features, the criterion ||A'r||^2 / n (§6.2)
  gmm.py          two-step GMM refit with bounded constants; Hansen's J (§6.3)
  selection.py    MMSC selection over the Pareto front; least-squares selection for plain SR (§6.3)
  recovery.py     form recovery and SRBench's SymPy check (§8.1)
  metrics.py      function, extrapolation and elasticity errors; implied constants (§8.1)
  diagnostics.py  success / search failure / statistical failure (§7)
  identification.py  after selection: first-stage F, AR intervals, the formula confidence set and a verdict (§6.4)
  templates.py    a fixed library of 11 economic shapes, scored as candidates like any formula (§11, §12.6)
  search.py       PySR wrappers; the loss is julia/moment_loss.jl (§6.6)
  baselines/      Phase 3: fixed_form (oracle and wrong-form IV), npiv (sieve 2SLS, KIV), deepiv (torch),
                  library_iv, distill (NPIV -> PySR), control_function (template SR), srit (SRIT-style)
experiments/
  smoke_pysr.py   one end-to-end run, plain PySR vs. symbolic IV
  phase2.py       Phase 2 Monte Carlo (resumable); phase2_report.py writes phase2/summary.md
  phase3.py       Phase 3 baselines (resumable, shardable); phase3_report.py writes phase3/summary.md
  phase4.py       Phase 4 searches: saves every Pareto front (grids breadth, nscale, nomax, cf, headline; resumable, shardable)
  phase4_analysis.py  selection rules and metrics on the saved fronts (pure Python, parallel); --separation for §7
  phase4_report.py    phase4/summary.md and figures (matplotlib, light and dark)
  phase5_inference.py Phase 5: inference after selection on fresh samples (Theorem 1 (iii)); reuses the Phase 4 fronts
  phase5_split.py     Phase 5: candidates from one sample, selection on another (Corollary 2.3)
  phase5_identification.py  Phase 5: the identification diagnostic on every Phase 4 breadth run (Proposition 5)
  phase5_discrete.py  Phase 5: a four-constant formula against four moments in D4 (Proposition 4); writes phase5/discrete.md
  phase5_report.py    phase5/summary.md
  phase6_simulated.py Phase 6: demand with a cost shifter (D6) and backward-bending labour supply (§8.2): search, analysis, report
  phase6_ak.py        Phase 6: the Angrist–Krueger stress test on the 1980 census extract (§8.3)
  phase6_engel.py     Phase 6: Engel curves on the FES 1995 extract, 7 shares x 3 subsamples; --synthetic runs a self-test (§8.3)
  phase7_budget.py    Before the paper: a larger search budget and the template library on the 3-constant and threshold laws (§12.6)
  fetch_data.py       downloads the two public application files into data/ (§8.3)
  phase2/ ... phase7/  one JSON record per run, and summary.md
tests/            pytest; `pytest -m julia` runs the PySR tests, `pytest -m slow` the DeepIV test
THEORY.md         Phase 5: assumptions, theorems and proofs (§7)
data/             third-party application data, downloaded by fetch_data.py and git-ignored: ak91.dta, engel95.csv (§8.3)
```

**Setup** (tested with Python 3.12, PySR 2.6.0, SymbolicRegression.jl 2.5.1, Julia 1.11.9, Windows 11):

```
python -m venv .venv
.venv\Scripts\activate            # Windows; elsewhere: source .venv/bin/activate
pip install -e ".[search,dev]"   # add "deep" for DeepIV (torch; CPU wheel: --index-url https://download.pytorch.org/whl/cpu)
python -c "import pysr"           # first run installs Julia and SymbolicRegression.jl (several minutes)
pytest                            # pure-Python tests, seconds
pytest -m julia                   # PySR integration, about a minute
python experiments/smoke_pysr.py --design D1 --law power --n 2000
python experiments/phase2.py --part main          # about 2 hours; then --part sensitivity (about 45 min)
python experiments/phase2_report.py
python experiments/phase3.py --shard 0 --of 2     # and --shard 1 --of 2 in parallel, each with
                                                  # PYTHON_JULIACALL_THREADS=4; about 4 hours of wall time
python experiments/phase3_report.py
python experiments/phase4.py --grid breadth nscale nomax cf --shard 0 --of 2   # and --shard 1 --of 2 in parallel,
                                                  # each with PYTHON_JULIACALL_THREADS=4; about 6 hours of wall time
python experiments/phase4_analysis.py --workers 8               # about 1 hour
python experiments/phase4_analysis.py --separation --workers 8  # about 10 minutes
python experiments/phase4_report.py
python experiments/phase5_inference.py --workers 8  # minutes; then phase5_split.py and phase5_report.py
python experiments/phase5_identification.py --workers 8; python experiments/phase5_report.py
python experiments/phase6_simulated.py --part search; then --part analyze --workers 8; --part report   # about 1 hour
python experiments/fetch_data.py                  # ak91.dta and engel95.csv into data/ (needs ".[apps]")
python experiments/phase6_ak.py; python experiments/phase6_engel.py --data data/engel95.csv            # about 2 hours
python experiments/phase4.py --grid headline      # the paper's cells to 50 seeds: about 15 hours; then phase4_analysis.py,
                                                  # phase4_report.py, phase5_identification.py, phase5_report.py
python experiments/phase7_budget.py --part search; then --part analyze --workers 8; --part report      # about 6 hours
```

Phase 4 runs for longer than a terminal session should be trusted with. On Windows, start each search as a detached process with logs, e.g. `Start-Process .venv\Scripts\python.exe -ArgumentList "-u","experiments\phase4.py",... -WindowStyle Hidden -RedirectStandardOutput experiments\phase4\logs\search-0.out.log -RedirectStandardError experiments\phase4\logs\search-0.err.log`; elsewhere use `nohup ... &`. Every script skips finished runs, so an interrupted job resumes where it stopped. `logs/` is git-ignored.

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
- Zeiringer, T., Garnier, H. & Horn, M. (2026). Instrumental variable framework for nonlinear continuous-time system identification. *J. Franklin Institute*, 363(7), 108619. https://doi.org/10.1016/j.jfranklin.2026.108619
- Li, R., Feng, Q. & Cui, Y. (2026). Causally guided symbolic regression for basin-scale water balance change in the China–Mongolia arid region. *J. Hydrology: Regional Studies*, 65, 103355. https://doi.org/10.1016/j.ejrh.2026.103355
