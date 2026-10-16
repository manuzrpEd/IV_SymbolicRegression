# Report of the Lean 4 check (first run 2026-10-15; second run 2026-10-16)

Toolchain: Lean 4.35.0, Mathlib v4.35.0 (`lean-toolchain`, `lake-manifest.json`). `lake build` of the
library `SymbolicIV` (14 modules, 4,762 lines) completed successfully in about two minutes after the Mathlib
cache download; no file contains `sorry`, `axiom`, `native_decide` or `unsafe`; all 100 `#print axioms` lines
in the build log list only `propext`, `Classical.choice`, `Quot.sound`. Remaining compiler output is style
only (two over-long lines; Mathlib's note that the files do not use the module system). The second run
(2026-10-16) added U15 (`Thm2Conditioning.lean`), the lemmas `prop4b_restated` and `prop4b_restated_fin`
to U10, and a general codomain for U14's statistic: 15 modules, about 5,030 lines, 110 `#print axioms`
lines, all standard, and `lake build` succeeds. Its findings about the paper are recorded in THEORY.md §9
(fifth pass).

How the run was organized: for each unit of [FORMALIZATION_PLAN.md](FORMALIZATION_PLAN.md) one agent wrote
the file and compiled it; a second, independent agent then tried to show that the Lean statement is not the
paper's (stronger hypotheses, weaker conclusion, trivializing definitions), recompiled, and recorded a
verdict; a repair round was available but no unit needed it. The mathematics is
[THEORY.md](../THEORY.md); the paper ([paper/](../paper/)) has the same numbering with ν, U, μ for the
file's ρ, Z, m.

Rule applied throughout: the probabilistic tools that Mathlib does not provide (the matrix Bernstein
inequality, the Hsu–Kakade–Zhang quadratic-form inequality, McDiarmid's inequality, the central limit
theorem, Slutsky's lemma) are never re-proved; their conclusions enter as named hypotheses. What Lean
checks is the paper's reasoning from those tools onward.

## Status

| Unit | File | Result | Verdict | Compiles | sorry-free | Axioms |
|---|---|---|---|---|---|---|
| U01 | `Prop21.lean` | Proposition 2.1, deterministic core | faithful | yes | yes | standard |
| U02 | `Prop24.lean` | Proposition 2.4, perturbed weights | faithful | yes | yes | standard |
| U03 | `Thm2Assembly.lean` | Theorem 2, assembly of the five events | faithful | yes | yes | standard |
| U04 | `Cor22.lean` | Corollary 2.2 algebra; tree-count arithmetic | faithful | yes | yes | standard |
| U05 | `Lemma1.lean` | Lemma 1 | faithful | yes | yes | standard |
| U06 | `Thm1.lean` | Theorem 1 (deterministic core and the in-probability statement) | faithful with extra hypotheses | yes | yes | standard |
| U07 | `Thm3a.lean` | Theorem 3(a) | faithful | yes | yes | standard |
| U08 | `Thm3b.lean` | Theorem 3(b): Steps 1, 3, 4, the Step 2 algebra, Δ_n(t) → 0 | faithful | yes | yes | standard |
| U09 | `Lemma4a.lean` | Lemma 4(a) | faithful | yes | yes | standard |
| U10 | `Prop4.lean` | Proposition 4 | faithful with extra hypotheses | yes | yes | standard |
| U11 | `Prop33Prop5.lean` | Proposition 3.3; Proposition 5 event logic and (c) | faithful | yes | yes | standard |
| U12 | `TreeCount.lean` | Tree count | faithful | yes | yes | standard |
| U13 | `Lemma3Algebra.lean` | Lemma 3 constants; Corollary 2.5 sandwich; trace bounds | faithful | yes | yes | standard |
| U14 | `Thm1iiiSelected.lean` | Theorem 1(iii), selected-tree step | faithful | yes | yes | standard |
| U15 | `Thm2Conditioning.lean` | Theorem 2, the conditioning clause: Lemma 3(b),(d) integrated on the event of (a), five events assembled (second run, 2026-10-16) | faithful with extra hypotheses (measurability of the events; the a.e. form of the conditional bound) | yes | yes | standard |

## What the formalization says about the paper

Classification: (a) error in a statement or proof as written; (b) missing hypothesis or gap; (c)
formalization detail with no bearing on the paper. Line numbers refer to THEORY.md before the fourth-pass
edits of 2026-10-15; every item marked "fixed" is now changed in THEORY.md and in the paper's sources on the
AfterDraft branch.

1. **(b) Theorem 3(a), statement** (line 528). Step 1 of the proof concludes Q(f̂) ≤ Q* + 2R_n + o_p(1) from
   Q̂_ŝ ≤ Q_n(f*) + σ̂² max_s pen_n(s)/n, which needs σ̂² = O_p(1) in addition to κ_n/n → 0; the statement
   listed only (A3), (C2), continuity of Q and κ_n/n → 0, while Theorem 3(b) had the condition in (S6).
   Fixed: added to the statement and the proof. (U07; Lean takes the slack as a sequence η'_n →_p 0.)
2. **(a) Proposition 4(b), statement** (line 509). With f₀ fixed before r, the conclusion "there is r > 0
   such that ‖m(f_s(·;θ̄) − f₀)‖ < r implies m(f_s(·;θ) − f₀) = 0 for some θ" is true for every map and
   every θ̄, with no C¹ or rank hypothesis (`prop4b_statement_trivial`): if the value is nonzero, take r
   below its norm. The Lyusternik–Graves argument proves the informative statement, in which r depends on
   the tree, θ̄ and Θ_s and is chosen before f₀ (`prop4b_ball_subset_image`, `prop4b`, `prop4b_fin`).
   Fixed: restated with that quantifier order, in THEORY.md and in theory.tex, with the proof adjusted.
   Nothing downstream changes: the use of Proposition 4 (formulas with J or more constants cannot be
   excluded by the moments; the Angrist–Krueger discussion) rests on the corrected reading.
3. **(b) Proposition 2.1 (II) and Proposition 2.4** (lines 332, 345, 480). The step "(II) forces π_s > 0"
   needs d_s^loc ≥ 0. The definition "any bound d_s^loc ≥ sup_{θ∈Θ_s(r)} ‖E_s(θ)‖" gives this only when the
   localized set is nonempty; when it is empty the supremum is over the empty set and a negative d_s^loc is
   formally admissible, and a one-dimensional counterexample to (II) then exists (Z = 1, G = −2.01, E = 0,
   dloc = −1, π = −1). Theorem 2's explicit d^loc_{s,t} is nonnegative, so nothing downstream is affected.
   Fixed: "any bound d_s^loc ≥ 0 with ...". (U01, U02.)
4. **(b) Theorem 1, statement** (lines 151, 160, 172). The proof uses Q_n ≥ 0 ("since Q̂_s ≥ 0") and
   pen_n ≥ 0 ("penalties are nonnegative", "crit_n(s) ≥ nQ̂_s/σ̂²"), i.e. κ_n ≥ 0, w ≥ 0, log m ≥ 0;
   (C1) states nonnegativity only for the population Q, and κ_n → ∞ gives κ_n ≥ 0 only for large n
   (HQIC is negative at n = 2). The asymptotic conclusion is unaffected. Fixed: "a nonnegative
   criterion Q_n" and "κ_n ≥ 0" in the statement. (U06.)
5. **(c) Theorem 2, proof** (lines 413–421). Lemma 3(b) and (d) are conditional on Z_{1:n} on the event of
   (a); the five-event count 5e^{−t} is right because their failure events are taken within (a) and
   integrated (tower property), which the text did not say; and ŝ is undefined when Ŝ is empty, which is
   harmless because such samples lie in the search-failure event. Fixed: one clause for each. (U03; Lean
   takes the five unconditional failure probabilities as hypotheses, so the tower-property step itself is
   outside what was checked.)
6. **(c) Wording, all fixed.** (A3) now says the formulas and the envelope are measurable (U05). Lemma 1(b)
   uses the continuity of T, not ‖T‖ ≤ 1 (U05). Theorem 3(b), Step 1: the net argument gives 2δ, not 3δ;
   Step 2's Δ_n(t) → 0 uses L_n ≥ 1 and Λ_n ≥ 1 without loss of generality (U08). Lemma 4(a): the
   interpolant is Λ₀-Lipschitz on each subinterval and, being continuous, on the whole support (the gluing
   step was missing from the sketch); "knots" meant subintervals in the count k = ⌊(L+3)/8⌋ (U09).
   Proposition 4(a): rank J makes Ψθ = m(f₀) solvable in ℝ^p for every f₀, the assumption is that a
   solution lies in Θ_s; the hypotheses "p ≥ J" and "rank J" were not used by the proof (U10).
   AR_s(θ) := +∞ where Ω̂_s(θ) is singular (U11). Proposition 3.3 states inf ∅ = +∞, which is what makes
   the generalized inverse finite (U11). Theorem 1(iii), step 2: φ is on ℝ^{p₀}, S_B(s) takes a fixed value
   off S₀^min, and the tail term also uses |E φ(N)| ≤ ‖φ‖_∞ (U14).
7. **(c) Confirmed as written, no change.** Every explicit constant of Lemma 3 (the Bernstein solution
   ε_n(t), the assembly of z_t², McDiarmid's constant, the covering count and the sum of the three terms)
   and the factor 2K (U13); the sharp sandwich constants (1+ε)⁻¹, (1−ε)⁻¹ of Corollary 2.5, obtained
   without the spectral theorem (U13); the algebra and the weighted union bound of Corollary 2.2, including
   that ε_n(t) rightly stays at the fixed level t (U04); the five-event count of Theorem 2 (U03); the
   constants of Lemma 4(a), with L ≥ 8 used exactly where 4/(L−4) ≤ 8/L needs it (U09); Proposition 2.4's
   constants, with no symmetry of Ŵ needed (U02); the tree count, which holds for every m (U12).

## What each file proves, and what it assumes beyond the paper

- **U01 `Prop21.lean`.** Conditions (I) and (II) of Proposition 2.1 pointwise in θ (`condI`, `condII`),
  W ≥ 0 and W ≤ ‖Z‖, the projection bound W ≤ ‖P_V Z‖ for any subspace with an orthogonal projection
  containing the directions, the passage from a strict pointwise inequality to the attained minimum on a
  compact Θ, the reduction to the criteria, and the assembled `prop21_I`, `prop21_II`, `prop21_II_proj`.
  Added: 0 ≤ dloc (item 3 above); compactness, nonemptiness of Θ and continuity of G, E for the attained
  minimum (the paper's own step). z ≥ 0 and d ≥ 0 were not needed.
- **U02 `Prop24.lean`.** (I′) and (II′) pointwise, the reduction (4.2), the criterion comparison, and the
  assembled statement for q x = ⟪x, A x⟫. Added: 0 ≤ dloc; the sandwich as bounds on the quadratic form
  (the paper's λ∓σ⁻²I after absorbing σ²). Symmetry of Ŵ was not needed.
- **U03 `Thm2Assembly.lean`.** On the intersection of the five events with coverage, ŝ ∈ S₀^min;
  P(ŝ ∉ S₀^min) ≤ 5e^{−t} + P(no coverage) (ℝ≥0∞ and real versions); the tree-specific union bound and the
  identity for the common level t_L; the tree-specific version of the theorem. Assumed: the separation that
  Proposition 2.1 delivers on the intersection (U01's output), the five failure probabilities ≤ e^{−t}, ŝ
  minimizing over a nonempty Ŝ; measurability only for the phrase "probability at least 1 − 5e^{−t}".
- **U04 `Cor22.lean`.** Weighted union bound ≤ 1; Σ e^{−t_s} ≤ e^{−t}; the expansion of (II) through
  2√(kt) ≤ k + t; the cancellation condition; the tree-count arithmetic Σ_{k≤L}(3m)^k ≤ 2(3m)^L and its
  logarithm. Added only sign conventions (m ≥ 1 or ≥ 2 where the paper says log m > 0, L ≥ 1, k, t ≥ 0).
- **U05 `Lemma1.lean`.** Compactness of each range and of F_L; positive separation for wrong trees and a
  common δ_L; positivity of ω_L(ε). Stretch done: with Mathlib's `Lp`, pointwise continuity in θ with a
  square-integrable envelope gives continuity into L²(P_X) and compactness of the range (needs first
  countability of Θ, a finite measure, and measurability of each f_s(·;θ)). Only continuity of T is used.
- **U06 `Thm1.lean`.** Display (3.1); Q̂_ŝ ≤ Q_n(f₀) + σ̂² pen(s*)/n; Q(f̂) ≤ that + R; the deterministic
  core of (ii) (ŝ ∈ S₀^min under explicit sufficient conditions) and the sufficient form
  κ − wL log m > nQ_n(f₀)/σ̂²; both stretch goals: P(ŝ_n ∉ S₀^min) → 0 and P(‖f̂_n − f₀‖ ≥ ε) → 0 from
  R_n →_p 0, nQ_n(f₀) = O_p(1), σ̂² →_p σ*² > 0, κ_n → ∞, κ_n/n → 0 and coverage → 1, through a
  four-event union bound. Added: κ_n ≥ 0 for all n, 1 ≤ m, Q̂_s ≥ 0, Q_n(f₀) ≥ 0 (item 4); the identification
  gap η(ε) > 0 of Lemma 1 as a hypothesis (not re-proved in this file).
- **U07 `Thm3a.lean`.** F* nonempty and compact; the gap inf{Q(f) : dist(f, F*) ≥ ε} > Q*; the basic
  inequality; the in-probability wrapper and an end-to-end `theorem3a`. Assumed: the argmin inequality on
  the good event with a slack η'_n →_p 0 (item 1), (C2) as a uniform bound R_n →_p 0, f̂_n ∈ F.
- **U08 `Thm3b.lean`.** ω(ε) > 0 (for a nonempty constraint set), uniform strong convergence of the
  projections on the compact image, Step 1 with the paper's ½√ω(ε) and ω(ε)/4 (abstract projections, and
  orthogonal projections onto subspaces), the Step 2 algebra, Steps 3 and 4, the deterministic and
  in-probability assemblies, and the stretch Δ_n(t) → 0 under (S6) with explicit constants. Assumed:
  |Q_n − Q_{K_n}| ≤ R_n at f̂_n and f*_n (Step 2's probabilistic bound), near-minimization at f*_n, and
  for Δ_n: Λ_n ≥ 1 and the sign conventions.
- **U09 `Lemma4a.lean`.** Interpolation error 2λ(1−λ)Λ₀h ≤ Λ₀h/2; sup-norm error Λ₀(x_hi − x_lo)/(2k);
  the interpolant bounded by A and Λ₀-Lipschitz on the support; the hinge representation with the four
  constant bounds; k = ⌊(L+3)/8⌋ ≥ (L−4)/8 and the final bound for L ≥ 8; the stretch node count
  5 + 8(k−1) on an expression-tree type (`lemma4a_tree`). Added: x_lo < x_hi.
- **U10 `Prop4.lean`.** (a) for an arbitrary linear moment map, plus solvability in ℝ^p under rank J;
  (b) the ball inclusion and the implication, in general complete normed spaces and for ℝ^p → ℝ^J with the
  literal matrix rank, through `ContDiffAt.hasStrictFDerivAt` and `HasStrictFDerivAt.map_nhds_eq_of_surj`;
  and `prop4b_statement_trivial` (item 2). The hypothesis "s wrong" is not needed for (b) and is omitted.
- **U11 `Prop33Prop5.lean`.** Proposition 3.3 in EReal (no boundedness needed) and in ℝ (with
  BddAbove); S_{s₀} ≤ AR_{s₀}(θ₀) and the event inclusions of 5(a) and 5(b) with their probability and
  limsup bounds (the χ²_K limit entering as limsup P(AR > c) ≤ α); for 5(c), ⟪x, Ω̂⁻¹x⟫ ≥ ‖x‖²/‖Ω̂‖ by a
  Cauchy–Schwarz argument, ‖Ω̂‖ ≤ B_n, and ‖ĝ‖² ≤ cB_n/n; the stretch inequalities ξ'Aξ ≥ ξ'ξ and
  ξ'Aξ ≤ ‖A‖ξ'ξ for the winsorized weight (the identification ‖A‖ = 1/λ_min(Ω_cΩ⁻¹) was not attempted).
  Added: AR ≥ 0, ĝ in the range of Ω̂ (the paper's implicit invertibility).
- **U12 `TreeCount.lean`.** An inductive type of labelled unary-binary trees; `Nat.card {t // size t = ℓ}
  ≤ (3m)^ℓ` by injection into Łukasiewicz words; the bound for size ≤ L and its logarithm, for every m.
- **U13 `Lemma3Algebra.lean`.** The Bernstein solution and the tail at level ε_n(t); the z_t² assembly and
  its Lemma 3(d) variant; McDiarmid's constant, the one-centre bound, the union bound over
  (1 + 2CΛ√n/M′)^p centres and the sum of the three terms; existence of the inverse of Σ̂ and the sharp
  sandwich of Corollary 2.5; the stretch trace bounds tr Σ̂ ≤ K(1+ε), tr Σ̂² ≤ K(1+ε)², tr(P_VΣ̂) ≤ k‖Σ̂‖,
  tr((P_VΣ̂P_V)²) ≤ k‖Σ̂‖². Tropp's and McDiarmid's inequalities enter as hypotheses on tail functions.
- **U15 `Thm2Conditioning.lean`** (second run). The conditional bounds of Lemma 3(b) and (d), holding
  a.e. on the event of (a), integrate to the same e^{−t} (`condProb_bound_integrates`, by the tower
  property in set-integral form); the five events assemble into probability at least 1 − 5e^{−t}
  (`five_events`), in the form `Thm2Assembly.prob_not_mem_le` consumes (`five_events_for_assembly`).
  Added: measurability of the events (the event of (a) with respect to σ(Z_{1:n})) and the a.e. form
  of the conditional bound. The conditional union bound over trees that produces the aggregate event
  (d) is taken as given.
- **U14 `Thm1iiiSelected.lean`.** The selected-tree inequality from the independence of the A and B
  σ-algebras, finiteness of the tree set and boundedness of φ (`selected_tree_bound`). Added: |c| ≤ ‖φ‖_∞
  for the constant c = E φ(N) (automatic in the paper, necessary once c is arbitrary).

## What remains unverified by Lean

- The probabilistic tools themselves: Tropp's matrix Bernstein inequality, the Hsu–Kakade–Zhang
  inequality, McDiarmid's inequality, the central limit theorem and Slutsky's lemma, the uniform law of large
  numbers of Lemma 2, and the GMM asymptotics of Newey and McFadden used by Corollary 1.1 and Theorem 1(iii).
- Lemma 2 (the two criteria satisfy (C1)–(C3)), Corollary 1.1, the asymptotic parts of Theorem 1(iii) and
  of Proposition 5(a), the two guards of Proposition 5 (sample envelope, winsorized weight) beyond the two
  matrix inequalities, and Lemma 4(b) (Bernstein polynomials). The tower-property clause of Theorem 2's proof, unverified in the first run, is U15 (second run).
- The paper's numerical paragraph ("Numbers" after Corollary 2.2) was recomputed in floating point, not in
  Lean: ε_n(3) = 0.314, log(3m)/log m = 1.477, w ≈ 5.8, wℓ̄₀ log m ≈ 80, the 15-node term ≈ 201, the
  channel-(I) terms 40.2 and 3.45, consistent with the paper's rounded figures (5.8, 80, 201, 40, 3.5).
