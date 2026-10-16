# Formalization plan

Source of truth for every statement: [THEORY.md](../THEORY.md) (section and line numbers below refer to
it) and, with the same numbering and slightly different notation, the paper's
[theory.tex](../paper/sections/theory.tex) and [appendix-proofs.tex](../paper/sections/appendix-proofs.tex).
The paper writes ν for the variance ratio ρ := σ̄²/σ² of Setting (F), U for the moment-noise vector
Z := √n ū/σ, and μ(h) for the conditional-moment map m(h). THEORY.md's symbols are used below.

Each unit is one Lean file `SymbolicIV/<File>.lean`, self-contained (`import Mathlib` only). "Required"
is what the file must prove; "Stretch" is proved if time allows and otherwise stated as a hypothesis and
reported. Probabilistic tools absent from Mathlib (matrix Bernstein, Hsu–Kakade–Zhang, McDiarmid, CLT,
Slutsky) are never re-proved: their conclusions enter as hypotheses.

General modelling conventions (so that files agree):
- The instrument space is a real finite-dimensional inner product space `E` (for instance
  `EuclideanSpace ℝ (Fin K)`), or an arbitrary `[NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]` when nothing depends on K.
- A parameter set Θ_s is a compact set in `EuclideanSpace ℝ (Fin p)` or an abstract compact topological
  space; use whichever makes the statement cleanest, but keep compactness where the paper uses it.
- The function space L²(P_X) is an abstract real inner product space (or normed space) `H`; T is a
  continuous linear map `H →L[ℝ] H'` with `‖T‖ ≤ 1` where the paper uses that bound.
- "n" is a natural number > 0 cast to ℝ where it appears in constants.

---

## U01 Proposition 2.1, the deterministic core (THEORY.md §4, lines 322–363)

File `Prop21.lean`. Abstract setting: `E` a real inner product space; `Z : E`; `Θ` a nonempty compact
topological space; `G E_ : Θ → E` continuous; reals `z d ≥ 0` with `‖Z‖ ≤ z` and `‖E_ θ‖ ≤ d` for all θ;
`π : ℝ` (the penalty gap).

Required:
1. (I) If `a > 2z + d + √(max (−π) 0)` and `‖G θ‖ ≥ a` for all θ, then for all θ,
   `‖Z + G θ + E_ θ‖^2 > ‖Z‖^2 − π`.
2. (II) With `r := 2z + d`, the localized set `Θloc := {θ | ‖G θ‖ ≤ r}`, the directions
   `D := {G θ / ‖G θ‖ | θ ∈ Θloc, G θ ≠ 0}`, `W := ⨆ v ∈ D, max ⟪−Z, v⟫ 0` (0 if D is empty; W is
   bounded by ‖Z‖), and any `dloc ≥ 0` with `‖E_ θ‖ ≤ dloc` for all θ ∈ Θloc: if `π > W^2 + 2 z dloc`
   then for all θ, `‖Z + G θ + E_ θ‖^2 > ‖Z‖^2 − π`. Follow the paper's proof: outside Θloc the
   reverse triangle inequality; inside, `‖Z + G‖^2 ≥ ‖Z‖^2 − (max ⟪−Z,v⟫ 0)^2 ≥ ‖Z‖^2 − W^2`,
   then `a := √(max (‖Z‖^2 − W^2) 0) ≤ ‖Z‖ ≤ z`, `Δ := ‖E_ θ‖ ≤ dloc`, and
   `(max (a − Δ) 0)^2 ≥ a^2 − 2aΔ`.
3. The projection bound: if `V` is a finite-dimensional subspace containing D and `P_V` the orthogonal
   projection, then `W ≤ ‖P_V Z‖`.
4. The reduction to criteria: for reals `Jstar ≤ ‖Z‖^2`, `penstar ≤ penbar`, and `J` with
   `J > ‖Z‖^2 − (pen − penbar)`, conclude `J + pen > Jstar + penstar`. And: if the strict inequality of
   1 or 2 holds at every θ and the minimum of `θ ↦ ‖Z + G θ + E_ θ‖^2` is attained (compactness and
   continuity), then the minimum value exceeds `‖Z‖^2 − π`.

Stretch: none. Note for the verifier: in the paper `G θ = √n g(s,θ)/σ`, `a = √(n δ_s)/σ` with
`δ_s = min_θ ‖g(s,θ)‖^2`, so `‖G θ‖ ≥ a` for all θ is exactly the paper's situation.

## U02 Proposition 2.4, perturbed weights (THEORY.md §4, lines 466–486)

File `Prop24.lean`. Same abstract setting as U01, plus a quadratic form `q : E → ℝ`, `q x = ⟪x, A x⟫`
for a self-adjoint `A`, with `λm ‖x‖^2 ≤ q x ≤ λp ‖x‖^2` for all x, `0 < λm ≤ λp` (this is the
paper's sandwich after absorbing σ²: n ĝ'Ŵĝ = σ² x'Ŵx with x = √n ĝ/σ).

Required: with the localization radius `r' := z (1 + √(λp/λm)) + d` in place of r in Θloc, D, W, dloc,
if either (I′) `a > z + d + √((λp/λm) z^2 + max (−π) 0 / λm)` with `‖G θ‖ ≥ a` for all θ, or (II′)
`π > (λp − λm) z^2 + λm (W^2 + 2 z dloc)`, then for all θ, `q (Z + G θ + E_ θ) > λp ‖Z‖^2 − π`.
Consequently (the criterion comparison): since `q Z ≤ λp ‖Z‖^2` plays the role of J̃(s*), and
`J̃(s) ≥ λm J(s)`, the perturbed criterion of s exceeds that of s* (state and prove this corollary with
`pen`, `penbar` as in U01 item 4).

## U03 Theorem 2 assembly (THEORY.md §4, lines 393–423)

File `Thm2Assembly.lean`. Setting: a probability space `(Ω, P)`; a `Fintype` of trees `S`; a subset
`Smin : Set S` (minimal true trees); for each ω a candidate set `Ŝ ω : Finset S` and a selected tree
`ŝ ω ∈ Ŝ ω` that minimizes `crit ω` over `Ŝ ω`; five measurable events `A i` with `P (A i)ᶜ ≤ exp (−t)`;
and the hypothesis (what Proposition 2.1 delivers on the intersection) that for every ω in `⋂ i, A i`,
every `s ∉ Smin` and every `s* ∈ Smin`, `crit ω s > crit ω s*`.

Required:
1. For ω in the intersection with `(Ŝ ω ∩ Smin).Nonempty`, `ŝ ω ∈ Smin`.
2. `P {ω | ŝ ω ∉ Smin} ≤ 5 exp (−t) + P {ω | (Ŝ ω ∩ Smin) = ∅}`.
3. The tree-specific union bound: events `B s` with `P (B s) ≤ exp (−t_s)` and `∑ s, exp (−t_s) ≤ exp (−t)`
   give `P (⋃ s, B s) ≤ exp (−t)`.
Stretch: none. (Measurability hypotheses may be added as needed; list them.)

## U04 Corollary 2.2, the algebra (THEORY.md §4, lines 439–451)

File `Cor22.lean`. Pure real-number and counting statements.

Required:
1. Weighted union bound: trees `S : Finset`, sizes `ℓ : S → ℕ` with `1 ≤ ℓ s ≤ L`, and
   `#{s | ℓ s = k} ≤ (3m)^k` for each k, imply `∑ s, (3m : ℝ)^(−ℓ s) / L ≤ 1`.
2. With `t_s := t + log L + ℓ_s log(3m)`, `exp (−t_s) = exp (−t) (3m)^(−ℓ_s) / L`, so
   `∑ s, exp (−t_s) ≤ exp (−t)`.
3. `2 √(k t) ≤ k + t` for `k t ≥ 0`, hence `ρ(1+ε)(k + 2√(k t_s) + 2 t_s) ≤ ρ(1+ε)(2k + 3t + 3 log L)
   + 3ρ(1+ε) ℓ_s log(3m)` for `ρ(1+ε) ≥ 0`.
4. Cancellation: for `m ≥ 2` (so `log m > 0`), if `w ≥ 3ρ(1+ε) log(3m) / log m` and
   `(p_s − p₀) κ > w ℓ̄₀ log m + ρ(1+ε)(2k + 3t + 3 log L) + 2 z dloc`, then
   `(p_s − p₀) κ + w (ℓ_s − ℓ̄₀) log m > ρ(1+ε)(k + 2√(k t_s) + 2 t_s) + 2 z dloc`
   (condition (II) at the tree-specific level), for all `ℓ_s ≥ 0`.
5. The tree-count bound as pure arithmetic: `∑_{k=0}^{L} (3m)^k ≤ 2 (3m)^L` for `3m ≥ 2`, hence
   `log (∑_{k ≤ L} (3m)^k) ≤ L log(3m) + log 2`.
Stretch: none.

## U05 Lemma 1, identification on a compact class (THEORY.md §1, lines 93–106)

File `Lemma1.lean`. Abstract setting: `H, H'` real normed (or inner product) spaces; `T : H →L[ℝ] H'`;
`f₀ : H`; for each tree s in a finite type, a compact space `Θ s` and a continuous `φ s : Θ s → H`
(this continuity is (A3)'s consequence "continuous into L²", taken as hypothesis in the required part);
(A2) as: for every s and θ, `T (φ s θ − f₀) = 0 → φ s θ = f₀`; a tree is wrong if `φ s θ ≠ f₀` for all θ.

Required:
1. (a) `range (φ s)` is compact, and the finite union `F_L := ⋃ s, range (φ s)` is compact.
2. (b) For a wrong tree, `∃ δ > 0, ∀ θ, ‖T (φ s θ − f₀)‖^2 ≥ δ`; hence over the (finitely many) wrong
   trees a common `δ_L > 0`.
3. (c) For every ε > 0, `∃ ω > 0, ∀ f ∈ F_L, ε ≤ ‖f − f₀‖ → ω ≤ ‖T (f − f₀)‖^2`.
Stretch: (A3) ⇒ continuity into L²: with Mathlib's `MeasureTheory.Lp` and dominated convergence, show
that pointwise continuity in θ with a square-integrable envelope gives continuity of `θ ↦ f_s(·;θ)`
into `Lp ℝ 2 μ`.

## U06 Theorem 1, deterministic core and consistency (THEORY.md §3, lines 151–180)

File `Thm1.lean`. Two layers.

Required (deterministic layer, everything for one fixed sample, no probability): trees `S` a finite
type, `Smin ⊆ S₀ ⊆ S`, `pen s = p s * κ + w * ℓ s * log m` with `κ, w ≥ 0`, `p s ≥ p₀` for `s ∈ S₀`
and `p s = p₀` for `s ∈ Smin`, `ℓ s ≤ L`; for a sample: `Qhat s ≥ 0`, `Qn0 ≥ 0` (= Q_n(f₀)),
`σ² > 0`, a candidate set `Ŝ` and `ŝ ∈ Ŝ` minimizing `crit s := n Qhat s / σ² + pen s` over `Ŝ`;
the facts `Qhat s* ≤ Qn0` for `s* ∈ S₀ ∩ Ŝ` (the true tree can reproduce f₀).
1. (3.1) and (i): if `s* ∈ Ŝ ∩ S₀` then `Qhat ŝ ≤ Qn0 + σ² pen s* / n`; and if moreover
   `|Qhat s − Q(f_s(θ̂_s))| ≤ R` (uniform deviation, as a hypothesis on the selected value) then
   `Q(f̂) ≤ Qn0 + σ² pen s*/n + R`.
2. (ii): if `s* ∈ Ŝ ∩ Smin`, and for every wrong `s`, `Qhat s ≥ δQ s − R` with
   `n (δQ s − R)/σ² > n Qn0/σ² + pen s*`, and for every over-parameterized true `s` (p s > p₀),
   `(p s − p₀) κ + w (ℓ s − ℓ s*) log m > n Qn0 / σ²`, then `ŝ ∈ Smin`. (Also show the paper's
   sufficient form `κ − w L log m > n Qn0 / σ²` for the second condition.)

Stretch (probabilistic layer): with sequences of random variables `R_n → 0` in probability,
`n Qn0_n = O_p(1)` (formulated as: ∀ η > 0, ∃ M, limsup P(n Qn0_n > M) ≤ η), `σ̂²_n → σ*² ∈ (0,∞)` in
probability, `κ_n → ∞`, `κ_n / n → 0`, and coverage probability → 1, conclude `P(ŝ_n ∈ Smin) → 1` and
`P(‖f̂_n − f₀‖ ≥ ε) → 0` using `η(ε) > 0` from Lemma 1(c)-type compactness (take `η(ε) > 0` as a
hypothesis if Lemma 1 is not re-proved here).

## U07 Theorem 3(a), misspecified law (THEORY.md §6, lines 528–534)

File `Thm3a.lean`. Setting: `F` a compact nonempty set in a metric space (the class F_L), `Q : F → ℝ`
continuous, `Qstar := ⨅ Q`, `Fstar := {f | Q f = Qstar}`.
Required:
1. `Fstar` is nonempty and compact.
2. For every ε > 0, `∃ η > 0, ∀ f ∈ F, (∀ g ∈ Fstar, ε ≤ dist f g) → Qstar + η ≤ Q f`.
3. The basic inequality: if `sup_F |Qn − Q| ≤ R` and `Qn f̂ ≤ Qn f* + η'` for some `f* ∈ Fstar`, then
   `Q f̂ ≤ Qstar + 2R + η'`. (The argmin step `Q̂_ŝ ≤ Q_n(f*) + σ̂² max pen / n` is U06 item 1.)
Stretch: the in-probability wrapper: if `P(Q f̂_n ≥ Qstar + η) → 0` for every η > 0 then
`P(inf_{g ∈ Fstar} dist(f̂_n, g) ≥ ε) → 0` for every ε > 0.

## U08 Theorem 3(b), growing formula size (THEORY.md §6, lines 540–575)

File `Thm3b.lean`. Setting: `H₀` a real Hilbert space (L²(P_X)), `H' ` a real Hilbert space (L²(P_Z)),
`T : H₀ →L[ℝ] H'` with `‖T‖ ≤ 1`, `𝓗 : Set H₀` compact with `f₀ ∈ 𝓗`, (S2): `∀ f ∈ 𝓗, T (f − f₀) = 0 →
f = f₀`; a sequence of closed subspaces `V_n` of `H'` with orthogonal projections `Π_n` such that
`∀ h, Π_n h → h` (strong convergence).
Required:
1. Step 1: `ω ε := ⨅ {‖T(f − f₀)‖^2 | f ∈ 𝓗, ε ≤ ‖f − f₀‖}` is positive for ε > 0, and there is
   `n₀` such that for `n ≥ n₀` and every `f ∈ 𝓗` with `‖f − f₀‖ ≥ ε`, `‖Π_n T (f − f₀)‖^2 ≥ ω ε / 4`.
   (Uniform strong convergence on the compact image `T '' (𝓗 − f₀)`, via a finite δ-net and
   `‖I − Π_n‖ ≤ 1`.)
2. The algebra of Step 2's last line: for vectors with `‖g‖ ≤ M` and perturbations `u, D`,
   `|‖u + g + D‖^2 − ‖g‖^2| ≤ (‖u‖ + ‖D‖)(2M + ‖u‖ + ‖D‖)`.
3. Steps 3–4 as deterministic implications: if `Q_Kn f̂ ≤ Q_n f̂ + R`, `Q_n f̂ ≤ Q_n f* + η`,
   `Q_n f* ≤ Q_Kn f* + R`, `Q_Kn f* ≤ ‖f* − f₀‖^2`, then `Q_Kn f̂ ≤ ‖f* − f₀‖^2 + 2R + η`; and, with
   Step 1, `‖f̂ − f₀‖ ≥ ε → Q_Kn f̂ ≥ ω ε/4`.
Stretch: `Δ_n(t) → 0` under (S6): with `ζ_n^2 L_n (L_n + log n)/n → 0`, `log Λ_n ≤ a (L_n + log n)`,
`K_n ≤ ζ_n^2`, `L_n ≥ 1`, show the explicit `Δ_n(t)` of line 564 tends to 0 for fixed t.

## U09 Lemma 4(a), hinge-spline approximation (THEORY.md §6, lines 579–583)

File `Lemma4a.lean`. Setting: `f₀ : ℝ → ℝ` with `|f₀ x| ≤ A` on `[xlo, xhi]` and `Λ₀`-Lipschitz there
(`LipschitzOnWith`), `k ≥ 1`, knots `x_j := xlo + j h` with `h := (xhi − xlo)/k`.
Required:
1. The interpolation error: for `x` in `[x_j, x_{j+1}]` written as `λ x_j + (1−λ) x_{j+1}`,
   `|λ (f₀ x − f₀ x_j) + (1−λ)(f₀ x − f₀ x_{j+1})| ≤ 2λ(1−λ) Λ₀ h ≤ Λ₀ h / 2`.
2. The piecewise-linear interpolant `I_k f₀` (define it) satisfies `‖I_k f₀ − f₀‖_∞ ≤ Λ₀ (xhi − xlo)/(2k)`
   on `[xlo, xhi]`, `|I_k f₀ x| ≤ A` there, and is `Λ₀`-Lipschitz on `[xlo, xhi]`.
3. The hinge representation `I_k f₀ x = a + b x + ∑_{j=1}^{k−1} c_j max (x − κ_j) 0` with
   `|b| ≤ Λ₀`, `|c_j| ≤ 2 Λ₀`, `|κ_j| ≤ x̄ := max |xlo| |xhi|`, `|a| ≤ A + Λ₀ x̄`.
4. The final bound: for `L ≥ 8` and `k := ⌊(L+3)/8⌋`, `k ≥ (L − 4)/8 ≥ 1` and
   `Λ₀ (xhi − xlo)/(2k) ≤ 4 Λ₀ (xhi − xlo)/(L − 4) ≤ 8 Λ₀ (xhi − xlo)/L`.
Stretch: an expression-tree type with `+, −, ×, max`, variables and constants, a `size` function, and
a proof that the hinge representation has `5 + 8(k − 1)` nodes.

## U10 Proposition 4, discrete instruments (THEORY.md §5, lines 505–513)

File `Prop4.lean`.
Required:
1. (a) With `m : H →ₗ[ℝ] (Fin J → ℝ)` linear, `f_s θ = ∑_k θ_k • ψ_k`, `Ψ θ := m (f_s θ)`, if
   `Ψ θ = m f₀` then `m (f_s θ − f₀) = 0`; and if the `J × p` matrix of `Ψ` has rank J (surjective)
   then such a θ exists for every target (state the existence as surjectivity of the linear map).
2. (b) Lyusternik–Graves from Mathlib: for `F : ℝ^p → ℝ^J` strictly differentiable at `θ̄` (a C¹ map
   near θ̄ is strictly differentiable there) with surjective derivative, and `θ̄` interior to `Θ`
   (`Θ ∈ 𝓝 θ̄`), there is `r > 0` such that `‖F θ̄‖ < r → ∃ θ ∈ Θ, F θ = 0`. Use
   `HasStrictFDerivAt.map_nhds_eq_of_surj` (or the open-mapping lemmas around it).
Stretch: none.

## U11 Proposition 3.3, Proposition 5 event logic, Proposition 5(c) (THEORY.md §6 lines 597–607; §3.2 lines 257–280)

File `Prop33Prop5.lean`.
Required:
1. Proposition 3.3: for a nondecreasing `ω : ℝ → ℝ` and `ωinv q := sSup {ε | ω ε ≤ q}` (state the
   boundedness needed for `sSup` or use `EReal`), if `ω ‖f̂ − f₀‖ ≤ Q` (the definition of the sieve
   modulus applied at `ε = ‖f̂ − f₀‖`) then `‖f̂ − f₀‖ ≤ ωinv Q`.
2. Proposition 5(a) event logic: with `S_{s₀} := ⨅ θ ∈ Θ, AR θ` and `θ₀ ∈ Θ`, `S_{s₀} ≤ AR θ₀`, so
   `{s₀ ∈ Ŝ ∧ ¬ (S_{s₀} ≤ c)} ⊆ {AR θ₀ > c}`; hence for a probability measure, the probability of the
   first is at most that of the second, whatever Ŝ is. (b): the event `E ∩ {s₀ ∉ C_α}` is contained in
   the same set.
3. Proposition 5(c) deterministic part: for a positive definite symmetric `Ω̂` on `ℝ^K` with
   `⟪x, Ω̂⁻¹ x⟫ ≥ ‖x‖^2 / ‖Ω̂‖` (prove it from the spectral theorem if feasible, else hypothesis), and
   `‖Ω̂‖ ≤ ζ² n⁻¹ ∑ r_i^2 ≤ 2 ζ² n⁻¹ ∑ (y_i^2 + F_i^2) =: B_n` (from `(a−b)^2 ≤ 2a^2 + 2b^2` and
   `‖b_i‖ ≤ ζ`), the inequality `AR ≤ c` with `AR = n ⟪ĝ, Ω̂⁻¹ ĝ⟫` gives `‖ĝ‖^2 ≤ c B_n / n`.
Stretch: the winsorized-weight algebra: for `0 ≺ Ω_c ⪯ Ω`, `A := Ω^{1/2} Ω_c^{-1} Ω^{1/2} ⪰ I`, hence
`ξ'Aξ ≥ ξ'ξ`, and `ξ'Aξ ≤ ‖A‖ ξ'ξ` with `‖A‖ = 1/λ_min(Ω_c Ω^{-1})`.

## U12 The tree count (THEORY.md §0, lines 53–55)

File `TreeCount.lean`. Define an inductive type of expression trees over an alphabet of `m` labels:
leaf (label), unary node (label, child), binary node (label, two children); `size` = number of nodes.
Required: the number of trees with exactly `ℓ` nodes is at most `(3m)^ℓ`, via an injection into
`Fin ℓ → Fin 3 × Fin m` (preorder arity-and-label sequence, a Łukasiewicz word), and
`#{trees with size ≤ L} ≤ ∑_{k ≤ L} (3m)^k ≤ 2 (3m)^L` for `3m ≥ 2`. (Trees of size ℓ form a finite
set; show finiteness or work with the injection on the subtype.)
Stretch: the sharper Motzkin bound is not needed.

## U13 Lemma 3 algebra and Corollary 2.5 (THEORY.md §4, lines 367–391 and 488)

File `Lemma3Algebra.lean`.
Required:
1. Matrix Bernstein solution: for `v, R > 0` and `u ≥ 0`, `x := √(2 v u) + 2 R u / 3` satisfies
   `x^2 / (2v + 2 R x / 3) ≥ u`, i.e. `2K exp(−x^2/(2v + 2Rx/3)) ≤ 2K exp(−u)`; with `u := t + log(2K)`
   this is `≤ exp(−t)`.
2. The z_t² assembly: from `tr Σ̂ ≤ K(1+ε)`, `tr Σ̂² ≤ K(1+ε)^2`, `‖Σ̂‖ ≤ 1+ε` (reals, hypotheses) and
   the HKZ form `σ̄²(tr Σ̂ + 2√(tr(Σ̂²) t) + 2‖Σ̂‖ t)`, the bound `≤ σ̄² (1+ε)(K + 2√(K t) + 2t)`; dividing
   by σ² gives `z_t^2 = ρ(1+ε)(K + 2√(Kt) + 2t)`.
3. McDiarmid's constant: with bounded differences `c = 4 ζ M'` for `n` summands, the bound
   `exp(−2 s^2 / (n c^2))` at `s := ζ M' √(8 n u)` equals `exp(−u)`.
4. Corollary 2.5 sandwich: for a self-adjoint positive definite `Σ̂` on a finite-dimensional real inner
   product space with `‖Σ̂ − id‖ ≤ ε < 1`, every `x` satisfies
   `(1+ε)⁻¹ ‖x‖^2 ≤ ⟪x, Σ̂⁻¹ x⟫ ≤ (1−ε)⁻¹ ‖x‖^2` (spectral theorem: eigenvalues of Σ̂ lie in
   `[1−ε, 1+ε]`).
Stretch: the trace bounds of Lemma 3(b)/(d) from `‖Σ̂ − I‖ ≤ ε`: `tr Σ̂ ≤ K(1+ε)`, `tr Σ̂² ≤ K(1+ε)^2`,
and `tr(P_V Σ̂) ≤ k ‖Σ̂‖`, `tr((P_V Σ̂ P_V)^2) ≤ k ‖Σ̂‖^2` for a rank-k orthogonal projection `P_V`.

## U14 Theorem 1(iii), the selected-tree step (THEORY.md §3, lines 225–231, step 2)

File `Thm1iiiSelected.lean`. Setting: a probability space; a finite type `S`; `ŝ : Ω → S` measurable
with respect to a σ-algebra `𝓐` (the A sample), statistics `X s : Ω → ℝ` measurable with respect to
`𝓑` (the B sample), `𝓐` and `𝓑` independent; `φ : ℝ → ℝ` bounded measurable; a constant `c`
(= E φ(N)); and `Smin ⊆ S`.
Required: `|E[φ (X (ŝ ω)) ] − c| ≤ ∑_{s ∈ Smin} P(ŝ = s) |E[φ (X s)] − c| + 2 ‖φ‖_∞ P(ŝ ∉ Smin)`,
using `E[φ(X s) 1{ŝ = s}] = P(ŝ = s) E[φ(X s)]` from independence.
Stretch: none.

## U15 Theorem 2, the conditioning clause (THEORY.md §4, Lemma 3(b),(d) lines 372–380; proof of Theorem 2, line 420)

File `Thm2Conditioning.lean` (second run, 2026-10-15). Lemma 3(b) and (d) are bounds conditional on
`Z_{1:n}`, valid on the event `A` of Lemma 3(a): on `A`, `P(B | Z_{1:n}) ≤ e^{-t}` with `B` the failure
event. Theorem 2's proof integrates them ("their failure events are taken within (a) and integrated,
which gives the same e^{-t}") and intersects five events. Setting: a probability space `(Ω, μ)`; a
sub-σ-algebra `m` standing for `σ(Z_{1:n})`; `A` measurable with respect to `m`; `B` measurable; the
conditional bound as the hypothesis `μ[1_B | m] ≤ ε` almost everywhere on `A`.
Required:
1. `P(A ∩ B) ≤ ε P(A) ≤ ε` from `P(A ∩ B) = ∫_A 1_B = ∫_A μ[1_B | m]` (the tower property, Mathlib's
   `setIntegral_condExp`).
2. The five events of Theorem 2: `A` (Lemma 3(a)), the failures `B_b`, `B_d` of (b) and (d) with the
   conditional bound on `A`, and the failures `C_c`, `C_c'` of the two applications of (c) with
   unconditional bounds; the good event `G := A ∩ B_bᶜ ∩ C_cᶜ ∩ C_c'ᶜ ∩ B_dᶜ` has `P(Gᶜ) ≤ 5 e^{-t}`.
3. The five sets `A`, `(A ∩ B_b)ᶜ`, `C_cᶜ`, `C_c'ᶜ`, `(A ∩ B_d)ᶜ` each have complement of probability at
   most `e^{-t}` and intersect to `G`, which is the form consumed by `Thm2Assembly.prob_not_mem_le`.
Stretch: none.
