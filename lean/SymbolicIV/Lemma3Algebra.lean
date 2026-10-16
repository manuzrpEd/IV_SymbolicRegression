/-
# Lemma 3, the algebra behind its constants, and Corollary 2.5 — THEORY.md §4, Lemma 3 and Corollary 2.5;
paper appendix-proofs.tex, proof of Lemma 3 and of Corollary 2.5 (unit U13 of the plan).

What is formalized (the probabilistic tools themselves — matrix Bernstein, Hsu–Kakade–Zhang,
McDiarmid — are not re-proved; what Lean checks is the arithmetic the paper performs with their
conclusions):

1. Bernstein solution (Lemma 3(a)): for `v R > 0`, `u ≥ 0`, `x := √(2 v u) + 2 R u / 3` satisfies
   `u ≤ x² / (2v + 2Rx/3)`, hence `2K exp(−x²/(2v + 2Rx/3)) ≤ 2K exp(−u)`, and with
   `u := t + log(2K)` the right side is `exp(−t)` (`K > 0`).  The paper's `ε_n(t)` is this `x` with
   `v = ζ²/n`, `R = (ζ² + 1)/n` (`epsN_eq`).  The tail-function version
   (`bernstein_tail_le_exp`) also records that the bound is monotone in `x`, so it applies at any
   level `≥ x`.
2. The `z_t²` assembly (Lemma 3(b)): from `tr Σ̂ ≤ K(1+ε)`, `tr Σ̂² ≤ K(1+ε)²`, `‖Σ̂‖ ≤ 1+ε` (reals),
   the HKZ bound `σ̄²(tr Σ̂ + 2√(tr(Σ̂²) t) + 2‖Σ̂‖ t)` is `≤ σ̄²(1+ε)(K + 2√(Kt) + 2t)`, and after
   division by `σ²` it is `≤ ρ(1+ε)(K + 2√(Kt) + 2t) = z_t²` with `ρ = σ̄²/σ²`.  The same algebra with
   `k ‖Σ̂‖`, `k ‖Σ̂‖²` gives Lemma 3(d).
3. McDiarmid's constant (Lemma 3(c), "one centre"): with bounded differences `c = 4ζM'` and `n`
   summands, `exp(−2s²/(n c²))` at `s := ζ M' √(8 n u)` equals `exp(−u)`; combined with
   `E F ≤ √n M' √K` and the antitone tail this is `P(F > √n M'√K + ζM'√(8nu)) ≤ e^{−u}`.
   "All centres": `N e^{−u} ≤ e^{−t}` for `N ≤ (1 + 2CΛ√n/M')^p` and `u = t + p log(1 + 2CΛ√n/M')`;
   "between centres": the three terms add up to the constant displayed in Lemma 3(c).
4. Corollary 2.5 sandwich: for a self-adjoint `Σ̂` on a finite-dimensional real inner product space
   with `‖Σ̂ − id‖ ≤ ε < 1` (operator norm), `Σ̂` is invertible and every `x` satisfies
   `(1+ε)⁻¹ ‖x‖² ≤ ⟪x, Σ̂⁻¹ x⟫ ≤ (1−ε)⁻¹ ‖x‖²`.  The paper argues through the eigenvalues; here the
   same bounds are obtained without the spectral theorem, from the Cauchy–Schwarz inequality for the
   positive form `⟪·, Σ̂ ·⟫` (lower bound) and from `Σ̂ − (1−ε) id ⪰ 0` (upper bound).
Stretch (Lemma 3(b)/(d), trace bounds), also proved: `tr Σ̂ ≤ K(1+ε)`, `tr Σ̂² ≤ K(1+ε)²` from
`‖Σ̂ − id‖ ≤ ε`, and `tr(P_V Σ̂) ≤ k ‖Σ̂‖`, `tr((P_V Σ̂ P_V)²) ≤ k ‖Σ̂‖²`, with `tr` the trace of a
linear map on `E`, `K = dim E`, and `P_V = proj v` the orthogonal projection `x ↦ ∑_j ⟪v_j, x⟫ v_j`
onto the span of an orthonormal `k`-tuple `v` (so `dim V = k`, `finrank_span_eq`).

Hypotheses of the Lean statements beyond the paper's:
* Item 2: `0 ≤ t`, `0 ≤ ε`, `0 ≤ σ̄²`, `0 < σ²` (and `0 ≤ k`, `0 ≤ ‖Σ̂‖` in the (d) version): all
  automatic in the paper (`t > 0`, `ε_n(t) > 0`, variances, `k ∈ ℕ`).
* Item 3: `0 < n`, `0 < ζ`, `0 < M'`, `0 ≤ u` (and `0 ≤ C`, `0 ≤ Λ`, `0 ≤ t` for the union bound);
  `M' > 0` is stated in the paper; the others are implicit there (`ζ_K ≥ 1`, `u = t + ... > 0`).
* Item 4: `Σ̂` is taken as a continuous linear map `E →L[ℝ] E` that is symmetric
  (`⟪Σ̂ x, y⟫ = ⟪x, Σ̂ y⟫`); positive definiteness is not assumed, it follows from `‖Σ̂ − id‖ ≤ ε < 1`.
  The inverse appears as any right inverse `Σinv` (`Σ̂ (Σinv x) = x`); `exists_rightInverse` shows one
  exists under the same hypotheses, and `sandwich_of_sigma_sub_id` packages the two.
Nothing is assumed beyond this; there is no `sorry`.
-/
import Mathlib

open Real

noncomputable section

namespace SymbolicIV.Lemma3Algebra

/-! ## 1. The matrix Bernstein solution (Lemma 3(a)) -/

/-- The exponent of Tropp's matrix Bernstein bound `2K exp(−x²/(2v + 2Rx/3))`. -/
def bernExp (v R x : ℝ) : ℝ := x ^ 2 / (2 * v + 2 * R * x / 3)

/-- The paper's solution `x := √(2vu) + 2Ru/3` of `x²/(2v + 2Rx/3) = u` (an upper solution). -/
def bernSol (v R u : ℝ) : ℝ := Real.sqrt (2 * v * u) + 2 * R * u / 3

/-- Item 1: `x := √(2vu) + 2Ru/3` satisfies `x²/(2v + 2Rx/3) ≥ u`. -/
theorem bernSol_exp_ge (v R u : ℝ) (hv : 0 < v) (hR : 0 < R) (hu : 0 ≤ u) :
    u ≤ bernExp v R (bernSol v R u) := by
  unfold bernExp bernSol
  set s := Real.sqrt (2 * v * u) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 2 * v * u := Real.sq_sqrt (by positivity)
  set w := 2 * R * u / 3 with hw
  have hw0 : 0 ≤ w := by positivity
  have hden : 0 < 2 * v + 2 * R * (s + w) / 3 := by positivity
  rw [le_div_iff₀ hden]
  -- `u (2v + 2R(s+w)/3) = s² + w s + w²` and `(s+w)² = s² + 2 s w + w²`.
  have h1 : u * (2 * v + 2 * R * (s + w) / 3) = s ^ 2 + w * s + w ^ 2 := by
    rw [hs2, hw]; ring
  rw [h1]
  nlinarith [mul_nonneg hs0 hw0]

/-- The Bernstein exponent is monotone in the level `x ≥ 0`. -/
theorem bernExp_mono (v R : ℝ) (hv : 0 < v) (hR : 0 < R) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    bernExp v R x ≤ bernExp v R y := by
  unfold bernExp
  have hy : 0 ≤ y := hx.trans hxy
  have hdx : 0 < 2 * v + 2 * R * x / 3 := by positivity
  have hdy : 0 < 2 * v + 2 * R * y / 3 := by positivity
  rw [div_le_div_iff₀ hdx hdy]
  have : x ^ 2 ≤ y ^ 2 := by nlinarith
  nlinarith [mul_nonneg hx hy, mul_nonneg (mul_nonneg hR.le hx) (sub_nonneg.2 hxy),
    mul_nonneg hv.le (sub_nonneg.2 this)]

/-- `2K exp(−x²/(2v + 2Rx/3)) ≤ 2K exp(−u)` at the solution `x`, for `K ≥ 0`. -/
theorem bernstein_bound_le (v R u K : ℝ) (hv : 0 < v) (hR : 0 < R) (hu : 0 ≤ u) (hK : 0 ≤ K) :
    2 * K * Real.exp (-(bernExp v R (bernSol v R u))) ≤ 2 * K * Real.exp (-u) := by
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.2
  linarith [bernSol_exp_ge v R u hv hR hu]

/-- With `u := t + log(2K)` and `K > 0`, `2K exp(−u) = exp(−t)`. -/
theorem two_K_exp_neg_log (t K : ℝ) (hK : 0 < K) :
    2 * K * Real.exp (-(t + Real.log (2 * K))) = Real.exp (-t) := by
  rw [Real.exp_neg, Real.exp_add, Real.exp_log (by positivity), Real.exp_neg]
  field_simp

/-- Lemma 3(a) as the paper states it: the Bernstein tail at level `x ≥ bernSol v R (t + log 2K)`
is at most `e^{−t}`.  The hypothesis `hBern` is Tropp's inequality for the tail function `P`
(`P x` stands for `P(‖Σ̂ − I‖ > x)`), which is antitone in the level. -/
theorem bernstein_tail_le_exp (v R t K : ℝ) (hv : 0 < v) (hR : 0 < R) (hK : 0 < K)
    (hu : 0 ≤ t + Real.log (2 * K)) (P : ℝ → ℝ) (hanti : Antitone P)
    (hBern : ∀ x, 0 ≤ x → P x ≤ 2 * K * Real.exp (-(bernExp v R x))) {x : ℝ}
    (hx : bernSol v R (t + Real.log (2 * K)) ≤ x) :
    P x ≤ Real.exp (-t) := by
  have hx0 : 0 ≤ bernSol v R (t + Real.log (2 * K)) := by unfold bernSol; positivity
  calc P x ≤ P (bernSol v R (t + Real.log (2 * K))) := hanti hx
    _ ≤ 2 * K * Real.exp (-(bernExp v R (bernSol v R (t + Real.log (2 * K))))) := hBern _ hx0
    _ ≤ 2 * K * Real.exp (-(t + Real.log (2 * K))) := bernstein_bound_le v R _ K hv hR hu hK.le
    _ = Real.exp (-t) := two_K_exp_neg_log t K hK

/-- The paper's `ε_n(t) = √(2ζ²(t + log 2K)/n) + 2(ζ² + 1)(t + log 2K)/(3n)`. -/
def epsN (ζ n K t : ℝ) : ℝ :=
  Real.sqrt (2 * ζ ^ 2 * (t + Real.log (2 * K)) / n) + 2 * (ζ ^ 2 + 1) * (t + Real.log (2 * K)) / (3 * n)

/-- `ε_n(t)` is the Bernstein solution with `v = ζ²/n` and `R = (ζ² + 1)/n`. -/
theorem epsN_eq (ζ n K t : ℝ) (hn : n ≠ 0) :
    epsN ζ n K t = bernSol (ζ ^ 2 / n) ((ζ ^ 2 + 1) / n) (t + Real.log (2 * K)) := by
  unfold epsN bernSol
  congr 1
  · congr 1; field_simp
  · field_simp

/-! ## 2. The `z_t²` assembly (Lemma 3(b), and (d) with `k` in place of `K`) -/

/-- The Hsu–Kakade–Zhang bound `σ̄²(tr Σ̂ + 2√(tr(Σ̂²) t) + 2‖Σ̂‖ t)`, as a function of the three
real numbers `tr Σ̂`, `tr Σ̂²`, `‖Σ̂‖`. -/
def hkz (σb2 trS trS2 nrm t : ℝ) : ℝ := σb2 * (trS + 2 * Real.sqrt (trS2 * t) + 2 * nrm * t)

/-- The paper's `z_t² := ρ(1 + ε)(K + 2√(Kt) + 2t)`. -/
def zt2 (ρ ε K t : ℝ) : ℝ := ρ * (1 + ε) * (K + 2 * Real.sqrt (K * t) + 2 * t)

/-- Item 2, before dividing by `σ²`: with `tr Σ̂ ≤ K(1+ε)`, `tr Σ̂² ≤ K(1+ε)²`, `‖Σ̂‖ ≤ 1+ε`,
the HKZ bound is at most `σ̄²(1+ε)(K + 2√(Kt) + 2t)`. -/
theorem hkz_le (σb2 trS trS2 nrm t K ε : ℝ) (hσ : 0 ≤ σb2) (ht : 0 ≤ t) (hε : 0 ≤ ε)
    (h1 : trS ≤ K * (1 + ε)) (h2 : trS2 ≤ K * (1 + ε) ^ 2) (h3 : nrm ≤ 1 + ε) :
    hkz σb2 trS trS2 nrm t ≤ σb2 * ((1 + ε) * (K + 2 * Real.sqrt (K * t) + 2 * t)) := by
  unfold hkz
  apply mul_le_mul_of_nonneg_left _ hσ
  have hsq : Real.sqrt (trS2 * t) ≤ (1 + ε) * Real.sqrt (K * t) := by
    calc Real.sqrt (trS2 * t) ≤ Real.sqrt (K * (1 + ε) ^ 2 * t) :=
          Real.sqrt_le_sqrt (by nlinarith)
      _ = (1 + ε) * Real.sqrt (K * t) := by
          rw [show K * (1 + ε) ^ 2 * t = (1 + ε) ^ 2 * (K * t) by ring, Real.sqrt_mul (by positivity),
            Real.sqrt_sq (by positivity)]
  nlinarith

/-- Item 2: dividing by `σ² > 0`, the conditional HKZ bound is at most `z_t²` with `ρ = σ̄²/σ²`. -/
theorem hkz_div_le_zt2 (σb2 σ2 trS trS2 nrm t K ε : ℝ) (hσ : 0 ≤ σb2) (hσ2 : 0 < σ2)
    (ht : 0 ≤ t) (hε : 0 ≤ ε)
    (h1 : trS ≤ K * (1 + ε)) (h2 : trS2 ≤ K * (1 + ε) ^ 2) (h3 : nrm ≤ 1 + ε) :
    hkz σb2 trS trS2 nrm t / σ2 ≤ zt2 (σb2 / σ2) ε K t := by
  unfold zt2
  rw [div_le_iff₀ hσ2]
  calc hkz σb2 trS trS2 nrm t ≤ σb2 * ((1 + ε) * (K + 2 * Real.sqrt (K * t) + 2 * t)) :=
        hkz_le σb2 trS trS2 nrm t K ε hσ ht hε h1 h2 h3
    _ = σb2 / σ2 * (1 + ε) * (K + 2 * Real.sqrt (K * t) + 2 * t) * σ2 := by
        field_simp

/-- Lemma 3(d): the same assembly with `tr Σ ≤ k‖Σ̂‖`, `tr Σ² ≤ k‖Σ̂‖²`, `‖Σ‖ ≤ ‖Σ̂‖` and
`‖Σ̂‖ ≤ 1 + ε` gives the bound with `k` in place of `K`. -/
theorem hkz_div_le_zt2_proj (σb2 σ2 trS trS2 nrm nrmP t k ε : ℝ) (hσ : 0 ≤ σb2) (hσ2 : 0 < σ2)
    (ht : 0 ≤ t) (hk : 0 ≤ k) (hε : 0 ≤ ε) (hnrm : 0 ≤ nrmP)
    (h1 : trS ≤ k * nrmP) (h2 : trS2 ≤ k * nrmP ^ 2) (h3 : nrm ≤ nrmP) (hP : nrmP ≤ 1 + ε) :
    hkz σb2 trS trS2 nrm t / σ2 ≤ zt2 (σb2 / σ2) ε k t := by
  apply hkz_div_le_zt2 σb2 σ2 trS trS2 nrm t k ε hσ hσ2 ht hε
  · exact h1.trans (by nlinarith)
  · exact h2.trans (by nlinarith [pow_le_pow_left₀ hnrm hP 2])
  · exact h3.trans hP

/-! ## 3. McDiarmid's constant (Lemma 3(c)) -/

/-- Item 3: with bounded differences `c = 4ζM'` and `n` summands, the McDiarmid exponent at
`s := ζM'√(8nu)` is exactly `u`, so `exp(−2s²/(nc²)) = exp(−u)`. -/
theorem mcdiarmid_const (ζ M' n u : ℝ) (hζ : 0 < ζ) (hM : 0 < M') (hn : 0 < n) (hu : 0 ≤ u) :
    Real.exp (-(2 * (ζ * M' * Real.sqrt (8 * n * u)) ^ 2 / (n * (4 * ζ * M') ^ 2))) =
      Real.exp (-u) := by
  congr 1
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
  field_simp
  ring

/-- "One centre": McDiarmid (`hMc`, for the antitone tail `P a = P(F > a)`) and `E F ≤ √n M'√K` give
`P(F > √n M'√K + ζM'√(8nu)) ≤ e^{−u}`. -/
theorem one_centre (ζ M' n u K EF : ℝ) (hζ : 0 < ζ) (hM : 0 < M') (hn : 0 < n) (hu : 0 ≤ u)
    (P : ℝ → ℝ) (hanti : Antitone P)
    (hMc : ∀ s, 0 ≤ s → P (EF + s) ≤ Real.exp (-(2 * s ^ 2 / (n * (4 * ζ * M') ^ 2))))
    (hEF : EF ≤ Real.sqrt n * M' * Real.sqrt K) :
    P (Real.sqrt n * M' * Real.sqrt K + ζ * M' * Real.sqrt (8 * n * u)) ≤ Real.exp (-u) := by
  have hs : 0 ≤ ζ * M' * Real.sqrt (8 * n * u) := by positivity
  calc P (Real.sqrt n * M' * Real.sqrt K + ζ * M' * Real.sqrt (8 * n * u))
      ≤ P (EF + ζ * M' * Real.sqrt (8 * n * u)) := hanti (by linarith)
    _ ≤ Real.exp (-(2 * (ζ * M' * Real.sqrt (8 * n * u)) ^ 2 / (n * (4 * ζ * M') ^ 2))) := hMc _ hs
    _ = Real.exp (-u) := mcdiarmid_const ζ M' n u hζ hM hn hu

/-- "All centres": a union bound over at most `(1 + 2CΛ√n/M')^p` centres, each failing with
probability `e^{−u}` at `u = t + p log(1 + 2CΛ√n/M')`, fails with probability at most `e^{−t}`. -/
theorem all_centres (C Λ n M' t : ℝ) (p : ℕ) (hC : 0 ≤ C) (hΛ : 0 ≤ Λ)
    (hM : 0 < M') (N : ℝ) (hN : N ≤ (1 + 2 * C * Λ * Real.sqrt n / M') ^ p) :
    N * Real.exp (-(t + p * Real.log (1 + 2 * C * Λ * Real.sqrt n / M'))) ≤ Real.exp (-t) := by
  have hb : 0 < 1 + 2 * C * Λ * Real.sqrt n / M' := by positivity
  have hpow : Real.exp (p * Real.log (1 + 2 * C * Λ * Real.sqrt n / M'))
      = (1 + 2 * C * Λ * Real.sqrt n / M') ^ p := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hb, mul_comm]
  rw [neg_add, Real.exp_add, Real.exp_neg (p * _), hpow]
  have h1 : N * ((1 + 2 * C * Λ * Real.sqrt n / M') ^ p)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one (by positivity)]; exact hN
  calc N * (Real.exp (-t) * ((1 + 2 * C * Λ * Real.sqrt n / M') ^ p)⁻¹)
      = (N * ((1 + 2 * C * Λ * Real.sqrt n / M') ^ p)⁻¹) * Real.exp (-t) := by ring
    _ ≤ 1 * Real.exp (-t) := by gcongr
    _ = Real.exp (-t) := one_mul _

/-- "Between centres": the per-centre level `(√n M'√K + ζM'√(8nu))/√n`, plus the Lipschitz slack
`2ζM'` between a point and its centre, is the constant displayed in Lemma 3(c). -/
theorem lemma3c_constant (ζ M' n u K : ℝ) (hn : 0 < n) :
    (Real.sqrt n * M' * Real.sqrt K + ζ * M' * Real.sqrt (8 * n * u)) / Real.sqrt n + 2 * ζ * M'
      = M' * (Real.sqrt K + 2 * ζ + ζ * Real.sqrt (8 * u)) := by
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  have h8 : Real.sqrt (8 * n * u) = Real.sqrt n * Real.sqrt (8 * u) := by
    rw [show 8 * n * u = n * (8 * u) by ring, Real.sqrt_mul hn.le]
  rw [h8]
  field_simp
  ring

/-! ## 4. Corollary 2.5: the sandwich for `Σ̂⁻¹` from `‖Σ̂ − id‖ ≤ ε < 1` -/

section Sandwich

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The quadratic form of `S` is sandwiched between `(1−ε)‖y‖²` and `(1+ε)‖y‖²` when
`‖S − id‖ ≤ ε` (operator norm). -/
theorem quad_bounds (S : E →L[ℝ] E) (ε : ℝ) (hε : ‖S - 1‖ ≤ ε) (y : E) :
    (1 - ε) * ‖y‖ ^ 2 ≤ ⟪y, S y⟫_ℝ ∧ ⟪y, S y⟫_ℝ ≤ (1 + ε) * ‖y‖ ^ 2 := by
  have hdec : ⟪y, S y⟫_ℝ = ‖y‖ ^ 2 + ⟪y, (S - 1) y⟫_ℝ := by
    have h : (S - 1) y = S y - y := by simp
    rw [h, inner_sub_right, real_inner_self_eq_norm_sq]; ring
  have hb : |⟪y, (S - 1) y⟫_ℝ| ≤ ε * ‖y‖ ^ 2 := by
    calc |⟪y, (S - 1) y⟫_ℝ| ≤ ‖y‖ * ‖(S - 1) y‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖y‖ * (‖S - 1‖ * ‖y‖) := by gcongr; exact (S - 1).le_opNorm y
      _ ≤ ‖y‖ * (ε * ‖y‖) := by gcongr
      _ = ε * ‖y‖ ^ 2 := by ring
  rw [abs_le] at hb
  constructor <;> nlinarith [hb.1, hb.2, hdec]

/-- Cauchy–Schwarz for the positive semidefinite form `(u, v) ↦ ⟪u, S v⟫` of a symmetric `S`:
`⟪u, S v⟫² ≤ ⟪u, S u⟫ ⟪v, S v⟫`. -/
theorem inner_map_sq_le (S : E →L[ℝ] E) (hsym : ∀ x y, ⟪S x, y⟫_ℝ = ⟪x, S y⟫_ℝ)
    (hpos : ∀ y, 0 ≤ ⟪y, S y⟫_ℝ) (u v : E) :
    ⟪u, S v⟫_ℝ ^ 2 ≤ ⟪u, S u⟫_ℝ * ⟪v, S v⟫_ℝ := by
  have hquad : ∀ x : ℝ, 0 ≤ ⟪v, S v⟫_ℝ * (x * x) + (2 * ⟪u, S v⟫_ℝ) * x + ⟪u, S u⟫_ℝ := by
    intro x
    have h := hpos (u + x • v)
    have hvu : ⟪v, S u⟫_ℝ = ⟪u, S v⟫_ℝ := by rw [← hsym, real_inner_comm]
    rw [map_add, map_smul, inner_add_left, inner_add_right, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, real_inner_smul_left, real_inner_smul_right, hvu] at h
    nlinarith [h]
  have hd := discrim_le_zero hquad
  unfold discrim at hd
  nlinarith [hd]

/-- Lower bound: `‖S y‖² ≤ (1+ε) ⟪y, S y⟫` for symmetric `S` with `‖S − id‖ ≤ ε < 1`. -/
theorem norm_map_sq_le (S : E →L[ℝ] E) (hsym : ∀ x y, ⟪S x, y⟫_ℝ = ⟪x, S y⟫_ℝ) (ε : ℝ)
    (hε : ‖S - 1‖ ≤ ε) (hε1 : ε < 1) (y : E) :
    ‖S y‖ ^ 2 ≤ (1 + ε) * ⟪y, S y⟫_ℝ := by
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hε
  have hpos : ∀ z, 0 ≤ ⟪z, S z⟫_ℝ := fun z => by
    have := (quad_bounds S ε hε z).1
    nlinarith [sq_nonneg ‖z‖]
  have hcs := inner_map_sq_le S hsym hpos y (S y)
  have h1 : ⟪y, S (S y)⟫_ℝ = ‖S y‖ ^ 2 := by rw [← hsym, real_inner_self_eq_norm_sq]
  have h2 : ⟪S y, S (S y)⟫_ℝ ≤ (1 + ε) * ‖S y‖ ^ 2 := (quad_bounds S ε hε (S y)).2
  rw [h1] at hcs
  -- `‖Sy‖⁴ ≤ ⟪y,Sy⟫ (1+ε) ‖Sy‖²`; divide by `‖Sy‖²` when it is positive.
  rcases eq_or_lt_of_le (sq_nonneg ‖S y‖) with h0 | h0
  · rw [← h0]; exact mul_nonneg (by linarith) (hpos y)
  · have hy := hpos y
    have : ‖S y‖ ^ 2 * ‖S y‖ ^ 2 ≤ ((1 + ε) * ⟪y, S y⟫_ℝ) * ‖S y‖ ^ 2 := by
      calc ‖S y‖ ^ 2 * ‖S y‖ ^ 2 = (‖S y‖ ^ 2) ^ 2 := by ring
        _ ≤ ⟪y, S y⟫_ℝ * ⟪S y, S (S y)⟫_ℝ := hcs
        _ ≤ ⟪y, S y⟫_ℝ * ((1 + ε) * ‖S y‖ ^ 2) := by gcongr
        _ = ((1 + ε) * ⟪y, S y⟫_ℝ) * ‖S y‖ ^ 2 := by ring
    exact le_of_mul_le_mul_right this h0

/-- Upper bound: `(1−ε) ⟪y, S y⟫ ≤ ‖S y‖²` when `‖S − id‖ ≤ ε` (from `S − (1−ε) id ⪰ 0`). -/
theorem inner_map_le_norm_sq (S : E →L[ℝ] E) (ε : ℝ) (hε : ‖S - 1‖ ≤ ε) (hε1 : ε < 1) (y : E) :
    (1 - ε) * ⟪y, S y⟫_ℝ ≤ ‖S y‖ ^ 2 := by
  -- write `S y = (1−ε) y + b` with `⟪y, b⟫ ≥ 0`.
  set b := S y - (1 - ε) • y with hb
  have hSy : S y = (1 - ε) • y + b := by rw [hb]; abel
  have hyb : 0 ≤ ⟪y, b⟫_ℝ := by
    rw [hb, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
    linarith [(quad_bounds S ε hε y).1]
  have hnorm : ‖S y‖ ^ 2 = (1 - ε) ^ 2 * ‖y‖ ^ 2 + 2 * (1 - ε) * ⟪y, b⟫_ℝ + ‖b‖ ^ 2 := by
    rw [hSy, norm_add_sq_real, norm_smul, real_inner_smul_left, mul_pow, Real.norm_eq_abs,
      sq_abs]; ring
  have hinner : ⟪y, S y⟫_ℝ = (1 - ε) * ‖y‖ ^ 2 + ⟪y, b⟫_ℝ := by
    rw [hSy, inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  rw [hnorm, hinner]
  nlinarith [sq_nonneg ‖b‖, mul_nonneg (sub_nonneg.2 hε1.le) hyb]

/-- **Corollary 2.5 (sandwich).**  For a symmetric `S` with `‖S − id‖ ≤ ε < 1` and any right inverse
`Sinv` (`S (Sinv x) = x`), every `x` satisfies `(1+ε)⁻¹ ‖x‖² ≤ ⟪x, Sinv x⟫ ≤ (1−ε)⁻¹ ‖x‖²`. -/
theorem sandwich (S : E →L[ℝ] E) (hsym : ∀ x y, ⟪S x, y⟫_ℝ = ⟪x, S y⟫_ℝ) (ε : ℝ)
    (hε : ‖S - 1‖ ≤ ε) (hε1 : ε < 1) (Sinv : E → E) (hinv : ∀ x, S (Sinv x) = x) (x : E) :
    (1 + ε)⁻¹ * ‖x‖ ^ 2 ≤ ⟪x, Sinv x⟫_ℝ ∧ ⟪x, Sinv x⟫_ℝ ≤ (1 - ε)⁻¹ * ‖x‖ ^ 2 := by
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hε
  set y := Sinv x with hy
  have hx : x = S y := (hinv x).symm
  have hq : ⟪x, Sinv x⟫_ℝ = ⟪y, S y⟫_ℝ := by rw [← hy, hx, hsym, real_inner_comm]
  rw [hq, hx]
  constructor
  · rw [inv_mul_le_iff₀ (by linarith)]
    exact norm_map_sq_le S hsym ε hε hε1 y
  · rw [le_inv_mul_iff₀ (by linarith)]
    exact inner_map_le_norm_sq S ε hε hε1 y

/-- The sandwich constants are the ones Proposition 2.4 needs: `0 < λ₋ ≤ λ₊`. -/
theorem sandwich_constants (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    0 < (1 + ε)⁻¹ ∧ (1 + ε)⁻¹ ≤ (1 - ε)⁻¹ := by
  constructor
  · positivity
  · exact inv_anti₀ (by linarith) (by linarith)

variable [FiniteDimensional ℝ E]

/-- A symmetric `S` with `‖S − id‖ ≤ ε < 1` on a finite-dimensional space is invertible: there is a
continuous linear two-sided inverse. -/
theorem exists_inverse (S : E →L[ℝ] E) (ε : ℝ) (hε : ‖S - 1‖ ≤ ε) (hε1 : ε < 1) :
    ∃ Sinv : E →L[ℝ] E, (∀ x, S (Sinv x) = x) ∧ (∀ x, Sinv (S x) = x) := by
  have hinj : Function.Injective (S : E →ₗ[ℝ] E) := by
    intro a b hab
    have h0 : S (a - b) = 0 := by
      simp only [ContinuousLinearMap.coe_coe] at hab
      rw [map_sub, hab, sub_self]
    have hq := (quad_bounds S ε hε (a - b)).1
    rw [h0, inner_zero_right] at hq
    have : ‖a - b‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖a - b‖]
    have : ‖a - b‖ = 0 := by nlinarith [sq_nonneg ‖a - b‖, norm_nonneg (a - b)]
    exact sub_eq_zero.1 (norm_eq_zero.1 this)
  have hsurj : Function.Surjective (S : E →ₗ[ℝ] E) := LinearMap.injective_iff_surjective.1 hinj
  let e : E ≃ₗ[ℝ] E := LinearEquiv.ofBijective (S : E →ₗ[ℝ] E) ⟨hinj, hsurj⟩
  have he : ∀ z, e z = S z := fun z => rfl
  refine ⟨LinearMap.toContinuousLinearMap (e.symm : E →ₗ[ℝ] E), fun x => ?_, fun x => ?_⟩
  · have h := e.apply_symm_apply x
    rw [he] at h
    exact h
  · have h := e.symm_apply_apply x
    rw [he] at h
    exact h

/-- **Corollary 2.5**, packaged: under `‖S − id‖ ≤ ε < 1` and symmetry, `S` has a continuous linear
inverse `Sinv` and `q x := ⟪x, Sinv x⟫` satisfies the sandwich `λ₋ ‖x‖² ≤ q x ≤ λ₊ ‖x‖²` with
`λ₋ = (1+ε)⁻¹`, `λ₊ = (1−ε)⁻¹`, `0 < λ₋ ≤ λ₊` (the hypotheses of Proposition 2.4 after absorbing
`σ²`). -/
theorem sandwich_of_sigma_sub_id (S : E →L[ℝ] E) (hsym : ∀ x y, ⟪S x, y⟫_ℝ = ⟪x, S y⟫_ℝ) (ε : ℝ)
    (hε : ‖S - 1‖ ≤ ε) (hε1 : ε < 1) :
    ∃ Sinv : E →L[ℝ] E, (∀ x, S (Sinv x) = x) ∧ (∀ x, Sinv (S x) = x) ∧
      (0 < (1 + ε)⁻¹ ∧ (1 + ε)⁻¹ ≤ (1 - ε)⁻¹) ∧
      ∀ x, (1 + ε)⁻¹ * ‖x‖ ^ 2 ≤ ⟪x, Sinv x⟫_ℝ ∧ ⟪x, Sinv x⟫_ℝ ≤ (1 - ε)⁻¹ * ‖x‖ ^ 2 := by
  obtain ⟨Sinv, h1, h2⟩ := exists_inverse S ε hε hε1
  exact ⟨Sinv, h1, h2, sandwich_constants ε ((norm_nonneg _).trans hε) hε1,
    sandwich S hsym ε hε hε1 Sinv h1⟩

end Sandwich

/-! ## Stretch: the trace bounds of Lemma 3(b)/(d) from `‖Σ̂ − id‖ ≤ ε` -/

section Trace

open scoped InnerProductSpace
open Module

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `‖S‖ ≤ 1 + ε` when `‖S − id‖ ≤ ε`. -/
theorem opNorm_le_one_add (S : E →L[ℝ] E) (ε : ℝ) (hε : ‖S - 1‖ ≤ ε) : ‖S‖ ≤ 1 + ε := by
  calc ‖S‖ = ‖(1 : E →L[ℝ] E) + (S - 1)‖ := by rw [add_sub_cancel]
    _ ≤ ‖(1 : E →L[ℝ] E)‖ + ‖S - 1‖ := norm_add_le _ _
    _ ≤ 1 + ε := add_le_add ContinuousLinearMap.norm_id_le hε

/-- The orthogonal projection onto the span of `v : Fin k → E` (orthonormal), as the rank-one sum
`x ↦ ∑ j ⟪v j, x⟫ v j`. -/
def proj {k : ℕ} (v : Fin k → E) : E →ₗ[ℝ] E where
  toFun x := ∑ j, ⟪v j, x⟫_ℝ • v j
  map_add' x y := by simp [inner_add_right, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [inner_smul_right, Finset.smul_sum, smul_smul]

variable {k : ℕ} {v : Fin k → E}

theorem proj_apply (v : Fin k → E) (x : E) : proj v x = ∑ j, ⟪v j, x⟫_ℝ • v j := rfl

theorem proj_apply_self (hv : Orthonormal ℝ v) (j : Fin k) : proj v (v j) = v j := by
  rw [proj_apply]
  simp [orthonormal_iff_ite.1 hv, ite_smul]

theorem proj_proj (hv : Orthonormal ℝ v) (x : E) : proj v (proj v x) = proj v x := by
  simp only [proj_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hv.inner_right_fintype (fun j => ⟪v j, x⟫_ℝ) i]

theorem proj_symm (v : Fin k → E) (x y : E) : ⟪proj v x, y⟫_ℝ = ⟪x, proj v y⟫_ℝ := by
  simp only [proj_apply, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [real_inner_comm (v j) x]
  ring

theorem norm_proj_le (hv : Orthonormal ℝ v) (y : E) : ‖proj v y‖ ≤ ‖y‖ := by
  have h : ‖proj v y‖ ^ 2 ≤ ‖y‖ * ‖proj v y‖ := by
    rw [← real_inner_self_eq_norm_sq, proj_symm, proj_proj hv]
    exact real_inner_le_norm _ _
  nlinarith [norm_nonneg (proj v y), norm_nonneg y]

/-- The span of an orthonormal `k`-tuple has dimension `k`: `proj v` is a rank-`k` projection. -/
theorem finrank_span_eq (hv : Orthonormal ℝ v) :
    finrank ℝ (Submodule.span ℝ (Set.range v)) = k := by
  rw [finrank_span_eq_card hv.linearIndependent, Fintype.card_fin]

variable [FiniteDimensional ℝ E]

/-- Lemma 3(b): `tr Σ̂ ≤ K(1+ε)` with `K = dim E`. -/
theorem trace_le (S : E →L[ℝ] E) (ε : ℝ) (hε : ‖S - 1‖ ≤ ε) :
    LinearMap.trace ℝ E (S : E →ₗ[ℝ] E) ≤ (finrank ℝ E : ℝ) * (1 + ε) := by
  let b := stdOrthonormalBasis ℝ E
  rw [LinearMap.trace_eq_sum_inner (S : E →ₗ[ℝ] E) b]
  calc ∑ i, ⟪b i, (S : E →ₗ[ℝ] E) (b i)⟫_ℝ ≤ ∑ _i : Fin (finrank ℝ E), (1 + ε) := by
        apply Finset.sum_le_sum
        intro i _
        have h := (quad_bounds S ε hε (b i)).2
        rw [b.orthonormal.1 i] at h
        simpa using h
    _ = (finrank ℝ E : ℝ) * (1 + ε) := by simp; ring

/-- Lemma 3(b): `tr Σ̂² ≤ K(1+ε)²` with `K = dim E`. -/
theorem trace_sq_le (S : E →L[ℝ] E) (ε : ℝ) (hε : ‖S - 1‖ ≤ ε) :
    LinearMap.trace ℝ E ((S : E →ₗ[ℝ] E) * (S : E →ₗ[ℝ] E)) ≤ (finrank ℝ E : ℝ) * (1 + ε) ^ 2 := by
  let b := stdOrthonormalBasis ℝ E
  have hS := opNorm_le_one_add S ε hε
  rw [LinearMap.trace_eq_sum_inner _ b]
  calc ∑ i, ⟪b i, ((S : E →ₗ[ℝ] E) * (S : E →ₗ[ℝ] E)) (b i)⟫_ℝ
      ≤ ∑ _i : Fin (finrank ℝ E), (1 + ε) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        rw [Module.End.mul_apply]
        simp only [ContinuousLinearMap.coe_coe]
        calc ⟪b i, S (S (b i))⟫_ℝ ≤ ‖b i‖ * ‖S (S (b i))‖ := real_inner_le_norm _ _
          _ ≤ ‖b i‖ * (‖S‖ * (‖S‖ * ‖b i‖)) := by
              gcongr
              exact (S.le_opNorm _).trans (by gcongr; exact S.le_opNorm _)
          _ = ‖S‖ ^ 2 := by rw [b.orthonormal.1 i]; ring
          _ ≤ (1 + ε) ^ 2 := by gcongr
    _ = (finrank ℝ E : ℝ) * (1 + ε) ^ 2 := by simp

/-- `tr(P_V A) = ∑_j ⟪v_j, A v_j⟫` for the rank-one sum `P_V = proj v` and any linear `A`. -/
theorem trace_proj_comp (v : Fin k → E) (A : E →ₗ[ℝ] E) :
    LinearMap.trace ℝ E (proj v ∘ₗ A) = ∑ j, ⟪v j, A (v j)⟫_ℝ := by
  let b := stdOrthonormalBasis ℝ E
  rw [LinearMap.trace_eq_sum_inner _ b]
  simp only [LinearMap.comp_apply, proj_apply, inner_sum, real_inner_smul_right]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hrep : A (v j) = ∑ i, ⟪b i, v j⟫_ℝ • A (b i) := by
    conv_lhs => rw [← b.sum_repr' (v j)]
    rw [map_sum]
    simp only [map_smul]
  rw [hrep, inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_smul_right]
  ring

/-- Lemma 3(d): `tr(P_V Σ̂) ≤ k ‖Σ̂‖` for the orthogonal projection `P_V` onto the span of an
orthonormal `k`-tuple. -/
theorem trace_proj_comp_le (hv : Orthonormal ℝ v) (S : E →L[ℝ] E) :
    LinearMap.trace ℝ E (proj v ∘ₗ (S : E →ₗ[ℝ] E)) ≤ k * ‖S‖ := by
  rw [trace_proj_comp]
  calc ∑ j, ⟪v j, (S : E →ₗ[ℝ] E) (v j)⟫_ℝ ≤ ∑ _j : Fin k, ‖S‖ := by
        apply Finset.sum_le_sum
        intro j _
        simp only [ContinuousLinearMap.coe_coe]
        calc ⟪v j, S (v j)⟫_ℝ ≤ ‖v j‖ * ‖S (v j)‖ := real_inner_le_norm _ _
          _ ≤ ‖v j‖ * (‖S‖ * ‖v j‖) := by gcongr; exact S.le_opNorm _
          _ = ‖S‖ := by rw [hv.1 j]; ring
    _ = k * ‖S‖ := by simp

/-- Lemma 3(d): `tr((P_V Σ̂ P_V)²) ≤ k ‖Σ̂‖²` for symmetric `Σ̂`. -/
theorem trace_proj_sq_le (hv : Orthonormal ℝ v) (S : E →L[ℝ] E)
    (hsym : ∀ x y, ⟪S x, y⟫_ℝ = ⟪x, S y⟫_ℝ) :
    LinearMap.trace ℝ E ((proj v ∘ₗ (S : E →ₗ[ℝ] E) ∘ₗ proj v) *
      (proj v ∘ₗ (S : E →ₗ[ℝ] E) ∘ₗ proj v)) ≤ k * ‖S‖ ^ 2 := by
  have hcomp : (proj v ∘ₗ (S : E →ₗ[ℝ] E) ∘ₗ proj v) * (proj v ∘ₗ (S : E →ₗ[ℝ] E) ∘ₗ proj v)
      = proj v ∘ₗ ((S : E →ₗ[ℝ] E) ∘ₗ proj v ∘ₗ proj v ∘ₗ (S : E →ₗ[ℝ] E) ∘ₗ proj v) := by
    rw [Module.End.mul_eq_comp]
    simp only [LinearMap.comp_assoc]
  rw [hcomp, trace_proj_comp]
  calc ∑ j, ⟪v j, ((S : E →ₗ[ℝ] E) ∘ₗ proj v ∘ₗ proj v ∘ₗ (S : E →ₗ[ℝ] E) ∘ₗ proj v) (v j)⟫_ℝ
      ≤ ∑ _j : Fin k, ‖S‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, proj_apply_self hv,
          proj_proj hv]
        calc ⟪v j, S (proj v (S (v j)))⟫_ℝ = ⟪S (v j), proj v (S (v j))⟫_ℝ := (hsym _ _).symm
          _ ≤ ‖S (v j)‖ * ‖proj v (S (v j))‖ := real_inner_le_norm _ _
          _ ≤ ‖S (v j)‖ * ‖S (v j)‖ := by gcongr; exact norm_proj_le hv _
          _ ≤ (‖S‖ * ‖v j‖) * (‖S‖ * ‖v j‖) := by gcongr <;> exact S.le_opNorm _
          _ = ‖S‖ ^ 2 := by rw [hv.1 j]; ring
    _ = k * ‖S‖ ^ 2 := by simp

end Trace

end SymbolicIV.Lemma3Algebra

#print axioms SymbolicIV.Lemma3Algebra.bernSol_exp_ge
#print axioms SymbolicIV.Lemma3Algebra.bernstein_tail_le_exp
#print axioms SymbolicIV.Lemma3Algebra.epsN_eq
#print axioms SymbolicIV.Lemma3Algebra.hkz_div_le_zt2
#print axioms SymbolicIV.Lemma3Algebra.hkz_div_le_zt2_proj
#print axioms SymbolicIV.Lemma3Algebra.mcdiarmid_const
#print axioms SymbolicIV.Lemma3Algebra.one_centre
#print axioms SymbolicIV.Lemma3Algebra.all_centres
#print axioms SymbolicIV.Lemma3Algebra.lemma3c_constant
#print axioms SymbolicIV.Lemma3Algebra.sandwich
#print axioms SymbolicIV.Lemma3Algebra.sandwich_of_sigma_sub_id
#print axioms SymbolicIV.Lemma3Algebra.trace_le
#print axioms SymbolicIV.Lemma3Algebra.trace_sq_le
#print axioms SymbolicIV.Lemma3Algebra.trace_proj_comp_le
#print axioms SymbolicIV.Lemma3Algebra.trace_proj_sq_le
