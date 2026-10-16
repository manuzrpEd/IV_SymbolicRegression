import Mathlib

/-!
# Theorem 3(b): consistency as the formula size grows

Formalizes the deterministic parts of the proof of Theorem 3(b) of THEORY.md (§6;
paper: theory.tex / appendix-proofs.tex, same numbering), unit U08 of `FORMALIZATION_PLAN.md`:
Step 1 (identification modulus, uniform in `K`), the algebra of the last line of Step 2, and Steps 3–4.
The probabilistic parts of Step 2 (`‖ū‖ →_p 0` by Chebyshev, `sup ‖D_n‖ →_p 0` by Lemma 3(c) and a
union bound) are not re-proved; they enter the assembled statements through the hypothesis
`|Q_n(f) − Q_{K_n}(f)| ≤ R_n` at the two functions where the proof uses it.

## Abstract setting

* `H₀` is a real inner product space (`L²(P_X)`), `H'` a real inner product space (`L²(P_Z)`).
* `T : H₀ →L[ℝ] H'` is the conditional-expectation operator; `‖T‖ ≤ 1` where the paper uses it.
* `𝓗 : Set H₀` is the compact class (S1), `f₀ ∈ 𝓗`; (S2) reads `∀ f ∈ 𝓗, T (f - f₀) = 0 → f = f₀`.
* The projections `Π_{K_n}` are modelled in two layers: a sequence `P : ℕ → H' →L[ℝ] H'` with
  `‖h − P n h‖ ≤ ‖h‖` (that is `‖I − Π_{K_n}‖ ≤ 1`) converging strongly to the identity
  (`strongLimitId`), and the specialization `P n = (V n).starProjection` for a sequence of subspaces
  `V n` with orthogonal projections (S4), where the bound `‖h − P n h‖ ≤ ‖h‖` is proved.
* `omega T 𝓗 f₀ ε := sInf {‖T (f − f₀)‖² : f ∈ 𝓗, ε ≤ ‖f − f₀‖}` is the identification modulus
  `ω(ε)`; `QK (P n) T f₀ f := ‖P n (T (f − f₀))‖²` is the population criterion `Q_{K_n}(f)`.

## Results

* `omega_pos` : `ω(ε) > 0` for `ε > 0` when `{f ∈ 𝓗 : ‖f − f₀‖ ≥ ε}` is nonempty (Step 1).
* `uniform_strong_convergence` : strong convergence is uniform on compact sets, via a finite net.
* `step1` : (6.1) — there is `n₀(ε)` with `Q_{K_n}(f) ≥ ω(ε)/4` for `n ≥ n₀`, `f ∈ 𝓗`, `‖f − f₀‖ ≥ ε`.
* `step1_starProjection` : the same for `P n = (V n).starProjection`.
* `norm_sq_perturb_bound` : the algebra of Step 2's last line,
  `|‖u + g + D‖² − ‖g‖²| ≤ (‖u‖ + ‖D‖)(2M + ‖u‖ + ‖D‖)` when `‖g‖ ≤ M`.
* `QK_le_norm_sq` : `Q_{K_n}(f) ≤ ‖f − f₀‖²` (from `‖T‖ ≤ 1`, `‖Π‖ ≤ 1`).
* `step3` : the basic inequality `Q_{K_n}(f̂) ≤ ‖f* − f₀‖² + 2R + η`.
* `step4` : `‖f̂ − f₀‖ ≥ ε → Q_{K_n}(f̂) ≥ ω(ε)/4` for `n ≥ n₀(ε)`.
* `thm3b_deterministic` : Theorem 3(b) with the stochastic inputs replaced by deterministic
  sequences: if `‖f*_n − f₀‖ → 0`, `R_n → 0`, `η_n → 0`, then `‖f̂_n − f₀‖ → 0`.
* `thm3b_inProbability` : Theorem 3(b) in probability: on a measure space `Ω`, if `R_n` and `η_n`
  converge to `0` in measure and `‖f*_n − f₀‖ → 0`, then `‖f̂_n − f₀‖ → 0` in measure
  (`MeasureTheory.TendstoInMeasure`).
* `Delta_tendsto_zero` : the stretch goal, `Δ_n(t) → 0` under (S6).

## Hypotheses beyond the paper's statement

* In `omega_pos`, the set `{f ∈ 𝓗 : ‖f − f₀‖ ≥ ε}` is assumed nonempty: Lean's `sInf ∅ = 0` on `ℝ`
  (the paper's convention `inf ∅ = +∞` makes the claim `ω(ε) > 0` true vacuously). The Step 1
  conclusion (6.1) and everything downstream hold for every `ε > 0` without this assumption, since
  (6.1) is vacuous when the set is empty.
* The assembled statements take `|Q_n(f) − Q_{K_n}(f)| ≤ R_n` at `f = f̂_n` and `f = f*_n` as a
  hypothesis (the paper's `R_n := sup_{𝓗_n} |Q_n − Q_{K_n}|`, bounded in Step 2 by probabilistic
  tools), and `Q_n(f̂_n) ≤ Q_n(f*_n) + η_n` (the paper's near-minimization over `𝓗_n`, applied at
  `f*_n ∈ 𝓗_n`). The probabilistic version takes `R_n →_p 0` and `η_n →_p 0` as hypotheses
  (`TendstoInMeasure`), which is the output of Step 2 and (S6).
* In `Delta_tendsto_zero`: `Λ_n ≥ 1` (the paper's bound `log Λ_n ≤ a(L_n + log n)` is used as an
  upper bound only; `Λ_n ≥ 1` removes the degenerate case of a Lipschitz constant below one, which
  can always be replaced by one), `ζ_n ≥ 0`, `K_n ≥ 0`, `M > 0`, `C ≥ 0`, `m ≥ 1`, `t ≥ 0`, `a ≥ 0`.
-/

open scoped RealInnerProductSpace
open Filter Topology

noncomputable section

namespace SymbolicIV.Thm3b

variable {H₀ H' : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀]
  [NormedAddCommGroup H'] [InnerProductSpace ℝ H']

/-! ### Definitions -/

/-- The identification modulus `ω(ε) := inf {‖T(f − f₀)‖² : f ∈ 𝓗, ‖f − f₀‖ ≥ ε}`. -/
def omega (T : H₀ →L[ℝ] H') (𝓗 : Set H₀) (f₀ : H₀) (ε : ℝ) : ℝ :=
  sInf ((fun f => ‖T (f - f₀)‖ ^ 2) '' {f ∈ 𝓗 | ε ≤ ‖f - f₀‖})

/-- The population criterion `Q_K(f) = ‖Π_K T(f − f₀)‖²` for a projection `P`. -/
def QK (P : H' →L[ℝ] H') (T : H₀ →L[ℝ] H') (f₀ f : H₀) : ℝ :=
  ‖P (T (f - f₀))‖ ^ 2

/-- Strong convergence of a sequence of operators to the identity. -/
def strongLimitId (P : ℕ → H' →L[ℝ] H') : Prop :=
  ∀ h : H', Tendsto (fun n => P n h) atTop (𝓝 h)

/-! ### Step 1: the identification modulus -/

theorem omega_nonneg (T : H₀ →L[ℝ] H') (𝓗 : Set H₀) (f₀ : H₀) (ε : ℝ) :
    0 ≤ omega T 𝓗 f₀ ε := by
  apply Real.sInf_nonneg
  rintro _ ⟨f, -, rfl⟩
  positivity

theorem omega_le (T : H₀ →L[ℝ] H') (𝓗 : Set H₀) (f₀ : H₀) (ε : ℝ) {f : H₀} (hf : f ∈ 𝓗)
    (hε : ε ≤ ‖f - f₀‖) : omega T 𝓗 f₀ ε ≤ ‖T (f - f₀)‖ ^ 2 := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro _ ⟨g, -, rfl⟩
    positivity
  · exact ⟨f, ⟨hf, hε⟩, rfl⟩

omit [InnerProductSpace ℝ H₀] in
/-- The set `{f ∈ 𝓗 : ‖f − f₀‖ ≥ ε}` is compact (closed in the compact `𝓗`). -/
theorem isCompact_farSet {𝓗 : Set H₀} (h𝓗 : IsCompact 𝓗) (f₀ : H₀) (ε : ℝ) :
    IsCompact {f ∈ 𝓗 | ε ≤ ‖f - f₀‖} := by
  have hcl : IsClosed {f : H₀ | ε ≤ ‖f - f₀‖} :=
    isClosed_le continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))
  exact h𝓗.inter_right hcl

/-- Step 1, first claim: `ω(ε) > 0` for `ε > 0` (when the set defining it is nonempty). -/
theorem omega_pos (T : H₀ →L[ℝ] H') {𝓗 : Set H₀} (h𝓗 : IsCompact 𝓗) {f₀ : H₀}
    (hid : ∀ f ∈ 𝓗, T (f - f₀) = 0 → f = f₀) {ε : ℝ} (hε : 0 < ε)
    (hne : {f ∈ 𝓗 | ε ≤ ‖f - f₀‖}.Nonempty) : 0 < omega T 𝓗 f₀ ε := by
  set S := {f ∈ 𝓗 | ε ≤ ‖f - f₀‖} with hS
  have hcpt : IsCompact S := isCompact_farSet h𝓗 f₀ ε
  have hcont : ContinuousOn (fun f : H₀ => ‖T (f - f₀)‖ ^ 2) S :=
    (((T.continuous.comp (continuous_id.sub continuous_const)).norm).pow 2).continuousOn
  obtain ⟨fm, hfmS, hmin⟩ := hcpt.exists_isMinOn hne hcont
  have hpos : 0 < ‖T (fm - f₀)‖ ^ 2 := by
    have hne0 : T (fm - f₀) ≠ 0 := by
      intro h0
      have := hid fm hfmS.1 h0
      have h1 : ε ≤ ‖fm - f₀‖ := hfmS.2
      rw [this, sub_self, norm_zero] at h1
      linarith
    positivity
  refine lt_of_lt_of_le hpos ?_
  apply le_csInf (hne.image _)
  rintro _ ⟨f, hf, rfl⟩
  exact hmin hf

/-- Strong convergence is uniform on compact sets: given `δ > 0`, eventually `‖h − P n h‖ ≤ 2δ` for
every `h` in the compact `G` (finite `δ`-net and `‖I − P n‖ ≤ 1`). -/
theorem uniform_strong_convergence {P : ℕ → H' →L[ℝ] H'}
    (hP : ∀ n (h : H'), ‖h - P n h‖ ≤ ‖h‖) (hconv : strongLimitId P)
    {G : Set H'} (hG : IsCompact G) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n in atTop, ∀ h ∈ G, ‖h - P n h‖ ≤ 2 * δ := by
  obtain ⟨t, -, htfin, hcover⟩ := Metric.finite_approx_of_totallyBounded hG.totallyBounded δ hδ
  have hev : ∀ᶠ n in atTop, ∀ y ∈ t, ‖y - P n y‖ ≤ δ := by
    rw [eventually_all_finite htfin]
    intro y _
    have := (hconv y).eventually (Metric.closedBall_mem_nhds y hδ)
    filter_upwards [this] with n hn
    rw [dist_eq_norm] at hn
    rwa [← norm_neg, neg_sub]
  filter_upwards [hev] with n hn h hh
  obtain ⟨y, hy, hhy⟩ := Set.mem_iUnion₂.1 (hcover hh)
  rw [Metric.mem_ball, dist_eq_norm] at hhy
  have e : h - P n h = ((h - y) - P n (h - y)) + (y - P n y) := by
    simp only [map_sub]; abel
  calc ‖h - P n h‖ = ‖((h - y) - P n (h - y)) + (y - P n y)‖ := by rw [e]
    _ ≤ ‖(h - y) - P n (h - y)‖ + ‖y - P n y‖ := norm_add_le _ _
    _ ≤ ‖h - y‖ + δ := add_le_add (hP n _) (hn y hy)
    _ ≤ 2 * δ := by linarith

/-- Step 1, conclusion (6.1): there is `n₀(ε)` such that for `n ≥ n₀(ε)` and every `f ∈ 𝓗` with
`‖f − f₀‖ ≥ ε`, `‖Π_{K_n} T(f − f₀)‖ ≥ ½√ω(ε)` and `Q_{K_n}(f) ≥ ω(ε)/4`. -/
theorem step1 (T : H₀ →L[ℝ] H') {𝓗 : Set H₀} (h𝓗 : IsCompact 𝓗) {f₀ : H₀}
    (hid : ∀ f ∈ 𝓗, T (f - f₀) = 0 → f = f₀) {P : ℕ → H' →L[ℝ] H'}
    (hP : ∀ n (h : H'), ‖h - P n h‖ ≤ ‖h‖) (hconv : strongLimitId P) {ε : ℝ} (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ f ∈ 𝓗, ε ≤ ‖f - f₀‖ →
      Real.sqrt (omega T 𝓗 f₀ ε) / 2 ≤ ‖P n (T (f - f₀))‖ ∧
      omega T 𝓗 f₀ ε / 4 ≤ QK (P n) T f₀ f := by
  set ω := omega T 𝓗 f₀ ε with hω
  have hω0 : 0 ≤ ω := omega_nonneg T 𝓗 f₀ ε
  -- the compact image `G = T '' (𝓗 − f₀)`
  have hG : IsCompact ((fun f => T (f - f₀)) '' 𝓗) :=
    h𝓗.image (T.continuous.comp (continuous_id.sub continuous_const))
  by_cases hne : {f ∈ 𝓗 | ε ≤ ‖f - f₀‖}.Nonempty
  · have hωpos : 0 < ω := omega_pos T h𝓗 hid hε hne
    have hδ : 0 < Real.sqrt ω / 4 := by positivity
    obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (uniform_strong_convergence hP hconv hG hδ)
    refine ⟨n₀, fun n hn f hf hεf => ?_⟩
    have hbound : ‖T (f - f₀) - P n (T (f - f₀))‖ ≤ 2 * (Real.sqrt ω / 4) :=
      hn₀ n hn _ ⟨f, hf, rfl⟩
    have hωle : ω ≤ ‖T (f - f₀)‖ ^ 2 := omega_le T 𝓗 f₀ ε hf hεf
    have hsqrt : Real.sqrt ω ≤ ‖T (f - f₀)‖ := by
      calc Real.sqrt ω ≤ Real.sqrt (‖T (f - f₀)‖ ^ 2) := Real.sqrt_le_sqrt hωle
        _ = ‖T (f - f₀)‖ := Real.sqrt_sq (norm_nonneg _)
    have hrev : ‖T (f - f₀)‖ - ‖T (f - f₀) - P n (T (f - f₀))‖ ≤ ‖P n (T (f - f₀))‖ := by
      have := norm_sub_norm_le (T (f - f₀)) (T (f - f₀) - P n (T (f - f₀)))
      rwa [sub_sub_cancel] at this
    have h1 : Real.sqrt ω / 2 ≤ ‖P n (T (f - f₀))‖ := by linarith
    refine ⟨h1, ?_⟩
    have hsq : (Real.sqrt ω / 2) ^ 2 ≤ ‖P n (T (f - f₀))‖ ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    have : (Real.sqrt ω / 2) ^ 2 = ω / 4 := by
      rw [div_pow, Real.sq_sqrt hω0]; norm_num
    unfold QK
    linarith
  · refine ⟨0, fun n _ f hf hεf => absurd ⟨f, hf, hεf⟩ hne⟩

/-- `‖I − Π_V‖ ≤ 1` for the orthogonal projection onto a subspace `V`. -/
theorem norm_sub_starProjection_le (V : Submodule ℝ H') [V.HasOrthogonalProjection] (h : H') :
    ‖h - V.starProjection h‖ ≤ ‖h‖ := by
  rw [← Submodule.starProjection_orthogonal_val]
  exact Submodule.norm_starProjection_apply_le _ h

/-- Step 1 for the orthogonal projections `Π_{K_n}` onto nested subspaces `V n` converging strongly
to the identity (assumption (S4)). -/
theorem step1_starProjection (T : H₀ →L[ℝ] H') {𝓗 : Set H₀} (h𝓗 : IsCompact 𝓗) {f₀ : H₀}
    (hid : ∀ f ∈ 𝓗, T (f - f₀) = 0 → f = f₀) (V : ℕ → Submodule ℝ H')
    [∀ n, (V n).HasOrthogonalProjection]
    (hconv : ∀ h : H', Tendsto (fun n => (V n).starProjection h) atTop (𝓝 h))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ f ∈ 𝓗, ε ≤ ‖f - f₀‖ →
      omega T 𝓗 f₀ ε / 4 ≤ ‖(V n).starProjection (T (f - f₀))‖ ^ 2 := by
  obtain ⟨n₀, hn₀⟩ := step1 T h𝓗 hid (P := fun n => (V n).starProjection)
    (fun n h => norm_sub_starProjection_le (V n) h) hconv hε
  exact ⟨n₀, fun n hn f hf hεf => (hn₀ n hn f hf hεf).2⟩

/-! ### Step 2: the algebra of the last line -/

/-- The last line of Step 2: with `‖g‖ ≤ M` and perturbations `u, D`,
`|‖u + g + D‖² − ‖g‖²| ≤ (‖u‖ + ‖D‖)(2M + ‖u‖ + ‖D‖)`. -/
theorem norm_sq_perturb_bound (u g D : H') {M : ℝ} (hM : ‖g‖ ≤ M) :
    |‖u + g + D‖ ^ 2 - ‖g‖ ^ 2| ≤ (‖u‖ + ‖D‖) * (2 * M + ‖u‖ + ‖D‖) := by
  have e : u + g + D = g + (u + D) := by abel
  rw [e, norm_add_sq_real]
  have hinner := abs_real_inner_le_norm g (u + D)
  have hr : ‖u + D‖ ≤ ‖u‖ + ‖D‖ := norm_add_le u D
  have hr0 : 0 ≤ ‖u + D‖ := norm_nonneg _
  have hg0 : 0 ≤ ‖g‖ := norm_nonneg _
  have hu0 : 0 ≤ ‖u‖ := norm_nonneg _
  have hD0 : 0 ≤ ‖D‖ := norm_nonneg _
  rw [abs_le] at hinner ⊢
  constructor <;> nlinarith [sq_nonneg (‖u + D‖ - (‖u‖ + ‖D‖))]

/-- `Q_K(f) ≤ ‖f − f₀‖²` from `‖T‖ ≤ 1` and `‖Π‖ ≤ 1`. -/
theorem QK_le_norm_sq {P : H' →L[ℝ] H'} (hP : ∀ h, ‖P h‖ ≤ ‖h‖) {T : H₀ →L[ℝ] H'} (hT : ‖T‖ ≤ 1)
    (f₀ f : H₀) : QK P T f₀ f ≤ ‖f - f₀‖ ^ 2 := by
  unfold QK
  have h1 : ‖P (T (f - f₀))‖ ≤ ‖f - f₀‖ := by
    calc ‖P (T (f - f₀))‖ ≤ ‖T (f - f₀)‖ := hP _
      _ ≤ ‖T‖ * ‖f - f₀‖ := T.le_opNorm _
      _ ≤ 1 * ‖f - f₀‖ := by gcongr
      _ = ‖f - f₀‖ := one_mul _
  exact pow_le_pow_left₀ (norm_nonneg _) h1 2

/-! ### Steps 3 and 4 -/

/-- Step 3, the basic inequality, as a deterministic implication on real numbers:
`Q_{K_n}(f̂) ≤ Q_n(f̂) + R ≤ Q_n(f*) + η + R ≤ Q_{K_n}(f*) + 2R + η ≤ ‖f* − f₀‖² + 2R + η`. -/
theorem step3 {QKhat Qnhat Qnstar QKstar R η d : ℝ}
    (h1 : QKhat ≤ Qnhat + R) (h2 : Qnhat ≤ Qnstar + η) (h3 : Qnstar ≤ QKstar + R)
    (h4 : QKstar ≤ d) : QKhat ≤ d + 2 * R + η := by
  linarith

/-- Step 4: for `n ≥ n₀(ε)`, `‖f̂ − f₀‖ ≥ ε` forces `Q_{K_n}(f̂) ≥ ω(ε)/4` (by (6.1) and `f̂ ∈ 𝓗`). -/
theorem step4 (T : H₀ →L[ℝ] H') {𝓗 : Set H₀} (h𝓗 : IsCompact 𝓗) {f₀ : H₀}
    (hid : ∀ f ∈ 𝓗, T (f - f₀) = 0 → f = f₀) {P : ℕ → H' →L[ℝ] H'}
    (hP : ∀ n (h : H'), ‖h - P n h‖ ≤ ‖h‖) (hconv : strongLimitId P) {ε : ℝ} (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ fhat ∈ 𝓗, ε ≤ ‖fhat - f₀‖ →
      omega T 𝓗 f₀ ε / 4 ≤ QK (P n) T f₀ fhat := by
  obtain ⟨n₀, hn₀⟩ := step1 T h𝓗 hid hP hconv hε
  exact ⟨n₀, fun n hn f hf hεf => (hn₀ n hn f hf hεf).2⟩

/-- Theorem 3(b), deterministic form. Inputs for each `n`: the near-minimizer `f̂_n ∈ 𝓗`, a comparison
function `f*_n` with `‖f*_n − f₀‖ → 0` (from (S3)), the near-minimization `Q_n(f̂_n) ≤ Q_n(f*_n) + η_n`,
and the uniform deviation `|Q_n − Q_{K_n}| ≤ R_n` at `f̂_n` and `f*_n` (Step 2). If `R_n → 0` and
`η_n → 0`, then `‖f̂_n − f₀‖ → 0`. -/
theorem thm3b_deterministic (T : H₀ →L[ℝ] H') (hT : ‖T‖ ≤ 1) {𝓗 : Set H₀} (h𝓗 : IsCompact 𝓗)
    {f₀ : H₀} (hid : ∀ f ∈ 𝓗, T (f - f₀) = 0 → f = f₀) {P : ℕ → H' →L[ℝ] H'}
    (hP : ∀ n (h : H'), ‖h - P n h‖ ≤ ‖h‖) (hP1 : ∀ n (h : H'), ‖P n h‖ ≤ ‖h‖)
    (hconv : strongLimitId P)
    (Qn : ℕ → H₀ → ℝ) (fhat fstar : ℕ → H₀) (R η : ℕ → ℝ)
    (hfhat : ∀ n, fhat n ∈ 𝓗)
    (hstar : Tendsto (fun n => ‖fstar n - f₀‖) atTop (𝓝 0))
    (hmin : ∀ n, Qn n (fhat n) ≤ Qn n (fstar n) + η n)
    (hRhat : ∀ n, |Qn n (fhat n) - QK (P n) T f₀ (fhat n)| ≤ R n)
    (hRstar : ∀ n, |Qn n (fstar n) - QK (P n) T f₀ (fstar n)| ≤ R n)
    (hR : Tendsto R atTop (𝓝 0)) (hη : Tendsto η atTop (𝓝 0)) :
    Tendsto (fun n => ‖fhat n - f₀‖) atTop (𝓝 0) := by
  -- Step 3: `Q_{K_n}(f̂_n) ≤ ‖f*_n − f₀‖² + 2 R_n + η_n → 0`
  have hbasic : ∀ n, QK (P n) T f₀ (fhat n) ≤ ‖fstar n - f₀‖ ^ 2 + 2 * R n + η n := by
    intro n
    have h1 := (abs_le.1 (hRhat n)).1
    have h3 := (abs_le.1 (hRstar n)).2
    exact step3 (by linarith) (hmin n) (by linarith) (QK_le_norm_sq (hP1 n) hT f₀ (fstar n))
  have hlim : Tendsto (fun n => ‖fstar n - f₀‖ ^ 2 + 2 * R n + η n) atTop (𝓝 0) := by
    have := ((hstar.pow 2).add (hR.const_mul 2)).add hη
    simpa using this
  -- Step 4
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨n₀, hn₀⟩ := step4 T h𝓗 hid hP hconv hε
  have hωpos_or : ∀ n ≥ n₀, ε ≤ ‖fhat n - f₀‖ → omega T 𝓗 f₀ ε / 4 ≤ QK (P n) T f₀ (fhat n) :=
    fun n hn h => hn₀ n hn (fhat n) (hfhat n) h
  by_cases hne : {f ∈ 𝓗 | ε ≤ ‖f - f₀‖}.Nonempty
  · have hω : 0 < omega T 𝓗 f₀ ε := omega_pos T h𝓗 hid hε hne
    obtain ⟨n₁, hn₁⟩ := Metric.tendsto_atTop.1 hlim (omega T 𝓗 f₀ ε / 4) (by positivity)
    refine ⟨max n₀ n₁, fun n hn => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
    by_contra hcon
    push Not at hcon
    have hA := hωpos_or n (le_of_max_le_left hn) hcon
    have hB := hn₁ n (le_of_max_le_right hn)
    rw [Real.dist_eq, sub_zero] at hB
    have hC := hbasic n
    have := (abs_lt.1 hB).2
    linarith
  · refine ⟨0, fun n _ => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
    by_contra hcon
    push Not at hcon
    exact hne ⟨fhat n, hfhat n, hcon⟩

/-- Theorem 3(b) in probability. The random inputs live on a measure space `Ω`: `f̂_n : Ω → 𝓗`, the
criterion `Q_n`, the near-minimization slack `η_n` and the uniform deviation bound `R_n` (Step 2's
output, a random variable with `R_n →_p 0`). The comparison sequence `f*_n` is deterministic (S3).
Conclusion: `‖f̂_n − f₀‖ →_p 0`, as `MeasureTheory.TendstoInMeasure`. -/
theorem thm3b_inProbability {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (T : H₀ →L[ℝ] H') (hT : ‖T‖ ≤ 1) {𝓗 : Set H₀} (h𝓗 : IsCompact 𝓗)
    {f₀ : H₀} (hid : ∀ f ∈ 𝓗, T (f - f₀) = 0 → f = f₀) {P : ℕ → H' →L[ℝ] H'}
    (hP : ∀ n (h : H'), ‖h - P n h‖ ≤ ‖h‖) (hP1 : ∀ n (h : H'), ‖P n h‖ ≤ ‖h‖)
    (hconv : strongLimitId P)
    (Qn : ℕ → Ω → H₀ → ℝ) (fhat : ℕ → Ω → H₀) (fstar : ℕ → H₀) (R η : ℕ → Ω → ℝ)
    (hfhat : ∀ n ω, fhat n ω ∈ 𝓗)
    (hstar : Tendsto (fun n => ‖fstar n - f₀‖) atTop (𝓝 0))
    (hmin : ∀ n ω, Qn n ω (fhat n ω) ≤ Qn n ω (fstar n) + η n ω)
    (hRhat : ∀ n ω, |Qn n ω (fhat n ω) - QK (P n) T f₀ (fhat n ω)| ≤ R n ω)
    (hRstar : ∀ n ω, |Qn n ω (fstar n) - QK (P n) T f₀ (fstar n)| ≤ R n ω)
    (hR : MeasureTheory.TendstoInMeasure μ R atTop (fun _ => (0 : ℝ)))
    (hη : MeasureTheory.TendstoInMeasure μ η atTop (fun _ => (0 : ℝ))) :
    MeasureTheory.TendstoInMeasure μ fhat atTop (fun _ => f₀) := by
  rw [MeasureTheory.tendstoInMeasure_iff_norm] at hR hη ⊢
  intro ε hε
  -- Step 3 pointwise in ω
  have hbasic : ∀ n ω, QK (P n) T f₀ (fhat n ω) ≤ ‖fstar n - f₀‖ ^ 2 + 2 * R n ω + η n ω := by
    intro n ω
    have h1 := (abs_le.1 (hRhat n ω)).1
    have h3 := (abs_le.1 (hRstar n ω)).2
    exact step3 (by linarith) (hmin n ω) (by linarith) (QK_le_norm_sq (hP1 n) hT f₀ (fstar n))
  by_cases hne : {f ∈ 𝓗 | ε ≤ ‖f - f₀‖}.Nonempty
  · set c := omega T 𝓗 f₀ ε / 8 with hc_def
    have hω : 0 < omega T 𝓗 f₀ ε := omega_pos T h𝓗 hid hε hne
    have hc : 0 < c := by positivity
    obtain ⟨n₀, hn₀⟩ := step4 T h𝓗 hid hP hconv hε
    obtain ⟨n₁, hn₁⟩ := Metric.tendsto_atTop.1 (hstar.pow 2) c hc
    -- Step 4: the bad event is contained in the union of two events of vanishing probability
    have hsub : ∀ n ≥ max n₀ n₁, {ω | ε ≤ ‖fhat n ω - f₀‖} ⊆
        {ω | c / 4 ≤ ‖R n ω - 0‖} ∪ {ω | c / 2 ≤ ‖η n ω - 0‖} := by
      intro n hn ω hω
      simp only [Set.mem_ofPred_eq] at hω
      have hA := hn₀ n (le_of_max_le_left hn) (fhat n ω) (hfhat n ω) hω
      have hB := hn₁ n (le_of_max_le_right hn)
      rw [Real.dist_eq, zero_pow (by norm_num), sub_zero] at hB
      have hB' := (abs_lt.1 hB).2
      have hC := hbasic n ω
      by_contra hcon
      simp only [Set.mem_union, Set.mem_ofPred_eq, sub_zero, Real.norm_eq_abs, not_or,
        not_le] at hcon
      have h1 : R n ω < c / 4 := lt_of_le_of_lt (le_abs_self _) hcon.1
      have h2 : η n ω < c / 2 := lt_of_le_of_lt (le_abs_self _) hcon.2
      linarith
    have hlim : Tendsto (fun n => μ {ω | c / 4 ≤ ‖R n ω - 0‖} + μ {ω | c / 2 ≤ ‖η n ω - 0‖})
        atTop (𝓝 0) := by
      simpa using (hR (c / 4) (by positivity)).add (hη (c / 2) (by positivity))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun n => zero_le) ?_
    filter_upwards [eventually_ge_atTop (max n₀ n₁)] with n hn
    exact (MeasureTheory.measure_mono (hsub n hn)).trans (MeasureTheory.measure_union_le _ _)
  · have hempty : ∀ n, {ω | ε ≤ ‖fhat n ω - f₀‖} = ∅ := by
      intro n
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h => hne ⟨fhat n ω, hfhat n ω, h⟩
    simp only [hempty, MeasureTheory.measure_empty]
    exact tendsto_const_nhds

/-! ### Stretch: `Δ_n(t) → 0` under (S6) -/

/-- The bracket inside `Δ_n(t)` (THEORY.md §6, Step 2 of the proof of Theorem 3(b)). -/
def Bn (t m C M : ℝ) (L Λ : ℕ → ℝ) (n : ℕ) : ℝ :=
  t + L n * Real.log (3 * m) + Real.log 2 +
    L n * Real.log (1 + 2 * C * Λ n * Real.sqrt n / M)

/-- `Δ_n(t)` of Step 2: `(M/√n)[√K_n + 2ζ_n + ζ_n √(8 B_n)]`. -/
def Delta (t m C M : ℝ) (K ζ L Λ : ℕ → ℝ) (n : ℕ) : ℝ :=
  M / Real.sqrt n * (Real.sqrt (K n) + 2 * ζ n + ζ n * Real.sqrt (8 * Bn t m C M L Λ n))

/-- The bracket is nonnegative. -/
theorem Bn_nonneg {t m C M : ℝ} {L Λ : ℕ → ℝ} (ht : 0 ≤ t) (hm : 1 ≤ m) (hC : 0 ≤ C)
    (hM : 0 < M) (hL : ∀ n, 1 ≤ L n) (hΛ1 : ∀ n, 1 ≤ Λ n) (n : ℕ) : 0 ≤ Bn t m C M L Λ n := by
  unfold Bn
  have h1 : 0 ≤ Real.log (3 * m) := Real.log_nonneg (by linarith)
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h3 : 0 ≤ Real.log (1 + 2 * C * Λ n * Real.sqrt n / M) := by
    apply Real.log_nonneg
    have : 0 ≤ 2 * C * Λ n * Real.sqrt n / M := by
      have := hΛ1 n
      positivity
    linarith
  have := hL n
  positivity

/-- The bracket is `O(L_n (L_n + log n))` for `n ≥ 1`, with constant
`c := t + log(3m) + log 2 + log(1 + 2C/M) + a + 1`. -/
theorem Bn_le {t m C M a : ℝ} {L Λ : ℕ → ℝ} (ht : 0 ≤ t) (hm : 1 ≤ m) (hC : 0 ≤ C)
    (hM : 0 < M) (hL : ∀ n, 1 ≤ L n) (hΛ1 : ∀ n, 1 ≤ Λ n)
    (hΛ : ∀ n, Real.log (Λ n) ≤ a * (L n + Real.log n)) {n : ℕ} (hn : 1 ≤ n) :
    Bn t m C M L Λ n ≤
      (t + Real.log (3 * m) + Real.log 2 + Real.log (1 + 2 * C / M) + a + 1) *
        (L n * (L n + Real.log n)) := by
  unfold Bn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hℓ : 0 ≤ Real.log n := Real.log_nonneg hn'
  have hsqrt1 : 1 ≤ Real.sqrt n := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hn'
  have hΛn := hΛ1 n
  have hLn := hL n
  have hq1 : 0 ≤ Real.log (3 * m) := Real.log_nonneg (by linarith)
  have hq2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hq3 : 0 ≤ Real.log (1 + 2 * C / M) := Real.log_nonneg (by
    have : 0 ≤ 2 * C / M := by positivity
    linarith)
  -- `log(1 + 2CΛ√n/M) ≤ log(1 + 2C/M) + log Λ + log n / 2`
  have hlog : Real.log (1 + 2 * C * Λ n * Real.sqrt n / M) ≤
      Real.log (1 + 2 * C / M) + Real.log (Λ n) + Real.log n / 2 := by
    have hx : 0 < 1 + 2 * C * Λ n * Real.sqrt n / M := by
      have : 0 ≤ 2 * C * Λ n * Real.sqrt n / M := by positivity
      linarith
    have hprod : 1 + 2 * C * Λ n * Real.sqrt n / M ≤ (1 + 2 * C / M) * (Λ n * Real.sqrt n) := by
      have hΛs : 1 ≤ Λ n * Real.sqrt n := one_le_mul_of_one_le_of_one_le hΛn hsqrt1
      have hCM : 0 ≤ 2 * C / M := by positivity
      have e : 2 * C * Λ n * Real.sqrt n / M = 2 * C / M * (Λ n * Real.sqrt n) := by
        field_simp
      rw [e]
      nlinarith
    calc Real.log (1 + 2 * C * Λ n * Real.sqrt n / M)
        ≤ Real.log ((1 + 2 * C / M) * (Λ n * Real.sqrt n)) := Real.log_le_log hx hprod
      _ = Real.log (1 + 2 * C / M) + (Real.log (Λ n) + Real.log (Real.sqrt n)) := by
          rw [Real.log_mul (by positivity) (by positivity),
            Real.log_mul (by positivity) (by positivity)]
      _ = Real.log (1 + 2 * C / M) + Real.log (Λ n) + Real.log n / 2 := by
          rw [Real.log_sqrt (by positivity)]; ring
  have hlog' : Real.log (1 + 2 * C * Λ n * Real.sqrt n / M) ≤
      Real.log (1 + 2 * C / M) + a * (L n + Real.log n) + Real.log n := by
    have := hΛ n
    linarith
  have hLlog : L n * Real.log (1 + 2 * C * Λ n * Real.sqrt n / M) ≤
      L n * (Real.log (1 + 2 * C / M) + a * (L n + Real.log n) + Real.log n) :=
    mul_le_mul_of_nonneg_left hlog' (by linarith)
  set X := L n * (L n + Real.log n) with hX
  have hX1 : 1 ≤ X := by rw [hX]; nlinarith
  have hLle : L n ≤ X := by rw [hX]; nlinarith
  have e1 : t ≤ t * X := le_mul_of_one_le_right ht hX1
  have e2 : L n * Real.log (3 * m) ≤ Real.log (3 * m) * X := by nlinarith
  have e3 : Real.log 2 ≤ Real.log 2 * X := le_mul_of_one_le_right hq2 hX1
  have e4 : L n * Real.log (1 + 2 * C / M) ≤ Real.log (1 + 2 * C / M) * X := by nlinarith
  have e5 : L n * (a * (L n + Real.log n)) = a * X := by rw [hX]; ring
  have e6 : L n * Real.log n ≤ 1 * X := by rw [hX]; nlinarith
  nlinarith

/-- The stretch goal: `Δ_n(t) → 0` for fixed `t` under (S6) (`ζ_n² L_n (L_n + log n)/n → 0`),
`log Λ_n ≤ a (L_n + log n)`, `K_n ≤ ζ_n²` and `L_n ≥ 1`. -/
theorem Delta_tendsto_zero {t m C M a : ℝ} {K ζ L Λ : ℕ → ℝ} (ht : 0 ≤ t) (hm : 1 ≤ m)
    (hC : 0 ≤ C) (hM : 0 < M) (ha : 0 ≤ a) (hL : ∀ n, 1 ≤ L n) (hΛ1 : ∀ n, 1 ≤ Λ n)
    (hΛ : ∀ n, Real.log (Λ n) ≤ a * (L n + Real.log n)) (hζ : ∀ n, 0 ≤ ζ n)
    (hK0 : ∀ n, 0 ≤ K n) (hK : ∀ n, K n ≤ ζ n ^ 2)
    (hgrowth : Tendsto (fun n : ℕ => ζ n ^ 2 * L n * (L n + Real.log n) / n) atTop (𝓝 0)) :
    Tendsto (Delta t m C M K ζ L Λ) atTop (𝓝 0) := by
  set c := t + Real.log (3 * m) + Real.log 2 + Real.log (1 + 2 * C / M) + a + 1 with hc_def
  have hc : 0 ≤ c := by
    have hq1 : 0 ≤ Real.log (3 * m) := Real.log_nonneg (by linarith)
    have hq2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hq3 : 0 ≤ Real.log (1 + 2 * C / M) := Real.log_nonneg (by
      have : 0 ≤ 2 * C / M := by positivity
      linarith)
    rw [hc_def]; linarith
  set κ := 3 * M ^ 2 * (5 + 8 * c) with hκ_def
  have hκ : 0 ≤ κ := by rw [hκ_def]; positivity
  -- the dominating sequence `√(κ A_n) → 0`
  have hdom : Tendsto (fun n : ℕ => Real.sqrt (κ * (ζ n ^ 2 * L n * (L n + Real.log n) / n)))
      atTop (𝓝 0) := by
    have := (hgrowth.const_mul κ).sqrt
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hdom
    (Eventually.of_forall fun n => ?_) ?_
  · unfold Delta
    have := hζ n
    positivity
  filter_upwards [eventually_ge_atTop 1] with n hn
  -- bound `Δ_n² ≤ κ A_n`, then take square roots
  have hB0 := Bn_nonneg ht hm hC hM hL hΛ1 n
  have hBle := Bn_le ht hm hC hM hL hΛ1 hΛ hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hℓ : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hLn := hL n
  have hζn := hζ n
  set X := L n * (L n + Real.log n) with hX
  have hX1 : 1 ≤ X := by rw [hX]; nlinarith
  set S := Real.sqrt (K n) + 2 * ζ n + ζ n * Real.sqrt (8 * Bn t m C M L Λ n) with hS
  have hS0 : 0 ≤ S := by rw [hS]; positivity
  have hsqK : Real.sqrt (K n) ^ 2 = K n := Real.sq_sqrt (hK0 n)
  have hsqB : Real.sqrt (8 * Bn t m C M L Λ n) ^ 2 = 8 * Bn t m C M L Λ n :=
    Real.sq_sqrt (by linarith)
  -- `S² ≤ 3 (K + 4ζ² + 8 ζ² B)`
  have hS2 : S ^ 2 ≤ 3 * (K n + 4 * ζ n ^ 2 + ζ n ^ 2 * (8 * Bn t m C M L Λ n)) := by
    rw [hS]
    nlinarith [sq_nonneg (Real.sqrt (K n) - 2 * ζ n),
      sq_nonneg (Real.sqrt (K n) - ζ n * Real.sqrt (8 * Bn t m C M L Λ n)),
      sq_nonneg (2 * ζ n - ζ n * Real.sqrt (8 * Bn t m C M L Λ n))]
  have hinner : K n + 4 * ζ n ^ 2 + ζ n ^ 2 * (8 * Bn t m C M L Λ n) ≤ ζ n ^ 2 * (5 + 8 * c) * X := by
    have h1 : ζ n ^ 2 * (8 * Bn t m C M L Λ n) ≤ ζ n ^ 2 * (8 * (c * X)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h2 : ζ n ^ 2 * 5 ≤ ζ n ^ 2 * 5 * X := by nlinarith [sq_nonneg (ζ n)]
    have h3 : 0 ≤ c * ζ n ^ 2 * X := by positivity
    nlinarith [hK n]
  have hΔ : Delta t m C M K ζ L Λ n = M / Real.sqrt n * S := rfl
  have hΔsq : Delta t m C M K ζ L Λ n ^ 2 ≤ κ * (ζ n ^ 2 * L n * (L n + Real.log n) / n) := by
    rw [hΔ, mul_pow, div_pow, Real.sq_sqrt hn'.le, hκ_def]
    have hX' : ζ n ^ 2 * L n * (L n + Real.log n) = ζ n ^ 2 * X := by rw [hX]; ring
    rw [hX']
    have hM2 : 0 ≤ M ^ 2 / n := by positivity
    calc M ^ 2 / n * S ^ 2
        ≤ M ^ 2 / n * (3 * (ζ n ^ 2 * (5 + 8 * c) * X)) :=
          mul_le_mul_of_nonneg_left (hS2.trans (by linarith)) hM2
      _ = 3 * M ^ 2 * (5 + 8 * c) * (ζ n ^ 2 * X / n) := by ring
  calc Delta t m C M K ζ L Λ n = Real.sqrt (Delta t m C M K ζ L Λ n ^ 2) := by
        rw [Real.sqrt_sq]
        rw [hΔ]; positivity
    _ ≤ Real.sqrt (κ * (ζ n ^ 2 * L n * (L n + Real.log n) / n)) := Real.sqrt_le_sqrt hΔsq

end SymbolicIV.Thm3b

#print axioms SymbolicIV.Thm3b.step1
#print axioms SymbolicIV.Thm3b.step1_starProjection
#print axioms SymbolicIV.Thm3b.norm_sq_perturb_bound
#print axioms SymbolicIV.Thm3b.step3
#print axioms SymbolicIV.Thm3b.step4
#print axioms SymbolicIV.Thm3b.thm3b_deterministic
#print axioms SymbolicIV.Thm3b.thm3b_inProbability
#print axioms SymbolicIV.Thm3b.Delta_tendsto_zero
