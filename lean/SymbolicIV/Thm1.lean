import Mathlib

/-!
# Theorem 1 (THEORY.md §3): deterministic core and consistency

This file formalizes the proof of Theorem 1 of THEORY.md (consistency and selection of the
penalized criterion `crit_n(s) = n Q̂_s / σ̂² + pen_n(s)`, `pen_n(s) = p_s κ_n + w ℓ_s log m`).

**Layer 1 (deterministic, one fixed sample).**
* `crit_true_le` is display (3.1): `crit(s*) ≤ n Q_n(f₀)/σ̂² + pen(s*)` for a true candidate `s*`.
* `Qhat_shat_le` is steps 1–2 of (i): `Q̂_ŝ ≤ Q_n(f₀) + σ̂² pen(s*)/n`.
* `Q_fhat_le` is step 3 of (i): `Q(f̂) ≤ Q_n(f₀) + σ̂² pen(s*)/n + R` when `|Q̂_ŝ − Q(f̂)| ≤ R`.
* `shat_mem_Smin` is the deterministic core of (ii): if a minimal true tree is a candidate, every
  wrong candidate satisfies `n(δ_s^Q − R)/σ̂² > n Q_n(f₀)/σ̂² + pen(s*)`, and every
  over-parameterized true candidate satisfies `(p_s − p₀)κ + w(ℓ_s − ℓ_{s*}) log m > n Q_n(f₀)/σ̂²`,
  then `ŝ ∈ S₀^min`.
* `over_cond_of_simple` is the paper's sufficient form `κ − w L log m > n Q_n(f₀)/σ̂²` of the
  over-parameterized condition.

**Layer 2 (probabilistic, the stretch goal of the plan).**
* `tendsto_shat_mem_Smin` is Theorem 1(ii): `P(ŝ_n ∉ S₀^min) → 0`.
* `tendsto_dist_fhat` is Theorem 1(i): `P(‖f̂_n − f₀‖ ≥ ε) → 0`.

## Modelling choices and hypotheses added beyond the paper

* Trees form a finite type `S`; `S₀` (true trees) is a set, `p₀ : ℕ`, and `S₀^min` is characterised
  by `s ∈ Smin ↔ s ∈ S₀ ∧ p s = p₀` together with `p₀ ≤ p s` for `s ∈ S₀` (THEORY.md §0, "Minimal true trees").
  The alphabet size `m` satisfies `1 ≤ m`, so `log m ≥ 0`; `κ ≥ 0`, `w ≥ 0`.
* Sample quantities are real numbers (layer 1) or real functions of `ω` (layer 2): `Q̂_s`, `Q_n(f₀)`,
  `σ̂²`, the uniform deviation `R_n`, `Q(f̂)`, `‖f̂ − f₀‖`. No measurability is assumed anywhere:
  probabilities are outer measures `μ.real`, and only monotonicity and finite subadditivity are used.
  Consequently "P(coverage) → 1" is stated as "P(coverage fails) → 0" (equivalent for measurable
  events), and the conclusions are stated as probabilities of failure tending to 0.
* The facts the paper takes from (C1)–(C3) and Lemma 1 enter as hypotheses:
  - `Q̂_s ≤ Q_n(f₀)` for every true tree `s` (the true tree reproduces `f₀`);
  - `Q̂_s ≥ δ_s^Q − R_n` for every wrong tree `s`, with `δ_s^Q > 0` (from (C1) and compactness);
  - `|Q̂_ŝ − Q(f̂)| ≤ R_n` (the uniform law (C2) at the selected function);
  - `η(ε) > 0` with `‖f̂ − f₀‖ ≥ ε → Q(f̂) ≥ η(ε)` (Lemma 1(a) and (C1));
  - `R_n →_p 0`, `n Q_n(f₀) = O_p(1)` (from (C3)), `σ̂² →_p σ*² > 0`, `κ_n → ∞`, `κ_n/n → 0`.
* `Q̂_s ≥ 0` and `Q_n(f₀) ≥ 0` (criteria are squared norms).
* The argmin: `crit(ŝ) ≤ crit(s)` for all `s ∈ Ŝ`, and (for (ii) only) `ŝ ∈ Ŝ` whenever `Ŝ ≠ ∅`.
* In layer 1, `σ̂² > 0` and `n > 0` are hypotheses; in layer 2 they hold on the good event.
-/

open Filter Topology MeasureTheory

namespace SymbolicIV.Thm1

/-- Penalty `pen s = p_s κ + w ℓ_s log m`. -/
noncomputable def pen {S : Type*} (p ℓ : S → ℕ) (κ w : ℝ) (m : ℕ) (s : S) : ℝ :=
  (p s : ℝ) * κ + w * (ℓ s : ℝ) * Real.log m

/-- Criterion `crit s = n Q̂_s / σ̂² + pen s`. -/
noncomputable def crit {S : Type*} (p ℓ : S → ℕ) (κ w : ℝ) (m : ℕ) (n : ℕ) (Qhat : S → ℝ)
    (σ2 : ℝ) (s : S) : ℝ :=
  (n : ℝ) * Qhat s / σ2 + pen p ℓ κ w m s

section Deterministic

variable {S : Type*} {p ℓ : S → ℕ} {κ w : ℝ} {m : ℕ} {n : ℕ} {Qhat : S → ℝ} {σ2 Qn0 : ℝ}
  {Shat : Set S} {shat sstar : S}

theorem pen_nonneg (hκ : 0 ≤ κ) (hw : 0 ≤ w) (hm : 1 ≤ m) (s : S) : 0 ≤ pen p ℓ κ w m s := by
  have hlog : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm)
  unfold pen
  positivity

/-- The penalty of a tree with `p₀` constants and at most `L` nodes is at most
`p₀ κ + w L log m`. -/
theorem pen_le (hw : 0 ≤ w) (hm : 1 ≤ m) {L : ℕ} (hL : ℓ sstar ≤ L) {p0 : ℕ} (hp : p sstar = p0) :
    pen p ℓ κ w m sstar ≤ (p0 : ℝ) * κ + w * L * Real.log m := by
  have hlog : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm)
  unfold pen
  rw [hp]
  have : (ℓ sstar : ℝ) ≤ L := by exact_mod_cast hL
  have := mul_le_mul_of_nonneg_left this hw
  have := mul_le_mul_of_nonneg_right this hlog
  linarith

/-- Display (3.1): for a candidate true tree `s*` (one with `Q̂_{s*} ≤ Q_n(f₀)`),
`crit(s*) ≤ n Q_n(f₀)/σ̂² + pen(s*)`. -/
theorem crit_true_le (hσ : 0 < σ2) (hQ : Qhat sstar ≤ Qn0) :
    crit p ℓ κ w m n Qhat σ2 sstar ≤ (n : ℝ) * Qn0 / σ2 + pen p ℓ κ w m sstar := by
  unfold crit
  have : (n : ℝ) * Qhat sstar / σ2 ≤ (n : ℝ) * Qn0 / σ2 := by gcongr
  linarith

/-- Steps 1–2 of (i): the selected criterion is at most the true one, and penalties are
nonnegative, so `Q̂_ŝ ≤ Q_n(f₀) + σ̂² pen(s*)/n`. -/
theorem Qhat_shat_le (hκ : 0 ≤ κ) (hw : 0 ≤ w) (hm : 1 ≤ m) (hn : 0 < n) (hσ : 0 < σ2)
    (hmin : ∀ s ∈ Shat, crit p ℓ κ w m n Qhat σ2 shat ≤ crit p ℓ κ w m n Qhat σ2 s)
    (hs : sstar ∈ Shat) (hQ : Qhat sstar ≤ Qn0) :
    Qhat shat ≤ Qn0 + σ2 * pen p ℓ κ w m sstar / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : (n : ℝ) * Qhat shat / σ2 ≤ (n : ℝ) * Qn0 / σ2 + pen p ℓ κ w m sstar := by
    have := (hmin sstar hs).trans (crit_true_le hσ hQ)
    unfold crit at this
    linarith [pen_nonneg (p := p) (ℓ := ℓ) hκ hw hm shat]
  have h2 : (n : ℝ) * Qhat shat ≤ (n : ℝ) * Qn0 + σ2 * pen p ℓ κ w m sstar := by
    have := (div_le_iff₀ hσ).mp h1
    rw [add_mul, div_mul_cancel₀ _ hσ.ne'] at this
    linarith
  rw [show Qn0 + σ2 * pen p ℓ κ w m sstar / n = ((n : ℝ) * Qn0 + σ2 * pen p ℓ κ w m sstar) / n by
    field_simp]
  rw [le_div_iff₀ hn']
  linarith

/-- Step 3 of (i): with the uniform deviation `|Q̂_ŝ − Q(f̂)| ≤ R`,
`Q(f̂) ≤ Q_n(f₀) + σ̂² pen(s*)/n + R`. -/
theorem Q_fhat_le (hκ : 0 ≤ κ) (hw : 0 ≤ w) (hm : 1 ≤ m) (hn : 0 < n) (hσ : 0 < σ2)
    (hmin : ∀ s ∈ Shat, crit p ℓ κ w m n Qhat σ2 shat ≤ crit p ℓ κ w m n Qhat σ2 s)
    (hs : sstar ∈ Shat) (hQ : Qhat sstar ≤ Qn0) {Qf R : ℝ} (hR : |Qhat shat - Qf| ≤ R) :
    Qf ≤ Qn0 + σ2 * pen p ℓ κ w m sstar / n + R := by
  have := Qhat_shat_le hκ hw hm hn hσ hmin hs hQ
  have := (abs_sub_le_iff.mp hR).2
  linarith

/-- The paper's sufficient form of the over-parameterized condition: if `p_s > p₀`, `ℓ_{s*} ≤ L`
and `κ − w L log m > n Q_n(f₀)/σ̂²`, then `(p_s − p₀)κ + w(ℓ_s − ℓ_{s*}) log m > n Q_n(f₀)/σ̂²`. -/
theorem over_cond_of_simple (hκ : 0 ≤ κ) (hw : 0 ≤ w) (hm : 1 ≤ m) {L p0 : ℕ} (hL : ℓ sstar ≤ L)
    {s : S} (hps : p0 < p s) {x : ℝ} (h : x < κ - w * L * Real.log m) :
    x < ((p s : ℝ) - p0) * κ + w * ((ℓ s : ℝ) - ℓ sstar) * Real.log m := by
  have hlog : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm)
  have h1 : (1 : ℝ) ≤ (p s : ℝ) - p0 := by
    have : p0 + 1 ≤ p s := hps
    have : ((p0 : ℝ) + 1) ≤ (p s : ℝ) := by exact_mod_cast this
    linarith
  have h2 : κ ≤ ((p s : ℝ) - p0) * κ := by nlinarith
  have h3 : 0 ≤ (ℓ s : ℝ) - ℓ sstar + L := by
    have : (ℓ sstar : ℝ) ≤ L := by exact_mod_cast hL
    have : (0 : ℝ) ≤ ℓ s := by positivity
    linarith
  have h4 : 0 ≤ w * Real.log m * ((ℓ s : ℝ) - ℓ sstar + L) := by positivity
  nlinarith

/-- The deterministic core of (ii). If a minimal true tree `s*` is a candidate, every wrong
candidate `s` has `Q̂_s ≥ δ_s^Q − R` with `n(δ_s^Q − R)/σ̂² > n Q_n(f₀)/σ̂² + pen(s*)`, and every
over-parameterized true candidate has `(p_s − p₀)κ + w(ℓ_s − ℓ_{s*}) log m > n Q_n(f₀)/σ̂²`,
then the selected tree is a minimal true tree. -/
theorem shat_mem_Smin {S0 Smin : Set S} {p0 : ℕ}
    (hSmin : ∀ s, s ∈ Smin ↔ s ∈ S0 ∧ p s = p0) (hp0 : ∀ s ∈ S0, p0 ≤ p s)
    (hκ : 0 ≤ κ) (hw : 0 ≤ w) (hm : 1 ≤ m) (hσ : 0 < σ2) (hQhat : ∀ s, 0 ≤ Qhat s)
    (hmem : shat ∈ Shat)
    (hmin : ∀ s ∈ Shat, crit p ℓ κ w m n Qhat σ2 shat ≤ crit p ℓ κ w m n Qhat σ2 s)
    (hs : sstar ∈ Shat) (hsmin : sstar ∈ Smin) (hQ : Qhat sstar ≤ Qn0)
    {δQ : S → ℝ} {R : ℝ}
    (hwrong : ∀ s ∈ Shat, s ∉ S0 →
      δQ s - R ≤ Qhat s ∧ (n : ℝ) * Qn0 / σ2 + pen p ℓ κ w m sstar < (n : ℝ) * (δQ s - R) / σ2)
    (hover : ∀ s ∈ Shat, s ∈ S0 → p0 < p s →
      (n : ℝ) * Qn0 / σ2 < ((p s : ℝ) - p0) * κ + w * ((ℓ s : ℝ) - ℓ sstar) * Real.log m) :
    shat ∈ Smin := by
  have hcrit : crit p ℓ κ w m n Qhat σ2 shat ≤ (n : ℝ) * Qn0 / σ2 + pen p ℓ κ w m sstar :=
    (hmin sstar hs).trans (crit_true_le hσ hQ)
  have hpen : 0 ≤ pen p ℓ κ w m shat := pen_nonneg hκ hw hm shat
  by_cases h0 : shat ∈ S0
  · -- a true tree: either minimal, or over-parameterized and then it loses on the penalty
    rcases (hp0 shat h0).lt_or_eq with hlt | heq
    · exfalso
      have hpos : 0 ≤ (n : ℝ) * Qhat shat / σ2 := by
        have := hQhat shat
        positivity
      have hdiff : pen p ℓ κ w m shat - pen p ℓ κ w m sstar
          = ((p shat : ℝ) - p0) * κ + w * ((ℓ shat : ℝ) - ℓ sstar) * Real.log m := by
        have hp : p sstar = p0 := ((hSmin sstar).mp hsmin).2
        unfold pen
        rw [hp]
        ring
      have := hover shat hmem h0 hlt
      unfold crit at hcrit
      linarith
    · exact (hSmin shat).mpr ⟨h0, heq.symm⟩
  · -- a wrong tree: its criterion grows linearly in n
    exfalso
    obtain ⟨h1, h2⟩ := hwrong shat hmem h0
    have h3 : (n : ℝ) * (δQ shat - R) / σ2 ≤ (n : ℝ) * Qhat shat / σ2 := by gcongr
    unfold crit at hcrit
    linarith

end Deterministic

section Probabilistic

/-! ### Layer 2: the asymptotic statement -/

/-- A finite family of positive numbers has a positive lower bound. -/
theorem exists_pos_lower_bound {S : Type*} [Finite S] (P : S → Prop) (f : S → ℝ)
    (h : ∀ s, P s → 0 < f s) : ∃ δ > 0, ∀ s, P s → δ ≤ f s := by
  classical
  cases isEmpty_or_nonempty S with
  | inl hS => exact ⟨1, one_pos, fun s _ => (IsEmpty.false s).elim⟩
  | inr hS =>
    let g : S → ℝ := fun s => if P s then f s else 1
    obtain ⟨s0, hs0⟩ := Finite.exists_min g
    refine ⟨g s0, ?_, fun s hs => ?_⟩
    · simp only [g]
      split_ifs with hP
      · exact h s0 hP
      · exact one_pos
    · have := hs0 s
      simp only [g, hs, ↓reduceIte] at this
      exact this

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- `X_n →_p c`: convergence in probability of real random variables (no measurability needed;
the probability is the outer measure `μ.real`). -/
def TendstoInProb (X : ℕ → Ω → ℝ) (c : ℝ) : Prop :=
  ∀ ε > 0, Tendsto (fun n => μ.real {ω | ε ≤ |X n ω - c|}) atTop (𝓝 0)

/-- `X_n = O_p(1)`: for every `η > 0` there is `M` with `P(|X_n| > M) ≤ η` for all large `n`. -/
def BoundedInProb (X : ℕ → Ω → ℝ) : Prop :=
  ∀ η > 0, ∃ M : ℝ, ∀ᶠ n in atTop, μ.real {ω | M < |X n ω|} ≤ η

variable {μ}

omit [IsProbabilityMeasure μ] in
theorem tendsto_zero_of_forall_eventually_lt {B : ℕ → Set Ω}
    (h : ∀ ε > 0, ∀ᶠ n in atTop, μ.real (B n) < ε) :
    Tendsto (fun n => μ.real (B n)) atTop (𝓝 0) :=
  tendsto_order.2 ⟨fun _ ha => Eventually.of_forall fun _ => ha.trans_le measureReal_nonneg,
    fun b hb => h b hb⟩

omit [IsProbabilityMeasure μ] in
theorem measureReal_union4_le (A B C D : Set Ω) :
    μ.real (A ∪ B ∪ C ∪ D) ≤ μ.real A + μ.real B + μ.real C + μ.real D :=
  calc μ.real (A ∪ B ∪ C ∪ D) ≤ μ.real (A ∪ B ∪ C) + μ.real D := measureReal_union_le _ _
    _ ≤ μ.real (A ∪ B) + μ.real C + μ.real D := by
      gcongr; exact measureReal_union_le _ _
    _ ≤ μ.real A + μ.real B + μ.real C + μ.real D := by
      gcongr; exact measureReal_union_le _ _

/-- The deterministic thresholds `(M + 2σ*(P κ_n + c))/n → 0` when `κ_n/n → 0`. -/
theorem tendsto_threshold (M σstar c : ℝ) (P : ℕ) {κ : ℕ → ℝ}
    (hκn : Tendsto (fun n => κ n / n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (M + 2 * σstar * (P * κ n + c)) / (n : ℝ)) atTop (𝓝 0) := by
  have h2 := (tendsto_const_nhds (x := M + 2 * σstar * c)).mul
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  have h3 := (tendsto_const_nhds (x := 2 * σstar * P)).mul hκn
  have := h2.add h3
  simp only [mul_zero, add_zero] at this
  refine this.congr (fun n => ?_)
  ring

/-- **Theorem 1(ii)**: with `κ_n → ∞`, `κ_n/n → 0`, `R_n →_p 0`, `n Q_n(f₀) = O_p(1)`,
`σ̂² →_p σ*² > 0` and coverage by a minimal true tree with probability tending to one, the
selected tree is a minimal true tree with probability tending to one. -/
theorem tendsto_shat_mem_Smin {S : Type*} [Fintype S]
    {S0 Smin : Set S} {p ℓ : S → ℕ} {p0 L m : ℕ} {w : ℝ} {κ : ℕ → ℝ}
    (hSmin : ∀ s, s ∈ Smin ↔ s ∈ S0 ∧ p s = p0) (hp0 : ∀ s ∈ S0, p0 ≤ p s)
    (hκ : ∀ n, 0 ≤ κ n) (hw : 0 ≤ w) (hm : 1 ≤ m) (hL : ∀ s, ℓ s ≤ L)
    (hκ_inf : Tendsto κ atTop atTop) (hκn : Tendsto (fun n => κ n / n) atTop (𝓝 0))
    {Shat : ℕ → Ω → Set S} {shat : ℕ → Ω → S} {Qhat : ℕ → S → Ω → ℝ} {Qn0 σ2 R : ℕ → Ω → ℝ}
    {δQ : S → ℝ} {σstar : ℝ} (hσstar : 0 < σstar)
    (hQhat : ∀ n s ω, 0 ≤ Qhat n s ω) (hQn0 : ∀ n ω, 0 ≤ Qn0 n ω)
    (hmem : ∀ n ω, (Shat n ω).Nonempty → shat n ω ∈ Shat n ω)
    (hmin : ∀ n ω, ∀ s ∈ Shat n ω,
      crit p ℓ (κ n) w m n (fun s => Qhat n s ω) (σ2 n ω) (shat n ω)
        ≤ crit p ℓ (κ n) w m n (fun s => Qhat n s ω) (σ2 n ω) s)
    (htrue : ∀ n ω, ∀ s ∈ S0, Qhat n s ω ≤ Qn0 n ω)
    (hδ : ∀ s, s ∉ S0 → 0 < δQ s)
    (hwrong : ∀ n ω s, s ∉ S0 → δQ s - R n ω ≤ Qhat n s ω)
    (hR : TendstoInProb μ R 0)
    (hOp : BoundedInProb μ (fun n ω => n * Qn0 n ω))
    (hσ : TendstoInProb μ σ2 σstar)
    (hcov : Tendsto (fun n => μ.real {ω | ¬ ∃ s ∈ Shat n ω, s ∈ Smin}) atTop (𝓝 0)) :
    Tendsto (fun n => μ.real {ω | shat n ω ∉ Smin}) atTop (𝓝 0) := by
  have hlog : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm)
  obtain ⟨δ, hδpos, hδle⟩ := exists_pos_lower_bound (fun s => s ∉ S0) δQ hδ
  apply tendsto_zero_of_forall_eventually_lt
  intro ε hε
  have hηpos : 0 < ε / 5 := by positivity
  obtain ⟨M, hM⟩ := hOp (ε / 5) hηpos
  -- the deterministic thresholds
  have hN1 : ∀ᶠ n in atTop, w * L * Real.log m + 2 * M / σstar < κ n :=
    hκ_inf.eventually (eventually_gt_atTop _)
  have hN2 : ∀ᶠ n in atTop,
      (M + 2 * σstar * (p0 * κ n + w * L * Real.log m)) / (n : ℝ) < δ / 2 :=
    (tendsto_threshold M σstar _ p0 hκn).eventually (gt_mem_nhds (by positivity))
  have hA1 := (tendsto_order.1 hcov).2 _ hηpos
  have hA2 := (tendsto_order.1 (hσ (σstar / 2) (by positivity))).2 _ hηpos
  have hA3 := (tendsto_order.1 (hR (δ / 4) (by positivity))).2 _ hηpos
  filter_upwards [hN1, hN2, hA1, hA2, hA3, hM, eventually_gt_atTop 0] with n hn1 hn2 ha1 ha2 ha3
    ha4 hnpos
  have hnpos' : (0 : ℝ) < n := by exact_mod_cast hnpos
  -- union bound: on the complement of the four bad events, the deterministic core applies
  have hsub : {ω | shat n ω ∉ Smin} ⊆
      {ω | ¬ ∃ s ∈ Shat n ω, s ∈ Smin} ∪ {ω | σstar / 2 ≤ |σ2 n ω - σstar|}
        ∪ {ω | δ / 4 ≤ |R n ω - 0|} ∪ {ω | M < |(n : ℝ) * Qn0 n ω|} := by
    intro ω hω
    by_contra hcon
    have h1 : ∃ s ∈ Shat n ω, s ∈ Smin := by
      by_contra h; exact hcon (Or.inl (Or.inl (Or.inl h)))
    have h2 : |σ2 n ω - σstar| < σstar / 2 := by
      by_contra h; exact hcon (Or.inl (Or.inl (Or.inr (not_lt.mp h))))
    have h3 : |R n ω - 0| < δ / 4 := by
      by_contra h; exact hcon (Or.inl (Or.inr (not_lt.mp h)))
    have h4 : |(n : ℝ) * Qn0 n ω| ≤ M := by
      by_contra h; exact hcon (Or.inr (not_le.mp h))
    obtain ⟨sstar, hs, hsmin⟩ := h1
    have hσlo : σstar / 2 < σ2 n ω := by linarith [(abs_sub_lt_iff.mp h2).2]
    have hσhi : σ2 n ω ≤ 2 * σstar := by linarith [(abs_sub_lt_iff.mp h2).1]
    have hσpos : 0 < σ2 n ω := by linarith
    have hRlt : R n ω < δ / 4 := by rw [sub_zero] at h3; exact (abs_lt.mp h3).2
    have hQM : (n : ℝ) * Qn0 n ω ≤ M := (le_abs_self _).trans h4
    have hMnn : 0 ≤ M := (abs_nonneg _).trans h4
    have hQn0n : Qn0 n ω ≤ M / n := by
      rw [le_div_iff₀ hnpos']; linarith
    apply hω
    refine shat_mem_Smin hSmin hp0 (hκ n) hw hm hσpos (fun s => hQhat n s ω)
      (hmem n ω ⟨sstar, hs⟩) (hmin n ω) hs hsmin (htrue n ω sstar ((hSmin sstar).mp hsmin).1)
      (δQ := δQ) (R := R n ω) ?_ ?_
    · -- wrong candidates
      intro s _ hsS0
      refine ⟨hwrong n ω s hsS0, ?_⟩
      set pb : ℝ := (p0 : ℝ) * κ n + w * L * Real.log m with hpb
      have hpbnn : 0 ≤ pb := by rw [hpb]; have := hκ n; positivity
      have hpen : pen p ℓ (κ n) w m sstar ≤ pb :=
        pen_le hw hm (hL sstar) ((hSmin sstar).mp hsmin).2
      have hkey : Qn0 n ω + σ2 n ω * pb / n < δQ s - R n ω := by
        have e1 : σ2 n ω * pb / n ≤ 2 * σstar * pb / n := by gcongr
        have e2 : M / n + 2 * σstar * pb / n = (M + 2 * σstar * pb) / n := by ring
        have e3 := hδle s hsS0
        linarith
      calc (n : ℝ) * Qn0 n ω / σ2 n ω + pen p ℓ (κ n) w m sstar
          ≤ (n : ℝ) * Qn0 n ω / σ2 n ω + pb := by linarith
        _ = (n : ℝ) * (Qn0 n ω + σ2 n ω * pb / n) / σ2 n ω := by
          field_simp
        _ < (n : ℝ) * (δQ s - R n ω) / σ2 n ω := by gcongr
    · -- over-parameterized true candidates
      intro s _ _ hps
      apply over_cond_of_simple (hκ n) hw hm (hL sstar) hps
      have e1 : (n : ℝ) * Qn0 n ω / σ2 n ω ≤ (n : ℝ) * Qn0 n ω / (σstar / 2) :=
        div_le_div_of_nonneg_left (by have := hQn0 n ω; positivity) (by positivity) hσlo.le
      have e2 : (n : ℝ) * Qn0 n ω / (σstar / 2) ≤ M / (σstar / 2) := by gcongr
      have e3 : M / (σstar / 2) = 2 * M / σstar := by field_simp
      linarith
  calc μ.real {ω | shat n ω ∉ Smin}
      ≤ μ.real ({ω | ¬ ∃ s ∈ Shat n ω, s ∈ Smin} ∪ {ω | σstar / 2 ≤ |σ2 n ω - σstar|}
        ∪ {ω | δ / 4 ≤ |R n ω - 0|} ∪ {ω | M < |(n : ℝ) * Qn0 n ω|}) := measureReal_mono hsub
    _ ≤ μ.real {ω | ¬ ∃ s ∈ Shat n ω, s ∈ Smin} + μ.real {ω | σstar / 2 ≤ |σ2 n ω - σstar|}
        + μ.real {ω | δ / 4 ≤ |R n ω - 0|} + μ.real {ω | M < |(n : ℝ) * Qn0 n ω|} :=
      measureReal_union4_le _ _ _ _
    _ < ε := by linarith

/-- **Theorem 1(i)**: with `κ_n/n → 0`, `R_n →_p 0`, `n Q_n(f₀) = O_p(1)`, `σ̂² →_p σ*² > 0`,
coverage by a true tree with probability tending to one, the uniform deviation
`|Q̂_ŝ − Q(f̂)| ≤ R_n`, and the identification gap `‖f̂ − f₀‖ ≥ ε → Q(f̂) ≥ η > 0`
(Lemma 1(a) with (C1)), `P(‖f̂_n − f₀‖ ≥ ε) → 0`. Here `Qf n ω = Q(f̂_n)` and
`D n ω = ‖f̂_n − f₀‖`. -/
theorem tendsto_dist_fhat {S : Type*} [Fintype S]
    {S0 : Set S} {p ℓ : S → ℕ} {L m : ℕ} {w : ℝ} {κ : ℕ → ℝ}
    (hκ : ∀ n, 0 ≤ κ n) (hw : 0 ≤ w) (hm : 1 ≤ m) (hL : ∀ s, ℓ s ≤ L)
    (hκn : Tendsto (fun n => κ n / n) atTop (𝓝 0))
    {Shat : ℕ → Ω → Set S} {shat : ℕ → Ω → S} {Qhat : ℕ → S → Ω → ℝ}
    {Qn0 σ2 R Qf D : ℕ → Ω → ℝ} {σstar : ℝ} (hσstar : 0 < σstar)
    (hmin : ∀ n ω, ∀ s ∈ Shat n ω,
      crit p ℓ (κ n) w m n (fun s => Qhat n s ω) (σ2 n ω) (shat n ω)
        ≤ crit p ℓ (κ n) w m n (fun s => Qhat n s ω) (σ2 n ω) s)
    (htrue : ∀ n ω, ∀ s ∈ S0, Qhat n s ω ≤ Qn0 n ω)
    (hRf : ∀ n ω, |Qhat n (shat n ω) ω - Qf n ω| ≤ R n ω)
    {ε η : ℝ} (hηpos : 0 < η) (hη : ∀ n ω, ε ≤ D n ω → η ≤ Qf n ω)
    (hR : TendstoInProb μ R 0)
    (hOp : BoundedInProb μ (fun n ω => n * Qn0 n ω))
    (hσ : TendstoInProb μ σ2 σstar)
    (hcov : Tendsto (fun n => μ.real {ω | ¬ ∃ s ∈ Shat n ω, s ∈ S0}) atTop (𝓝 0)) :
    Tendsto (fun n => μ.real {ω | ε ≤ D n ω}) atTop (𝓝 0) := by
  classical
  have hlog : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm)
  set P : ℕ := Finset.univ.sup p with hP
  have hpP : ∀ s, p s ≤ P := fun s => Finset.le_sup (f := p) (Finset.mem_univ s)
  apply tendsto_zero_of_forall_eventually_lt
  intro ε' hε'
  have hη'pos : 0 < ε' / 5 := by positivity
  obtain ⟨M, hM⟩ := hOp (ε' / 5) hη'pos
  have hN2 : ∀ᶠ n in atTop,
      (M + 2 * σstar * (P * κ n + w * L * Real.log m)) / (n : ℝ) < η / 2 :=
    (tendsto_threshold M σstar _ P hκn).eventually (gt_mem_nhds (by positivity))
  have hA1 := (tendsto_order.1 hcov).2 _ hη'pos
  have hA2 := (tendsto_order.1 (hσ (σstar / 2) (by positivity))).2 _ hη'pos
  have hA3 := (tendsto_order.1 (hR (η / 4) (by positivity))).2 _ hη'pos
  filter_upwards [hN2, hA1, hA2, hA3, hM, eventually_gt_atTop 0] with n hn2 ha1 ha2 ha3
    ha4 hnpos
  have hnpos' : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hsub : {ω | ε ≤ D n ω} ⊆
      {ω | ¬ ∃ s ∈ Shat n ω, s ∈ S0} ∪ {ω | σstar / 2 ≤ |σ2 n ω - σstar|}
        ∪ {ω | η / 4 ≤ |R n ω - 0|} ∪ {ω | M < |(n : ℝ) * Qn0 n ω|} := by
    intro ω hω
    by_contra hcon
    have h1 : ∃ s ∈ Shat n ω, s ∈ S0 := by
      by_contra h; exact hcon (Or.inl (Or.inl (Or.inl h)))
    have h2 : |σ2 n ω - σstar| < σstar / 2 := by
      by_contra h; exact hcon (Or.inl (Or.inl (Or.inr (not_lt.mp h))))
    have h3 : |R n ω - 0| < η / 4 := by
      by_contra h; exact hcon (Or.inl (Or.inr (not_lt.mp h)))
    have h4 : |(n : ℝ) * Qn0 n ω| ≤ M := by
      by_contra h; exact hcon (Or.inr (not_le.mp h))
    obtain ⟨sstar, hs, hsS0⟩ := h1
    have hσhi : σ2 n ω ≤ 2 * σstar := by linarith [(abs_sub_lt_iff.mp h2).1]
    have hσpos : 0 < σ2 n ω := by linarith [(abs_sub_lt_iff.mp h2).2]
    have hRlt : R n ω < η / 4 := by rw [sub_zero] at h3; exact (abs_lt.mp h3).2
    have hQM : (n : ℝ) * Qn0 n ω ≤ M := (le_abs_self _).trans h4
    have hQn0n : Qn0 n ω ≤ M / n := by
      rw [le_div_iff₀ hnpos']; linarith
    have hQf := Q_fhat_le (hκ n) hw hm hnpos hσpos (hmin n ω) hs (htrue n ω sstar hsS0)
      (hRf n ω)
    set pb : ℝ := (P : ℝ) * κ n + w * L * Real.log m with hpb
    have hpbnn : 0 ≤ pb := by rw [hpb]; have := hκ n; positivity
    have hpen : pen p ℓ (κ n) w m sstar ≤ pb := by
      have h1 := pen_le (κ := κ n) (p0 := p sstar) hw hm (hL sstar) rfl
      have h2 : (p sstar : ℝ) ≤ P := by exact_mod_cast hpP sstar
      have h3 : (p sstar : ℝ) * κ n ≤ P * κ n := mul_le_mul_of_nonneg_right h2 (hκ n)
      linarith
    have e1 : σ2 n ω * pen p ℓ (κ n) w m sstar / n ≤ 2 * σstar * pb / n := by
      have := pen_nonneg (p := p) (ℓ := ℓ) (hκ n) hw hm sstar
      gcongr
    have e2 : M / n + 2 * σstar * pb / n = (M + 2 * σstar * pb) / n := by ring
    have := hη n ω hω
    linarith
  calc μ.real {ω | ε ≤ D n ω}
      ≤ μ.real ({ω | ¬ ∃ s ∈ Shat n ω, s ∈ S0} ∪ {ω | σstar / 2 ≤ |σ2 n ω - σstar|}
        ∪ {ω | η / 4 ≤ |R n ω - 0|} ∪ {ω | M < |(n : ℝ) * Qn0 n ω|}) := measureReal_mono hsub
    _ ≤ μ.real {ω | ¬ ∃ s ∈ Shat n ω, s ∈ S0} + μ.real {ω | σstar / 2 ≤ |σ2 n ω - σstar|}
        + μ.real {ω | η / 4 ≤ |R n ω - 0|} + μ.real {ω | M < |(n : ℝ) * Qn0 n ω|} :=
      measureReal_union4_le _ _ _ _
    _ < ε' := by linarith

end Probabilistic

end SymbolicIV.Thm1

#print axioms SymbolicIV.Thm1.Qhat_shat_le
#print axioms SymbolicIV.Thm1.Q_fhat_le
#print axioms SymbolicIV.Thm1.shat_mem_Smin
#print axioms SymbolicIV.Thm1.over_cond_of_simple
#print axioms SymbolicIV.Thm1.tendsto_shat_mem_Smin
#print axioms SymbolicIV.Thm1.tendsto_dist_fhat
