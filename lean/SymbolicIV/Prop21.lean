import Mathlib

/-!
# Proposition 2.1: the deterministic core of Theorem 2

Formalizes Proposition 2.1 of THEORY.md (§4, Proposition 2.1 and its proof; paper: theory.tex / appendix-proofs.tex,
"Proof of Proposition 2.1"), unit U01 of `FORMALIZATION_PLAN.md`.

## Abstract setting

* `E` is a real inner product space (the instrument space, `ℝ^K` in the paper).
* `Z : E` is the moment noise at the truth (`√n ū/σ`; the paper writes `U`).
* `Θ` is a topological space of parameters of one tree `s`; `G E_ : Θ → E` are the scaled population
  moment `G θ = √n g(s,θ)/σ` and the empirical-process term `E_s(θ)`.
* `z, d, dloc, π : ℝ` with `‖Z‖ ≤ z`, `∀ θ, ‖E_ θ‖ ≤ d`, `∀ θ ∈ Θloc, ‖E_ θ‖ ≤ dloc`;
  `π = pen(s) − pen̄₀` is the penalty gap.
* `locSet G r = {θ | ‖G θ‖ ≤ r}` (the paper's `Θ_s(r)`), `dirs G r` (the paper's `𝒟_s(r)`),
  `W Z G r = sSup ((fun v ↦ max ⟪-Z, v⟫ 0) '' dirs G r)` (the paper's `W_s`; Mathlib's `sSup ∅ = 0`
  on `ℝ` gives the paper's convention `W_s = 0` when `𝒟_s(r)` is empty).

## Results

* `condI`   : (I) separation, pointwise in θ: `‖Z + G θ + E_ θ‖² > ‖Z‖² − π`.
* `condII`  : (II) complexity, pointwise in θ, following the paper's proof (outside / inside `Θ_s(r)`).
* `W_nonneg`, `W_le_norm` : `0 ≤ W_s ≤ ‖Z‖`.
* `W_le_norm_starProjection` : the projection bound `W_s ≤ ‖P_V Z‖` for a subspace `V ⊇ 𝒟_s(r)` with an
  orthogonal projection (any finite-dimensional subspace qualifies).
* `iInf_gt_of_forall_gt` : a strict inequality at every θ passes to the minimum (compactness and
  continuity; the "Reduction" paragraph of the proof).
* `crit_gt_of_J_gt` : the criterion comparison `J(s) + pen(s) > J(s*) + pen(s*)` from
  `J(s*) ≤ ‖Z‖²`, `pen(s*) ≤ pen̄₀` and `J(s) > ‖Z‖² − π`.
* `prop21_I`, `prop21_II` : Proposition 2.1 assembled, in criterion form, with
  `J(s) = ⨅ θ, ‖Z + G θ + E_ θ‖²`.

## Hypotheses beyond the paper's statement

* `0 ≤ dloc`. Since the fourth pass (2026-10-15) the paper states it ("any bound `d_s^loc ≥ 0` with
  `d_s^loc ≥ sup_{θ ∈ Θ_s(r)} ‖E_s(θ)‖`"), so it is no longer beyond the paper. The supremum alone
  implies it only when `Θ_s(r)` is nonempty; when `Θ_s(r)` is empty the sign is what makes the
  paper's remark "Here π_s > 0" true. It is used only there.
* In `prop21_I`/`prop21_II`: `Θ` compact and nonempty, `G`, `E_` continuous (the paper's "the
  minimum is attained, as θ ↦ ‖Z + G(θ) + E(θ)‖² is continuous on the compact Θ_s"). The pointwise
  statements `condI`, `condII` need none of these.
* The projection bound takes `V` with `[V.HasOrthogonalProjection]`, which every finite-dimensional
  subspace satisfies; the paper's `V_s = span 𝒟_s(r)` is one such `V`.

No hypothesis of the paper is dropped: `z ≥ 0` and `d ≥ 0` are not needed (`z ≥ 0` follows from
`‖Z‖ ≤ z`; `d` is used only through `‖E_ θ‖ ≤ d`).
-/

open scoped RealInnerProductSpace

noncomputable section

namespace SymbolicIV.Prop21

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {Θ : Type*}

/-! ### Definitions -/

/-- The localized parameter set `Θ_s(r) = {θ : ‖G θ‖ ≤ r}`. -/
def locSet (G : Θ → E) (r : ℝ) : Set Θ := {θ | ‖G θ‖ ≤ r}

/-- The directions `𝒟_s(r) = {G θ / ‖G θ‖ : θ ∈ Θ_s(r), G θ ≠ 0}`. -/
def dirs (G : Θ → E) (r : ℝ) : Set E :=
  {v | ∃ θ ∈ locSet G r, G θ ≠ 0 ∧ v = ‖G θ‖⁻¹ • G θ}

/-- `W_s = sup_{v ∈ 𝒟_s(r)} ⟪-Z, v⟫₊`, with `W_s = 0` when `𝒟_s(r)` is empty (`Real.sSup_empty`). -/
def W (Z : E) (G : Θ → E) (r : ℝ) : ℝ :=
  sSup ((fun v => max ⟪-Z, v⟫ 0) '' dirs G r)

/-- The (scaled) J statistic `J_n(s) = min_θ ‖Z + G θ + E θ‖²`, as an infimum. -/
def Jn (Z : E) (G E_ : Θ → E) : ℝ := ⨅ θ, ‖Z + G θ + E_ θ‖ ^ 2

/-! ### Elementary norm inequalities -/

omit [InnerProductSpace ℝ E] in
/-- Reverse triangle inequality in the form used twice in the proof:
`‖Z + G + E‖ ≥ ‖G‖ − ‖Z‖ − ‖E‖`. -/
theorem norm_sub_sub_le_norm_add_add (x y w : E) : ‖y‖ - ‖x‖ - ‖w‖ ≤ ‖x + y + w‖ := by
  have h1 : ‖y‖ ≤ ‖x + y + w‖ + ‖x‖ + ‖w‖ := by
    calc ‖y‖ = ‖(x + y + w) - x - w‖ := by congr 1; abel
      _ ≤ ‖(x + y + w) - x‖ + ‖w‖ := norm_sub_le _ _
      _ ≤ ‖x + y + w‖ + ‖x‖ + ‖w‖ := by gcongr; exact norm_sub_le _ _
  linarith

omit [InnerProductSpace ℝ E] in
/-- `‖x + w‖ ≥ ‖x‖ − ‖w‖`. -/
theorem norm_sub_le_norm_add (x w : E) : ‖x‖ - ‖w‖ ≤ ‖x + w‖ := by
  have h1 : ‖x‖ ≤ ‖x + w‖ + ‖w‖ := by
    calc ‖x‖ = ‖(x + w) - w‖ := by congr 1; abel
      _ ≤ ‖x + w‖ + ‖w‖ := norm_sub_le _ _
  linarith

/-- For a unit vector `v`, `⟪-Z, v⟫₊ ≤ ‖Z‖`. -/
theorem posPart_inner_le_norm (Z v : E) (hv : ‖v‖ = 1) : max ⟪-Z, v⟫ 0 ≤ ‖Z‖ := by
  have h := real_inner_le_norm (-Z) v
  rw [norm_neg, hv, mul_one] at h
  exact max_le h (norm_nonneg Z)

/-- "Minimizing over the length `‖G‖ ≥ 0`": for a unit vector `v` and `t ≥ 0`,
`‖Z + t v‖² = ‖Z‖² + 2 t ⟪Z, v⟫ + t² ≥ ‖Z‖² − ⟪-Z, v⟫₊²`. -/
theorem sq_norm_add_smul_ge (Z v : E) (hv : ‖v‖ = 1) {t : ℝ} (ht : 0 ≤ t) :
    ‖Z‖ ^ 2 - (max ⟪-Z, v⟫ 0) ^ 2 ≤ ‖Z + t • v‖ ^ 2 := by
  rw [norm_add_sq_real, norm_smul, hv, mul_one, Real.norm_eq_abs, abs_of_nonneg ht,
    real_inner_smul_right, inner_neg_left]
  rcases le_or_gt 0 ⟪Z, v⟫ with hc | hc
  · rw [max_eq_right (by linarith)]
    nlinarith [mul_nonneg ht hc]
  · rw [max_eq_left (by linarith)]
    nlinarith [sq_nonneg (t + ⟪Z, v⟫)]

/-- `(a − Δ)₊² ≥ a² − 2aΔ` for `a, Δ ≥ 0`. -/
theorem sq_sub_two_mul_le_posPart_sq {a Δ : ℝ} (ha : 0 ≤ a) (hΔ : 0 ≤ Δ) :
    a ^ 2 - 2 * a * Δ ≤ (max (a - Δ) 0) ^ 2 := by
  rcases le_or_gt Δ a with h | h
  · rw [max_eq_left (by linarith)]
    nlinarith [sq_nonneg Δ]
  · rw [max_eq_right (by linarith)]
    nlinarith

/-! ### The directions and `W_s` -/

theorem norm_eq_one_of_mem_dirs {G : Θ → E} {r : ℝ} {v : E} (hv : v ∈ dirs G r) : ‖v‖ = 1 := by
  obtain ⟨θ, -, hG, rfl⟩ := hv
  exact norm_smul_inv_norm hG

theorem bddAbove_posPart_image (Z : E) (G : Θ → E) (r : ℝ) :
    BddAbove ((fun v => max ⟪-Z, v⟫ 0) '' dirs G r) := by
  refine ⟨‖Z‖, ?_⟩
  rintro _ ⟨v, hv, rfl⟩
  exact posPart_inner_le_norm Z v (norm_eq_one_of_mem_dirs hv)

/-- Every direction contributes at most `W_s`. -/
theorem le_W (Z : E) (G : Θ → E) (r : ℝ) {v : E} (hv : v ∈ dirs G r) :
    max ⟪-Z, v⟫ 0 ≤ W Z G r :=
  le_csSup (bddAbove_posPart_image Z G r) ⟨v, hv, rfl⟩

theorem W_nonneg (Z : E) (G : Θ → E) (r : ℝ) : 0 ≤ W Z G r := by
  by_cases h : (dirs G r).Nonempty
  · obtain ⟨v, hv⟩ := h
    exact le_trans (le_max_right _ _) (le_W Z G r hv)
  · rw [Set.not_nonempty_iff_eq_empty] at h
    simp [W, h, Real.sSup_empty]

/-- `W_s ≤ ‖Z‖` (the plan's "W is bounded by ‖Z‖"). -/
theorem W_le_norm (Z : E) (G : Θ → E) (r : ℝ) : W Z G r ≤ ‖Z‖ := by
  by_cases h : (dirs G r).Nonempty
  · apply csSup_le (h.image _)
    rintro _ ⟨v, hv, rfl⟩
    exact posPart_inner_le_norm Z v (norm_eq_one_of_mem_dirs hv)
  · rw [Set.not_nonempty_iff_eq_empty] at h
    simp [W, h, Real.sSup_empty]

/-- **The projection bound** `W_s ≤ ‖P_V Z‖` for any subspace `V ⊇ 𝒟_s(r)` admitting an orthogonal
projection (in particular `V_s = span 𝒟_s(r)`, which is finite-dimensional when `E` is). -/
theorem W_le_norm_starProjection (Z : E) (G : Θ → E) (r : ℝ) (V : Submodule ℝ E)
    [V.HasOrthogonalProjection] (hD : dirs G r ⊆ V) :
    W Z G r ≤ ‖V.starProjection Z‖ := by
  by_cases h : (dirs G r).Nonempty
  · apply csSup_le (h.image _)
    rintro _ ⟨v, hv, rfl⟩
    have hv1 : ‖v‖ = 1 := norm_eq_one_of_mem_dirs hv
    have h0 : ⟪Z - V.starProjection Z, v⟫ = 0 := V.starProjection_inner_eq_zero Z v (hD hv)
    rw [inner_sub_left] at h0
    have h1 : ⟪-Z, v⟫ = ⟪-(V.starProjection Z), v⟫ := by
      rw [inner_neg_left, inner_neg_left]; linarith
    have h2 := real_inner_le_norm (-(V.starProjection Z)) v
    rw [norm_neg, hv1, mul_one] at h2
    exact max_le (h1 ▸ h2) (norm_nonneg _)
  · rw [Set.not_nonempty_iff_eq_empty] at h
    simp [W, h, Real.sSup_empty]

/-- Inside the localized set, `‖Z + G θ‖² ≥ ‖Z‖² − W_s²` (also when `G θ = 0`). -/
theorem sq_norm_add_ge_of_mem_locSet (Z : E) (G : Θ → E) (r : ℝ) {θ : Θ}
    (hθ : θ ∈ locSet G r) : ‖Z‖ ^ 2 - (W Z G r) ^ 2 ≤ ‖Z + G θ‖ ^ 2 := by
  by_cases hG : G θ = 0
  · rw [hG, add_zero]
    nlinarith [sq_nonneg (W Z G r)]
  · set v : E := ‖G θ‖⁻¹ • G θ with hv
    have hv1 : ‖v‖ = 1 := norm_smul_inv_norm hG
    have hvD : v ∈ dirs G r := ⟨θ, hθ, hG, rfl⟩
    have hGv : G θ = ‖G θ‖ • v := by
      rw [hv, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hG), one_smul]
    have h1 := sq_norm_add_smul_ge Z v hv1 (norm_nonneg (G θ))
    rw [← hGv] at h1
    have h2 : max ⟪-Z, v⟫ 0 ≤ W Z G r := le_W Z G r hvD
    have h3 : 0 ≤ max ⟪-Z, v⟫ 0 := le_max_right _ _
    have h4 : (max ⟪-Z, v⟫ 0) ^ 2 ≤ (W Z G r) ^ 2 := pow_le_pow_left₀ h3 h2 2
    linarith

/-! ### Condition (I): separation -/

omit [InnerProductSpace ℝ E] in
/-- **Proposition 2.1 (I), pointwise.** If `‖G θ‖ ≥ a > 2z + d + √((−π)₊)` for every `θ`, then
`‖Z + G θ + E θ‖² > ‖Z‖² − π` for every `θ`. In the paper `a = √(n δ_s)/σ`. (Only the norm is
used: this part holds in any normed space.) -/
theorem condI (Z : E) (G E_ : Θ → E) {z d a π : ℝ} (hz : ‖Z‖ ≤ z) (hd : ∀ θ, ‖E_ θ‖ ≤ d)
    (ha : 2 * z + d + Real.sqrt (max (-π) 0) < a) (hG : ∀ θ, a ≤ ‖G θ‖) (θ : Θ) :
    ‖Z‖ ^ 2 - π < ‖Z + G θ + E_ θ‖ ^ 2 := by
  set s := Real.sqrt (max (-π) 0) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = max (-π) 0 := Real.sq_sqrt (le_max_right _ _)
  have hz0 : 0 ≤ z := le_trans (norm_nonneg Z) hz
  have hlow : a - z - d ≤ ‖Z + G θ + E_ θ‖ := by
    have := norm_sub_sub_le_norm_add_add Z (G θ) (E_ θ)
    linarith [hG θ, hd θ]
  have hpos : z + s < ‖Z + G θ + E_ θ‖ := by linarith
  have hzs : 0 ≤ z + s := by linarith
  have hsq : (z + s) ^ 2 < ‖Z + G θ + E_ θ‖ ^ 2 := by
    have := mul_pos (sub_pos.mpr hpos) (by linarith : 0 < ‖Z + G θ + E_ θ‖ + (z + s))
    nlinarith
  have hmax : -π ≤ max (-π) 0 := le_max_left _ _
  have hZ2 : ‖Z‖ ^ 2 ≤ z ^ 2 := pow_le_pow_left₀ (norm_nonneg Z) hz 2
  nlinarith [mul_nonneg hz0 hs0]

/-! ### Condition (II): complexity -/

/-- **Proposition 2.1 (II), pointwise.** With `r = 2z + d`, `Θloc = locSet G r`, `W = W Z G r` and
`dloc ≥ 0` bounding `‖E_ θ‖` on `Θloc`: if `π > W² + 2 z dloc` then
`‖Z + G θ + E θ‖² > ‖Z‖² − π` for every `θ`. -/
theorem condII (Z : E) (G E_ : Θ → E) {z d dloc π : ℝ} (hz : ‖Z‖ ≤ z) (hd : ∀ θ, ‖E_ θ‖ ≤ d)
    (hdloc0 : 0 ≤ dloc) (hdloc : ∀ θ ∈ locSet G (2 * z + d), ‖E_ θ‖ ≤ dloc)
    (hπ : (W Z G (2 * z + d)) ^ 2 + 2 * z * dloc < π) (θ : Θ) :
    ‖Z‖ ^ 2 - π < ‖Z + G θ + E_ θ‖ ^ 2 := by
  set r := 2 * z + d with hr
  have hz0 : 0 ≤ z := le_trans (norm_nonneg Z) hz
  have hπ0 : 0 < π := by nlinarith [sq_nonneg (W Z G r), mul_nonneg hz0 hdloc0]
  by_cases hθ : θ ∈ locSet G r
  · -- inside the localized set
    have hW := W_nonneg Z G r
    have hinner := sq_norm_add_ge_of_mem_locSet Z G r hθ
    set b := ‖Z‖ ^ 2 - (W Z G r) ^ 2 with hb
    set a := Real.sqrt (max b 0) with ha
    have ha0 : 0 ≤ a := Real.sqrt_nonneg _
    have ha2 : a ^ 2 = max b 0 := Real.sq_sqrt (le_max_right _ _)
    have haZ : a ≤ ‖Z‖ := by
      rw [ha, Real.sqrt_le_left (norm_nonneg Z)]
      exact max_le (by nlinarith [sq_nonneg (W Z G r)]) (sq_nonneg _)
    have haz : a ≤ z := haZ.trans hz
    have hZG : a ≤ ‖Z + G θ‖ := by
      rw [ha, Real.sqrt_le_left (norm_nonneg _)]
      exact max_le hinner (sq_nonneg _)
    have hΔ0 : 0 ≤ ‖E_ θ‖ := norm_nonneg _
    have hΔ : ‖E_ θ‖ ≤ dloc := hdloc θ hθ
    have h1 : a - ‖E_ θ‖ ≤ ‖Z + G θ + E_ θ‖ := by
      have := norm_sub_le_norm_add (Z + G θ) (E_ θ)
      linarith
    have h2 : max (a - ‖E_ θ‖) 0 ≤ ‖Z + G θ + E_ θ‖ := max_le h1 (norm_nonneg _)
    have h3 : (max (a - ‖E_ θ‖) 0) ^ 2 ≤ ‖Z + G θ + E_ θ‖ ^ 2 :=
      pow_le_pow_left₀ (le_max_right _ _) h2 2
    have h4 := sq_sub_two_mul_le_posPart_sq ha0 hΔ0
    have h5 : a * ‖E_ θ‖ ≤ z * dloc := mul_le_mul haz hΔ hΔ0 hz0
    have h6 : b ≤ max b 0 := le_max_left _ _
    nlinarith
  · -- outside the localized set
    simp only [locSet, Set.mem_ofPred_eq, not_le] at hθ
    have hlow := norm_sub_sub_le_norm_add_add Z (G θ) (E_ θ)
    have hgt : ‖Z‖ < ‖Z + G θ + E_ θ‖ := by linarith [hd θ]
    have hsq : ‖Z‖ ^ 2 < ‖Z + G θ + E_ θ‖ ^ 2 := by
      have := mul_pos (sub_pos.mpr hgt) (by linarith [norm_nonneg Z] : 0 < ‖Z + G θ + E_ θ‖ + ‖Z‖)
      nlinarith
    linarith

/-! ### The reduction to criteria -/

variable [TopologicalSpace Θ]

/-- A strict inequality at every `θ` passes to the minimum over a nonempty compact `Θ` of a
continuous function (the minimum is attained). -/
theorem iInf_gt_of_forall_gt [CompactSpace Θ] [Nonempty Θ] {φ : Θ → ℝ} (hφ : Continuous φ)
    {c : ℝ} (h : ∀ θ, c < φ θ) : c < ⨅ θ, φ θ := by
  obtain ⟨θ₀, -, hmin⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hφ.continuousOn
  have hle : φ θ₀ ≤ ⨅ θ, φ θ := le_ciInf fun θ => (isMinOn_iff.mp hmin) θ (Set.mem_univ θ)
  exact lt_of_lt_of_le (h θ₀) hle

/-- The criterion of `s*` is at most `‖Z‖² + pen̄₀`, so `J(s) > ‖Z‖² − (pen(s) − pen̄₀)` gives
`crit(s) > crit(s*)`. -/
theorem crit_gt_of_J_gt {J pen Jstar penstar penbar Z2 : ℝ} (hJstar : Jstar ≤ Z2)
    (hpen : penstar ≤ penbar) (hJ : Z2 - (pen - penbar) < J) : Jstar + penstar < J + pen := by
  linarith

omit [InnerProductSpace ℝ E] in
theorem continuous_sqNorm (Z : E) {G E_ : Θ → E} (hG : Continuous G) (hE : Continuous E_) :
    Continuous fun θ => ‖Z + G θ + E_ θ‖ ^ 2 :=
  ((continuous_const.add hG).add hE).norm.pow 2

omit [InnerProductSpace ℝ E] in
/-- `J_n(s) > ‖Z‖² − π` from the pointwise inequality, by compactness. -/
theorem Jn_gt_of_forall_gt [CompactSpace Θ] [Nonempty Θ] (Z : E) {G E_ : Θ → E}
    (hG : Continuous G) (hE : Continuous E_) {π : ℝ}
    (h : ∀ θ, ‖Z‖ ^ 2 - π < ‖Z + G θ + E_ θ‖ ^ 2) : ‖Z‖ ^ 2 - π < Jn Z G E_ :=
  iInf_gt_of_forall_gt (continuous_sqNorm Z hG hE) h

/-! ### Proposition 2.1 assembled -/

omit [InnerProductSpace ℝ E] in
/-- **Proposition 2.1 under (I), criterion form.** For a tree `s` with `J(s) = Jn Z G E_` and penalty
`pen`, and a minimal true tree `s*` with `J(s*) = Jstar ≤ ‖Z‖²` and `pen(s*) = penstar ≤ penbar`:
if `√(n δ_s)/σ = a > 2z + d + √((−(pen − penbar))₊)`, then `crit(s) > crit(s*)`. -/
theorem prop21_I [CompactSpace Θ] [Nonempty Θ] (Z : E) {G E_ : Θ → E}
    (hG : Continuous G) (hE : Continuous E_) {z d a pen penbar Jstar penstar : ℝ}
    (hz : ‖Z‖ ≤ z) (hd : ∀ θ, ‖E_ θ‖ ≤ d)
    (ha : 2 * z + d + Real.sqrt (max (-(pen - penbar)) 0) < a) (hsep : ∀ θ, a ≤ ‖G θ‖)
    (hJstar : Jstar ≤ ‖Z‖ ^ 2) (hpen : penstar ≤ penbar) :
    Jstar + penstar < Jn Z G E_ + pen :=
  crit_gt_of_J_gt hJstar hpen (Jn_gt_of_forall_gt Z hG hE (condI Z G E_ hz hd ha hsep))

/-- **Proposition 2.1 under (II), criterion form.** With `r = 2z + d`, `W = W Z G r`, and `dloc ≥ 0`
bounding `‖E_ θ‖` on `locSet G r`: if `pen − penbar > W² + 2 z dloc`, then `crit(s) > crit(s*)`. -/
theorem prop21_II [CompactSpace Θ] [Nonempty Θ] (Z : E) {G E_ : Θ → E}
    (hG : Continuous G) (hE : Continuous E_) {z d dloc pen penbar Jstar penstar : ℝ}
    (hz : ‖Z‖ ≤ z) (hd : ∀ θ, ‖E_ θ‖ ≤ d)
    (hdloc0 : 0 ≤ dloc) (hdloc : ∀ θ ∈ locSet G (2 * z + d), ‖E_ θ‖ ≤ dloc)
    (hπ : (W Z G (2 * z + d)) ^ 2 + 2 * z * dloc < pen - penbar)
    (hJstar : Jstar ≤ ‖Z‖ ^ 2) (hpen : penstar ≤ penbar) :
    Jstar + penstar < Jn Z G E_ + pen :=
  crit_gt_of_J_gt hJstar hpen
    (Jn_gt_of_forall_gt Z hG hE (condII Z G E_ hz hd hdloc0 hdloc hπ))

/-- **Proposition 2.1 under (II), with the projection bound substituted**: `W_s ≤ ‖P_V Z‖` for a
subspace `V ⊇ 𝒟_s(r)`, so `pen − penbar > ‖P_V Z‖² + 2 z dloc` suffices. This is the form in which
Theorem 2 uses the proposition. -/
theorem prop21_II_proj [CompactSpace Θ] [Nonempty Θ] (Z : E) {G E_ : Θ → E}
    (hG : Continuous G) (hE : Continuous E_) {z d dloc pen penbar Jstar penstar : ℝ}
    (hz : ‖Z‖ ≤ z) (hd : ∀ θ, ‖E_ θ‖ ≤ d)
    (hdloc0 : 0 ≤ dloc) (hdloc : ∀ θ ∈ locSet G (2 * z + d), ‖E_ θ‖ ≤ dloc)
    (V : Submodule ℝ E) [V.HasOrthogonalProjection] (hD : dirs G (2 * z + d) ⊆ V)
    (hπ : ‖V.starProjection Z‖ ^ 2 + 2 * z * dloc < pen - penbar)
    (hJstar : Jstar ≤ ‖Z‖ ^ 2) (hpen : penstar ≤ penbar) :
    Jstar + penstar < Jn Z G E_ + pen := by
  have hW := W_le_norm_starProjection Z G (2 * z + d) V hD
  have hW0 := W_nonneg Z G (2 * z + d)
  have hW2 : (W Z G (2 * z + d)) ^ 2 ≤ ‖V.starProjection Z‖ ^ 2 := pow_le_pow_left₀ hW0 hW 2
  exact prop21_II Z hG hE hz hd hdloc0 hdloc (by linarith) hJstar hpen

end SymbolicIV.Prop21

end

#print axioms SymbolicIV.Prop21.condI
#print axioms SymbolicIV.Prop21.condII
#print axioms SymbolicIV.Prop21.W_le_norm
#print axioms SymbolicIV.Prop21.W_le_norm_starProjection
#print axioms SymbolicIV.Prop21.iInf_gt_of_forall_gt
#print axioms SymbolicIV.Prop21.crit_gt_of_J_gt
#print axioms SymbolicIV.Prop21.prop21_I
#print axioms SymbolicIV.Prop21.prop21_II
#print axioms SymbolicIV.Prop21.prop21_II_proj
