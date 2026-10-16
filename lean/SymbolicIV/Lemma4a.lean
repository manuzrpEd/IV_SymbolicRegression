import Mathlib

/-!
# Lemma 4(a): hinge-spline approximation within a Lipschitz ball

Formalizes Lemma 4(a) of THEORY.md (§6, after the proof of Theorem 3(b); paper: theory.tex / appendix-proofs.tex,
"Lemma 4"), unit U09 of `FORMALIZATION_PLAN.md`.

## Setting

* `f₀ : ℝ → ℝ`, bounded by `A` on `[xlo, xhi]` and `Λ₀`-Lipschitz there (`LipschitzOnWith`).
* `k ≥ 1` subintervals, step `h := (xhi − xlo)/k`, knots `knot xlo h j = xlo + j h` (the paper's `x_j`),
  difference quotients `slope f xlo h j = (f x_{j+1} − f x_j)/h`.
* `interp f xlo h k` is the piecewise-linear interpolant `I_k f` of `f` at the `k+1` knots. It is
  *defined* directly in the paper's hinge form
  `f x₀ + s₀ (x − x₀) + ∑_{i<k−1} (s_{i+1} − s_i) max (x − x_{i+1}) 0`
  (so `b = s₀`, `a = f x₀ − s₀ x₀`, `c_j = s_j − s_{j−1}`, `κ_j = x_j`, `j = 1..k−1`), and
  `interp_eq_on_piece` / `interp_knot` prove that it is the linear interpolant on every subinterval.

## Results (numbering of the plan, section U09)

1. `interp_error_convex`, `interp_error_convex_knots`: the interpolation error at
   `x = λ x_j + (1−λ) x_{j+1}` is at most `2λ(1−λ) Λ₀ h ≤ Λ₀ h/2`.
2. `interp_sub_le` (`‖I_k f₀ − f₀‖_∞ ≤ Λ₀ (xhi − xlo)/(2k)` on `[xlo, xhi]`), `abs_interp_le`
   (`|I_k f₀| ≤ A` there), `interp_lipschitzOnWith` (`Λ₀`-Lipschitz there).
3. `hinge_representation`: `I_k f₀ x = a + b x + ∑_{j<k−1} c_j max (x − κ_j) 0` with `|b| ≤ Λ₀`,
   `|c_j| ≤ 2Λ₀`, `|κ_j| ≤ x̄ := max |xlo| |xhi|`, `|a| ≤ A + Λ₀ x̄`.
4. `knots_of_nodes`: for `L ≥ 8` and `k := ⌊(L+3)/8⌋`, `1 ≤ k`, `(L−4)/8 ≤ k`, and
   `Λ₀ (xhi − xlo)/(2k) ≤ 4Λ₀ (xhi − xlo)/(L−4) ≤ 8Λ₀ (xhi − xlo)/L`.
* `lemma4a`: everything assembled: for `L ≥ 8` the interpolant with `k = ⌊(L+3)/8⌋` has the hinge
  form with bounded constants, lies in the Lipschitz ball `ℋ`, and is within `8Λ₀ (xhi − xlo)/L` of
  `f₀` uniformly on `[xlo, xhi]`.
* Stretch: `Expr`, an expression-tree type with variables, constants, `+`, `−`, `×`, `max`; `Expr.size`,
  `Expr.eval`; `splineExpr` builds the hinge form as a tree and `splineExpr_size` /
  `splineExpr_eval` show it has `5 + 8(k−1)` nodes and evaluates to `I_k f₀`; `lemma4a_tree` packages
  this with the bounds above.

## Hypotheses beyond the paper's statement

* `xlo < xhi`: the support is an interval of positive width (the paper takes this for granted; with
  `xlo = xhi` the step `h` would be `0` and the difference quotients undefined).
* Nothing else: `|f₀| ≤ A` on `[xlo, xhi]` and `LipschitzOnWith Λ₀ f₀ (Icc xlo xhi)` are the paper's
  `f₀ ∈ ℋ`.

## Note on the paper's claim

The paper claims `I_k f₀ ∈ ℋ` "because its values are convex combinations of values of `f₀` and its
slopes are difference quotients of `f₀`". The second half needs the extra (elementary) step that a
continuous function which is `Λ₀`-Lipschitz on each of finitely many consecutive closed subintervals
is `Λ₀`-Lipschitz on their union; this is `interp_lipschitz_aux` below (induction on the knots).
-/

noncomputable section

open Finset Set

namespace Lemma4a

/-! ## Knots, slopes, interpolant -/

/-- The `j`-th knot `x_j = xlo + j h`. -/
def knot (xlo h : ℝ) (j : ℕ) : ℝ := xlo + j * h

/-- The difference quotient of `f` on `[x_j, x_{j+1}]`. -/
def slope (f : ℝ → ℝ) (xlo h : ℝ) (j : ℕ) : ℝ :=
  (f (knot xlo h (j + 1)) - f (knot xlo h j)) / h

/-- The piecewise-linear interpolant of `f` at the knots `x_0, …, x_k`, written in hinge form. -/
def interp (f : ℝ → ℝ) (xlo h : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  f xlo + slope f xlo h 0 * (x - xlo) +
    ∑ i ∈ range (k - 1), (slope f xlo h (i + 1) - slope f xlo h i) * max (x - knot xlo h (i + 1)) 0

@[simp] lemma knot_zero (xlo h : ℝ) : knot xlo h 0 = xlo := by simp [knot]

lemma knot_succ_sub (xlo h : ℝ) (j : ℕ) : knot xlo h (j + 1) - knot xlo h j = h := by
  simp only [knot]; push_cast; ring

lemma knot_mono {xlo h : ℝ} (hh : 0 ≤ h) {i j : ℕ} (hij : i ≤ j) : knot xlo h i ≤ knot xlo h j := by
  unfold knot
  have : (i : ℝ) ≤ j := by exact_mod_cast hij
  have := mul_le_mul_of_nonneg_right this hh
  linarith

lemma knot_mem_Icc {xlo xhi : ℝ} {k : ℕ} (hk : 1 ≤ k) (hlt : xlo < xhi) {j : ℕ} (hj : j ≤ k) :
    knot xlo ((xhi - xlo) / k) j ∈ Icc xlo xhi := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hh : 0 ≤ (xhi - xlo) / k := div_nonneg (by linarith) hkpos.le
  constructor
  · simpa using knot_mono (xlo := xlo) hh (Nat.zero_le j)
  · calc knot xlo ((xhi - xlo) / k) j ≤ knot xlo ((xhi - xlo) / k) k := knot_mono hh hj
      _ = xhi := by unfold knot; field_simp; ring

lemma slope_mul (f : ℝ → ℝ) (xlo : ℝ) {h : ℝ} (hh : h ≠ 0) (j : ℕ) :
    slope f xlo h j * h = f (knot xlo h (j + 1)) - f (knot xlo h j) := by
  unfold slope; field_simp

/-- The telescoping identity behind the hinge form: the partial hinge sum with the first `j`
hinges "switched on" is the `j`-th linear piece. Pure algebra, valid for every `x`. -/
lemma partial_sum_eq (f : ℝ → ℝ) {xlo h : ℝ} (hh : h ≠ 0) (x : ℝ) : ∀ j : ℕ,
    f xlo + slope f xlo h 0 * (x - xlo) +
      ∑ i ∈ range j, (slope f xlo h (i + 1) - slope f xlo h i) * (x - knot xlo h (i + 1))
    = f (knot xlo h j) + slope f xlo h j * (x - knot xlo h j)
  | 0 => by simp
  | j + 1 => by
    rw [sum_range_succ, ← add_assoc, partial_sum_eq f hh x j]
    have h1 := slope_mul f xlo hh j
    have h2 := knot_succ_sub xlo h j
    linear_combination slope f xlo h j * h2 + h1

/-- On the `j`-th subinterval `[x_j, x_{j+1}]` (`j < k`), `I_k f` is the linear interpolant
`f x_j + s_j (x − x_j)`. -/
lemma interp_eq_on_piece (f : ℝ → ℝ) {xlo h : ℝ} (hh : 0 < h) {k j : ℕ} (hj : j < k) {x : ℝ}
    (hx : x ∈ Icc (knot xlo h j) (knot xlo h (j + 1))) :
    interp f xlo h k x = f (knot xlo h j) + slope f xlo h j * (x - knot xlo h j) := by
  unfold interp
  rw [← partial_sum_eq f hh.ne' x j, ← sum_range_add_sum_Ico _ (show j ≤ k - 1 by omega)]
  congr 1
  have hz : ∑ i ∈ Ico j (k - 1),
      (slope f xlo h (i + 1) - slope f xlo h i) * max (x - knot xlo h (i + 1)) 0 = 0 := by
    apply sum_eq_zero
    intro i hi
    rw [Finset.mem_Ico] at hi
    have : knot xlo h (j + 1) ≤ knot xlo h (i + 1) := knot_mono hh.le (by omega)
    rw [max_eq_right (by linarith [hx.2]), mul_zero]
  rw [hz, add_zero]
  apply sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  have : knot xlo h (i + 1) ≤ knot xlo h j := knot_mono hh.le (by omega)
  rw [max_eq_left (by linarith [hx.1] : (0 : ℝ) ≤ x - knot xlo h (i + 1))]

/-- `I_k f` interpolates `f` at every knot. -/
lemma interp_knot (f : ℝ → ℝ) {xlo h : ℝ} (hh : 0 < h) {k : ℕ} (hk : 1 ≤ k) {j : ℕ} (hj : j ≤ k) :
    interp f xlo h k (knot xlo h j) = f (knot xlo h j) := by
  rcases Nat.lt_or_ge j k with hjk | hjk
  · rw [interp_eq_on_piece f hh hjk ⟨le_rfl, knot_mono hh.le (Nat.le_succ j)⟩]; ring
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have hjm : j = m + 1 := by omega
    subst hjm
    rw [interp_eq_on_piece f hh (Nat.lt_succ_self m) ⟨knot_mono hh.le (Nat.le_succ m), le_rfl⟩,
      knot_succ_sub, slope_mul f xlo hh.ne']
    ring

/-- The convex-combination form of the linear piece: with `λ := (x_{j+1} − x)/h`,
`x = λ x_j + (1−λ) x_{j+1}` and `I_k f x = λ f x_j + (1−λ) f x_{j+1}`. -/
lemma interp_eq_convex (f : ℝ → ℝ) {xlo h : ℝ} (hh : 0 < h) {k j : ℕ} (hj : j < k) {x : ℝ}
    (hx : x ∈ Icc (knot xlo h j) (knot xlo h (j + 1))) :
    let lam := (knot xlo h (j + 1) - x) / h
    lam ∈ Icc (0 : ℝ) 1 ∧ x = lam * knot xlo h j + (1 - lam) * knot xlo h (j + 1) ∧
      interp f xlo h k x = lam * f (knot xlo h j) + (1 - lam) * f (knot xlo h (j + 1)) := by
  intro lam
  have hd := knot_succ_sub xlo h j
  refine ⟨⟨div_nonneg (by linarith [hx.2]) hh.le, ?_⟩, ?_, ?_⟩
  · rw [div_le_one hh]; linarith [hx.1]
  · simp only [lam, knot]; push_cast; field_simp; ring
  · rw [interp_eq_on_piece f hh hj hx]
    simp only [lam, slope, knot]
    push_cast
    field_simp
    ring

/-! ## 1. The interpolation error on one subinterval -/

/-- Item 1 in abstract form: on `[a, b]`, at `x = λ a + (1−λ) b`, for a `Λ`-Lipschitz `f`,
`|λ (f x − f a) + (1−λ)(f x − f b)| ≤ 2λ(1−λ) Λ (b − a) ≤ Λ (b − a)/2`. -/
lemma interp_error_convex (f : ℝ → ℝ) {Λ a b lam x : ℝ} (hΛ : 0 ≤ Λ) (hab : a ≤ b)
    (hlam : lam ∈ Icc (0 : ℝ) 1) (hx : x = lam * a + (1 - lam) * b)
    (hfa : |f x - f a| ≤ Λ * |x - a|) (hfb : |f x - f b| ≤ Λ * |x - b|) :
    |lam * (f x - f a) + (1 - lam) * (f x - f b)| ≤ 2 * lam * (1 - lam) * Λ * (b - a) ∧
      2 * lam * (1 - lam) * Λ * (b - a) ≤ Λ * (b - a) / 2 := by
  obtain ⟨h0, h1⟩ := hlam
  have hp1 : 0 ≤ (1 - lam) * (b - a) := mul_nonneg (by linarith) (by linarith)
  have hp2 : 0 ≤ lam * (b - a) := mul_nonneg h0 (by linarith)
  have hxa : |x - a| = (1 - lam) * (b - a) := by
    rw [hx, abs_of_nonneg (by linarith)]; ring
  have hxb : |x - b| = lam * (b - a) := by
    rw [hx, abs_of_nonpos (by linarith)]; ring
  rw [hxa] at hfa
  rw [hxb] at hfb
  constructor
  · calc |lam * (f x - f a) + (1 - lam) * (f x - f b)|
        ≤ |lam * (f x - f a)| + |(1 - lam) * (f x - f b)| := abs_add_le _ _
      _ = lam * |f x - f a| + (1 - lam) * |f x - f b| := by
          rw [abs_mul, abs_mul, abs_of_nonneg h0, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - lam)]
      _ ≤ lam * (Λ * ((1 - lam) * (b - a))) + (1 - lam) * (Λ * (lam * (b - a))) := by
          gcongr
      _ = 2 * lam * (1 - lam) * Λ * (b - a) := by ring
  · have h4 : lam * (1 - lam) ≤ 1 / 4 := by nlinarith [sq_nonneg (lam - 1 / 2)]
    have hΛba : 0 ≤ Λ * (b - a) := mul_nonneg hΛ (by linarith)
    have := mul_le_mul_of_nonneg_right h4 hΛba
    linarith

/-- Item 1 at the knots: `x_j, x_{j+1}` with `j < k`, `h = (xhi − xlo)/k`, `f₀` Lipschitz on
`[xlo, xhi]`. -/
theorem interp_error_convex_knots (f₀ : ℝ → ℝ) {xlo xhi : ℝ} (Λ₀ : NNReal) (hlt : xlo < xhi)
    (hf : LipschitzOnWith Λ₀ f₀ (Icc xlo xhi)) {k j : ℕ} (hk : 1 ≤ k) (hj : j < k) {lam x : ℝ}
    (hlam : lam ∈ Icc (0 : ℝ) 1)
    (hx : x = lam * knot xlo ((xhi - xlo) / k) j + (1 - lam) * knot xlo ((xhi - xlo) / k) (j + 1)) :
    |lam * (f₀ x - f₀ (knot xlo ((xhi - xlo) / k) j)) +
        (1 - lam) * (f₀ x - f₀ (knot xlo ((xhi - xlo) / k) (j + 1)))|
      ≤ 2 * lam * (1 - lam) * Λ₀ * ((xhi - xlo) / k) ∧
    2 * lam * (1 - lam) * Λ₀ * ((xhi - xlo) / k) ≤ Λ₀ * ((xhi - xlo) / k) / 2 := by
  set h := (xhi - xlo) / k with hh_def
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hh : 0 < h := div_pos (by linarith) hkpos
  have hd := knot_succ_sub xlo h j
  have hxj : knot xlo h j ∈ Icc xlo xhi := knot_mem_Icc hk hlt hj.le
  have hxj1 : knot xlo h (j + 1) ∈ Icc xlo xhi := knot_mem_Icc hk hlt hj
  have hxmem : x ∈ Icc xlo xhi := by
    obtain ⟨h0, h1⟩ := hlam
    constructor
    · linarith [mul_nonneg h0 (sub_nonneg.2 hxj.1), mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 hxj1.1)]
    · linarith [mul_nonneg h0 (sub_nonneg.2 hxj.2), mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 hxj1.2)]
  have hL := fun y hy => hf.dist_le_mul x hxmem y hy
  simp only [Real.dist_eq] at hL
  have := interp_error_convex f₀ Λ₀.coe_nonneg (by linarith) hlam hx (hL _ hxj) (hL _ hxj1)
  rwa [hd] at this

/-! ## 2. Uniform error, boundedness, Lipschitz property of the interpolant -/

/-- Every `x ∈ [xlo, xhi]` lies in some subinterval `[x_j, x_{j+1}]` with `j < k`. -/
lemma exists_piece {xlo xhi : ℝ} {k : ℕ} (hk : 1 ≤ k) (hlt : xlo < xhi) {x : ℝ}
    (hx : x ∈ Icc xlo xhi) :
    ∃ j < k, x ∈ Icc (knot xlo ((xhi - xlo) / k) j) (knot xlo ((xhi - xlo) / k) (j + 1)) := by
  set h := (xhi - xlo) / k with hh_def
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hh : 0 < h := div_pos (by linarith) hkpos
  set t := (x - xlo) / h with ht_def
  have ht0 : 0 ≤ t := div_nonneg (by linarith [hx.1]) hh.le
  have hxt : x = xlo + t * h := by rw [ht_def, div_mul_cancel₀ _ hh.ne']; ring
  have htk : t ≤ k := by
    rw [ht_def, div_le_iff₀ hh, hh_def]; field_simp; linarith [hx.2]
  have hfl := Nat.floor_le ht0
  have hfl' := Nat.lt_floor_add_one t
  rcases Nat.lt_or_ge ⌊t⌋₊ k with hlt' | hge
  · refine ⟨⌊t⌋₊, hlt', ?_, ?_⟩
    · unfold knot; rw [hxt]
      have := mul_le_mul_of_nonneg_right hfl hh.le
      linarith
    · unfold knot; rw [hxt]; push_cast
      have := mul_le_mul_of_nonneg_right hfl'.le hh.le
      linarith
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    refine ⟨m, Nat.lt_succ_self m, ?_, ?_⟩
    · unfold knot; rw [hxt]
      have hmt : (m : ℝ) ≤ t := by
        have : ((m + 1 : ℕ) : ℝ) ≤ ⌊t⌋₊ := by exact_mod_cast hge
        push_cast at this; linarith
      have := mul_le_mul_of_nonneg_right hmt hh.le
      linarith
    · have : knot xlo h (m + 1) = xhi := by unfold knot; rw [hh_def]; field_simp; ring
      rw [this]; exact hx.2

/-- The slopes of the interpolant are difference quotients of `f₀`, hence bounded by `Λ₀`. -/
lemma abs_slope_le (f₀ : ℝ → ℝ) {xlo xhi Λ : ℝ} (hlt : xlo < xhi)
    (hf : ∀ x ∈ Icc xlo xhi, ∀ y ∈ Icc xlo xhi, |f₀ x - f₀ y| ≤ Λ * |x - y|)
    {k j : ℕ} (hk : 1 ≤ k) (hj : j < k) : |slope f₀ xlo ((xhi - xlo) / k) j| ≤ Λ := by
  set h := (xhi - xlo) / k with hh_def
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hh : 0 < h := div_pos (by linarith) hkpos
  have hd := knot_succ_sub xlo h j
  have := hf _ (knot_mem_Icc hk hlt hj) _ (knot_mem_Icc hk hlt hj.le)
  rw [hd, abs_of_pos hh] at this
  unfold slope
  rw [abs_div, abs_of_pos hh, div_le_iff₀ hh]
  exact this

/-- Item 2, uniform error: `|I_k f₀ x − f₀ x| ≤ Λ₀ (xhi − xlo)/(2k)` on `[xlo, xhi]`. -/
theorem interp_sub_le (f₀ : ℝ → ℝ) {xlo xhi : ℝ} (Λ₀ : NNReal) (hlt : xlo < xhi)
    (hf : LipschitzOnWith Λ₀ f₀ (Icc xlo xhi)) {k : ℕ} (hk : 1 ≤ k) {x : ℝ} (hx : x ∈ Icc xlo xhi) :
    |interp f₀ xlo ((xhi - xlo) / k) k x - f₀ x| ≤ Λ₀ * (xhi - xlo) / (2 * k) := by
  set h := (xhi - xlo) / k with hh_def
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hh : 0 < h := div_pos (by linarith) hkpos
  obtain ⟨j, hj, hxj⟩ := exists_piece hk hlt hx
  obtain ⟨hlam, hxeq, hI⟩ := interp_eq_convex f₀ hh hj hxj
  obtain ⟨h1, h2⟩ := interp_error_convex_knots f₀ Λ₀ hlt hf hk hj hlam hxeq
  rw [← hh_def] at h1 h2
  have : interp f₀ xlo h k x - f₀ x =
      -((knot xlo h (j + 1) - x) / h * (f₀ x - f₀ (knot xlo h j)) +
        (1 - (knot xlo h (j + 1) - x) / h) * (f₀ x - f₀ (knot xlo h (j + 1)))) := by
    rw [hI]; ring
  rw [this, abs_neg]
  calc _ ≤ _ := h1
    _ ≤ Λ₀ * h / 2 := h2
    _ = Λ₀ * (xhi - xlo) / (2 * k) := by rw [hh_def]; field_simp

/-- Item 2, boundedness: `|I_k f₀ x| ≤ A` on `[xlo, xhi]`. -/
theorem abs_interp_le (f₀ : ℝ → ℝ) {xlo xhi A : ℝ} (hlt : xlo < xhi)
    (hA : ∀ x ∈ Icc xlo xhi, |f₀ x| ≤ A) {k : ℕ} (hk : 1 ≤ k) {x : ℝ} (hx : x ∈ Icc xlo xhi) :
    |interp f₀ xlo ((xhi - xlo) / k) k x| ≤ A := by
  set h := (xhi - xlo) / k with hh_def
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hh : 0 < h := div_pos (by linarith) hkpos
  obtain ⟨j, hj, hxj⟩ := exists_piece hk hlt hx
  obtain ⟨⟨h0, h1⟩, -, hI⟩ := interp_eq_convex f₀ hh hj hxj
  rw [hI]
  have ha := hA _ (knot_mem_Icc hk hlt hj.le)
  have hb := hA _ (knot_mem_Icc hk hlt hj)
  rw [← hh_def] at ha hb
  calc |(knot xlo h (j + 1) - x) / h * f₀ (knot xlo h j) +
          (1 - (knot xlo h (j + 1) - x) / h) * f₀ (knot xlo h (j + 1))|
      ≤ |(knot xlo h (j + 1) - x) / h * f₀ (knot xlo h j)| +
          |(1 - (knot xlo h (j + 1) - x) / h) * f₀ (knot xlo h (j + 1))| := abs_add_le _ _
    _ = (knot xlo h (j + 1) - x) / h * |f₀ (knot xlo h j)| +
          (1 - (knot xlo h (j + 1) - x) / h) * |f₀ (knot xlo h (j + 1))| := by
        rw [abs_mul, abs_mul, abs_of_nonneg h0,
          abs_of_nonneg (show (0 : ℝ) ≤ 1 - (knot xlo h (j + 1) - x) / h by linarith)]
    _ ≤ (knot xlo h (j + 1) - x) / h * A + (1 - (knot xlo h (j + 1) - x) / h) * A := by
        gcongr
    _ = A := by ring

/-- On one subinterval the interpolant is affine with slope `s_j`, so `Λ`-Lipschitz there. -/
lemma interp_lipschitz_piece (f₀ : ℝ → ℝ) {xlo xhi Λ : ℝ} (hlt : xlo < xhi)
    (hf : ∀ x ∈ Icc xlo xhi, ∀ y ∈ Icc xlo xhi, |f₀ x - f₀ y| ≤ Λ * |x - y|)
    {k j : ℕ} (hk : 1 ≤ k) (hj : j < k) {x y : ℝ}
    (hx : x ∈ Icc (knot xlo ((xhi - xlo) / k) j) (knot xlo ((xhi - xlo) / k) (j + 1)))
    (hy : y ∈ Icc (knot xlo ((xhi - xlo) / k) j) (knot xlo ((xhi - xlo) / k) (j + 1))) :
    |interp f₀ xlo ((xhi - xlo) / k) k x - interp f₀ xlo ((xhi - xlo) / k) k y| ≤ Λ * |x - y| := by
  set h := (xhi - xlo) / k with hh_def
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hh : 0 < h := div_pos (by linarith) hkpos
  rw [interp_eq_on_piece f₀ hh hj hx, interp_eq_on_piece f₀ hh hj hy]
  have hs := abs_slope_le f₀ hlt hf hk hj
  rw [← hh_def] at hs
  calc |f₀ (knot xlo h j) + slope f₀ xlo h j * (x - knot xlo h j) -
          (f₀ (knot xlo h j) + slope f₀ xlo h j * (y - knot xlo h j))|
      = |slope f₀ xlo h j| * |x - y| := by rw [← abs_mul]; congr 1; ring
    _ ≤ Λ * |x - y| := by gcongr

/-- Induction on the knots: `I_k f₀` is `Λ`-Lipschitz on `[x_0, x_j]` for every `j ≤ k`
(ordered version `x ≤ y`). -/
lemma interp_lipschitz_aux (f₀ : ℝ → ℝ) {xlo xhi Λ : ℝ} (hlt : xlo < xhi)
    (hf : ∀ x ∈ Icc xlo xhi, ∀ y ∈ Icc xlo xhi, |f₀ x - f₀ y| ≤ Λ * |x - y|)
    {k : ℕ} (hk : 1 ≤ k) : ∀ j ≤ k, ∀ x ∈ Icc xlo (knot xlo ((xhi - xlo) / k) j),
      ∀ y ∈ Icc xlo (knot xlo ((xhi - xlo) / k) j), x ≤ y →
      |interp f₀ xlo ((xhi - xlo) / k) k x - interp f₀ xlo ((xhi - xlo) / k) k y| ≤ Λ * (y - x) := by
  set h := (xhi - xlo) / k with hh_def
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hh : 0 < h := div_pos (by linarith) hkpos
  intro j
  induction j with
  | zero =>
    intro _ x hx y hy hxy
    simp only [knot_zero] at hx hy
    have : x = y := le_antisymm hxy (by linarith [hx.1, hy.2])
    subst this; simp
  | succ j ih =>
    intro hjk x hx y hy hxy
    have hjk' : j < k := by omega
    have hpiece : ∀ {x y : ℝ}, x ∈ Icc (knot xlo h j) (knot xlo h (j + 1)) →
        y ∈ Icc (knot xlo h j) (knot xlo h (j + 1)) →
        |interp f₀ xlo h k x - interp f₀ xlo h k y| ≤ Λ * |x - y| :=
      fun hx hy => interp_lipschitz_piece f₀ hlt hf hk hjk' hx hy
    rcases le_or_gt y (knot xlo h j) with hyj | hyj
    · exact ih hjk'.le x ⟨hx.1, by linarith⟩ y ⟨hy.1, hyj⟩ hxy
    rcases le_or_gt (knot xlo h j) x with hxj | hxj
    · have := hpiece ⟨hxj, hx.2⟩ ⟨hyj.le, hy.2⟩
      rwa [abs_of_nonpos (show x - y ≤ 0 by linarith), neg_sub] at this
    · have hxlo : xlo ≤ knot xlo h j := by simpa using knot_mono (xlo := xlo) hh.le (Nat.zero_le j)
      have h1 := ih hjk'.le x ⟨hx.1, hxj.le⟩ (knot xlo h j) ⟨hxlo, le_rfl⟩ hxj.le
      have h2 := hpiece ⟨le_rfl, knot_mono hh.le (Nat.le_succ j)⟩ ⟨hyj.le, hy.2⟩
      rw [abs_of_nonpos (show knot xlo h j - y ≤ 0 by linarith), neg_sub] at h2
      calc |interp f₀ xlo h k x - interp f₀ xlo h k y|
          = |(interp f₀ xlo h k x - interp f₀ xlo h k (knot xlo h j)) +
              (interp f₀ xlo h k (knot xlo h j) - interp f₀ xlo h k y)| := by ring_nf
        _ ≤ |interp f₀ xlo h k x - interp f₀ xlo h k (knot xlo h j)| +
              |interp f₀ xlo h k (knot xlo h j) - interp f₀ xlo h k y| := abs_add_le _ _
        _ ≤ Λ * (knot xlo h j - x) + Λ * (y - knot xlo h j) := add_le_add h1 h2
        _ = Λ * (y - x) := by ring

/-- Item 2, Lipschitz property: `I_k f₀` is `Λ₀`-Lipschitz on `[xlo, xhi]`. -/
theorem interp_lipschitzOnWith (f₀ : ℝ → ℝ) {xlo xhi : ℝ} (Λ₀ : NNReal) (hlt : xlo < xhi)
    (hf : LipschitzOnWith Λ₀ f₀ (Icc xlo xhi)) {k : ℕ} (hk : 1 ≤ k) :
    LipschitzOnWith Λ₀ (interp f₀ xlo ((xhi - xlo) / k) k) (Icc xlo xhi) := by
  have hf' : ∀ x ∈ Icc xlo xhi, ∀ y ∈ Icc xlo xhi, |f₀ x - f₀ y| ≤ Λ₀ * |x - y| := by
    intro x hx y hy
    have := hf.dist_le_mul x hx y hy
    simpa only [Real.dist_eq] using this
  have hxhi : knot xlo ((xhi - xlo) / k) k = xhi := by
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
    unfold knot; field_simp; ring
  have aux := interp_lipschitz_aux f₀ hlt hf' hk k le_rfl
  rw [hxhi] at aux
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  simp only [Real.dist_eq]
  rcases le_or_gt x y with hxy | hxy
  · rw [abs_of_nonpos (show x - y ≤ 0 by linarith), neg_sub]; exact aux x hx y hy hxy
  · rw [abs_of_pos (show 0 < x - y by linarith)]
    have := aux y hy x hx hxy.le
    rwa [abs_sub_comm] at this

/-! ## 3. The hinge representation with bounded constants -/

/-- Item 3: `I_k f₀ x = a + b x + ∑_{j<k−1} c_j max (x − κ_j) 0` with `|b| ≤ Λ₀`, `|c_j| ≤ 2Λ₀`,
`|κ_j| ≤ x̄ := max |xlo| |xhi|`, `|a| ≤ A + Λ₀ x̄`. -/
theorem hinge_representation (f₀ : ℝ → ℝ) {xlo xhi A : ℝ} (Λ₀ : NNReal) (hlt : xlo < xhi)
    (hA : ∀ x ∈ Icc xlo xhi, |f₀ x| ≤ A) (hf : LipschitzOnWith Λ₀ f₀ (Icc xlo xhi))
    {k : ℕ} (hk : 1 ≤ k) :
    ∃ (a b : ℝ) (c κ : ℕ → ℝ),
      |b| ≤ Λ₀ ∧ (∀ j < k - 1, |c j| ≤ 2 * Λ₀) ∧ (∀ j < k - 1, |κ j| ≤ max |xlo| |xhi|) ∧
      |a| ≤ A + Λ₀ * max |xlo| |xhi| ∧
      ∀ x, interp f₀ xlo ((xhi - xlo) / k) k x = a + b * x + ∑ j ∈ range (k - 1), c j * max (x - κ j) 0 := by
  set h := (xhi - xlo) / k with hh_def
  have hf' : ∀ x ∈ Icc xlo xhi, ∀ y ∈ Icc xlo xhi, |f₀ x - f₀ y| ≤ Λ₀ * |x - y| := by
    intro x hx y hy
    have := hf.dist_le_mul x hx y hy
    simpa only [Real.dist_eq] using this
  have hs : ∀ j < k, |slope f₀ xlo h j| ≤ Λ₀ := fun j hj => by
    have := abs_slope_le f₀ hlt hf' hk hj; rwa [← hh_def] at this
  have hxlo : |xlo| ≤ max |xlo| |xhi| := le_max_left _ _
  refine ⟨f₀ xlo - slope f₀ xlo h 0 * xlo, slope f₀ xlo h 0,
    fun j => slope f₀ xlo h (j + 1) - slope f₀ xlo h j, fun j => knot xlo h (j + 1),
    hs 0 hk, ?_, ?_, ?_, ?_⟩
  · intro j hj
    calc |slope f₀ xlo h (j + 1) - slope f₀ xlo h j|
        ≤ |slope f₀ xlo h (j + 1)| + |slope f₀ xlo h j| := abs_sub _ _
      _ ≤ Λ₀ + Λ₀ := add_le_add (hs _ (by omega)) (hs _ (by omega))
      _ = 2 * Λ₀ := by ring
  · intro j hj
    have hm := knot_mem_Icc hk hlt (j := j + 1) (by omega)
    rw [← hh_def] at hm
    exact abs_le_max_abs_abs hm.1 hm.2
  · have hA0 := hA xlo ⟨le_rfl, hlt.le⟩
    calc |f₀ xlo - slope f₀ xlo h 0 * xlo|
        ≤ |f₀ xlo| + |slope f₀ xlo h 0 * xlo| := abs_sub _ _
      _ = |f₀ xlo| + |slope f₀ xlo h 0| * |xlo| := by rw [abs_mul]
      _ ≤ A + Λ₀ * max |xlo| |xhi| := by gcongr; exact hs 0 hk
  · intro x
    unfold interp
    ring

/-! ## 4. From a node budget `L` to the number of knots -/

/-- Item 4: with `L ≥ 8` nodes, `k := ⌊(L+3)/8⌋` knots satisfy `1 ≤ k`, `(L−4)/8 ≤ k`, and
`w/(2k) ≤ 4w/(L−4) ≤ 8w/L` for every `w ≥ 0` (applied with `w = Λ₀ (xhi − xlo)`). -/
theorem knots_of_nodes {L k : ℕ} (hL : 8 ≤ L) (hk : k = (L + 3) / 8) :
    1 ≤ k ∧ ((L : ℝ) - 4) / 8 ≤ k ∧
      ∀ w : ℝ, 0 ≤ w → w / (2 * k) ≤ 4 * w / ((L : ℝ) - 4) ∧ 4 * w / ((L : ℝ) - 4) ≤ 8 * w / L := by
  have hdiv := Nat.div_add_mod (L + 3) 8
  have hmod := Nat.mod_lt (L + 3) (by norm_num : 0 < 8)
  have hk1 : 1 ≤ k := by omega
  have hk8 : L - 4 ≤ 8 * k := by omega
  have hk8' : ((L : ℝ) - 4) ≤ 8 * k := by
    have : ((L - 4 : ℕ) : ℝ) ≤ ((8 * k : ℕ) : ℝ) := by exact_mod_cast hk8
    rw [Nat.cast_sub (by omega)] at this
    push_cast at this ⊢
    linarith
  have hL8 : (8 : ℝ) ≤ L := by exact_mod_cast hL
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
  refine ⟨hk1, by linarith, ?_⟩
  intro w hw
  have hp1 := mul_le_mul_of_nonneg_left hk8' hw
  have hp2 := mul_le_mul_of_nonneg_left hL8 hw
  constructor
  · rw [div_le_div_iff₀ (by positivity) (by linarith)]
    linarith
  · rw [div_le_div_iff₀ (by linarith) (by linarith)]
    linarith

/-! ## Lemma 4(a) assembled -/

/-- **Lemma 4(a).** For `f₀` in the Lipschitz ball `ℋ = {|f| ≤ A, Lip(f) ≤ Λ₀}` on `[xlo, xhi]` and a
node budget `L ≥ 8`, the interpolant `g := I_k f₀` with `k = ⌊(L+3)/8⌋` knots
* is a hinge spline `a + b x + ∑_{j<k−1} c_j max (x − κ_j) 0` with `|b| ≤ Λ₀`, `|c_j| ≤ 2Λ₀`,
  `|κ_j| ≤ x̄`, `|a| ≤ A + Λ₀ x̄` (so `g ∈ 𝓕_{8k} ⊆ 𝓕_L` once `C ≥ max(2Λ₀, A + Λ₀ x̄, x̄)`);
* lies in `ℋ`;
* satisfies `‖g − f₀‖_∞ ≤ Λ₀ (xhi − xlo)/(2k) ≤ 8 Λ₀ (xhi − xlo)/L` on `[xlo, xhi]`. -/
theorem lemma4a (f₀ : ℝ → ℝ) {xlo xhi A : ℝ} (Λ₀ : NNReal) (hlt : xlo < xhi)
    (hA : ∀ x ∈ Icc xlo xhi, |f₀ x| ≤ A) (hf : LipschitzOnWith Λ₀ f₀ (Icc xlo xhi))
    {L k : ℕ} (hL : 8 ≤ L) (hk : k = (L + 3) / 8) :
    1 ≤ k ∧ ((L : ℝ) - 4) / 8 ≤ k ∧
    (∃ (a b : ℝ) (c κ : ℕ → ℝ),
      |b| ≤ Λ₀ ∧ (∀ j < k - 1, |c j| ≤ 2 * Λ₀) ∧ (∀ j < k - 1, |κ j| ≤ max |xlo| |xhi|) ∧
      |a| ≤ A + Λ₀ * max |xlo| |xhi| ∧
      ∀ x, interp f₀ xlo ((xhi - xlo) / k) k x
        = a + b * x + ∑ j ∈ range (k - 1), c j * max (x - κ j) 0) ∧
    (∀ x ∈ Icc xlo xhi, |interp f₀ xlo ((xhi - xlo) / k) k x| ≤ A) ∧
    LipschitzOnWith Λ₀ (interp f₀ xlo ((xhi - xlo) / k) k) (Icc xlo xhi) ∧
    (∀ x ∈ Icc xlo xhi,
      |interp f₀ xlo ((xhi - xlo) / k) k x - f₀ x| ≤ Λ₀ * (xhi - xlo) / (2 * k) ∧
      Λ₀ * (xhi - xlo) / (2 * k) ≤ 8 * (Λ₀ * (xhi - xlo)) / L) := by
  obtain ⟨hk1, hk2, hw⟩ := knots_of_nodes hL hk
  obtain ⟨hw1, hw2⟩ := hw (Λ₀ * (xhi - xlo)) (mul_nonneg Λ₀.coe_nonneg (by linarith))
  refine ⟨hk1, hk2, hinge_representation f₀ Λ₀ hlt hA hf hk1,
    fun x hx => abs_interp_le f₀ hlt hA hk1 hx, interp_lipschitzOnWith f₀ Λ₀ hlt hf hk1,
    fun x hx => ⟨interp_sub_le f₀ Λ₀ hlt hf hk1 hx, hw1.trans hw2⟩⟩

/-! ## Stretch: expression trees and the node count `5 + 8(k−1)` -/

/-- Expression trees in one variable with real constants and the operators `+`, `−`, `×`, `max`. -/
inductive Expr
  | var : Expr
  | const : ℝ → Expr
  | add : Expr → Expr → Expr
  | sub : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | max : Expr → Expr → Expr

namespace Expr

/-- Number of nodes (leaves and internal nodes). -/
def size : Expr → ℕ
  | var => 1
  | const _ => 1
  | add e₁ e₂ => 1 + e₁.size + e₂.size
  | sub e₁ e₂ => 1 + e₁.size + e₂.size
  | mul e₁ e₂ => 1 + e₁.size + e₂.size
  | max e₁ e₂ => 1 + e₁.size + e₂.size

/-- Evaluation at `x`. -/
def eval : Expr → ℝ → ℝ
  | var => fun x => x
  | const c => fun _ => c
  | add e₁ e₂ => fun x => e₁.eval x + e₂.eval x
  | sub e₁ e₂ => fun x => e₁.eval x - e₂.eval x
  | mul e₁ e₂ => fun x => e₁.eval x * e₂.eval x
  | max e₁ e₂ => fun x => Max.max (e₁.eval x) (e₂.eval x)

end Expr

/-- One hinge `c × max (x − κ, 0)`: seven nodes. -/
def hingeExpr (c κ : ℝ) : Expr :=
  .mul (.const c) (.max (.sub .var (.const κ)) (.const 0))

/-- The hinge spline `a + b x + ∑_{j<m} c_j max (x − κ_j) 0` as a tree: five nodes for `a + b x`,
eight more for each hinge (seven for the hinge, one for the `+`). -/
def splineExpr (a b : ℝ) (c κ : ℕ → ℝ) : ℕ → Expr
  | 0 => .add (.const a) (.mul (.const b) .var)
  | m + 1 => .add (splineExpr a b c κ m) (hingeExpr (c m) (κ m))

theorem splineExpr_size (a b : ℝ) (c κ : ℕ → ℝ) : ∀ m, (splineExpr a b c κ m).size = 5 + 8 * m
  | 0 => by simp [splineExpr, Expr.size]
  | m + 1 => by
    simp only [splineExpr, hingeExpr, Expr.size, splineExpr_size a b c κ m]; ring

theorem splineExpr_eval (a b : ℝ) (c κ : ℕ → ℝ) (x : ℝ) :
    ∀ m, (splineExpr a b c κ m).eval x = a + b * x + ∑ j ∈ range m, c j * max (x - κ j) 0
  | 0 => by simp [splineExpr, Expr.eval]
  | m + 1 => by
    simp only [splineExpr, hingeExpr, Expr.eval, splineExpr_eval a b c κ x m, sum_range_succ]
    ring

/-- **Lemma 4(a), tree form.** With `L ≥ 8` and `k = ⌊(L+3)/8⌋`, there is an expression tree with
`5 + 8(k−1) ≤ L` nodes, whose constants are bounded as in `hinge_representation`, that evaluates to
`I_k f₀`; hence it lies in `ℋ` and is within `8Λ₀ (xhi − xlo)/L` of `f₀` on `[xlo, xhi]`. -/
theorem lemma4a_tree (f₀ : ℝ → ℝ) {xlo xhi A : ℝ} (Λ₀ : NNReal) (hlt : xlo < xhi)
    (hA : ∀ x ∈ Icc xlo xhi, |f₀ x| ≤ A) (hf : LipschitzOnWith Λ₀ f₀ (Icc xlo xhi))
    {L k : ℕ} (hL : 8 ≤ L) (hk : k = (L + 3) / 8) :
    ∃ e : Expr, e.size = 5 + 8 * (k - 1) ∧ e.size ≤ L ∧
      (∀ x, e.eval x = interp f₀ xlo ((xhi - xlo) / k) k x) ∧
      (∀ x ∈ Icc xlo xhi, |e.eval x| ≤ A) ∧ LipschitzOnWith Λ₀ e.eval (Icc xlo xhi) ∧
      ∀ x ∈ Icc xlo xhi, |e.eval x - f₀ x| ≤ 8 * (Λ₀ * (xhi - xlo)) / L := by
  obtain ⟨hk1, -, ⟨a, b, c, κ, -, -, -, -, hrep⟩, hbd, hlip, herr⟩ :=
    lemma4a f₀ Λ₀ hlt hA hf hL hk
  have heval : ∀ x, (splineExpr a b c κ (k - 1)).eval x = interp f₀ xlo ((xhi - xlo) / k) k x :=
    fun x => by rw [splineExpr_eval, hrep]
  have hfun : (splineExpr a b c κ (k - 1)).eval = interp f₀ xlo ((xhi - xlo) / k) k := funext heval
  refine ⟨splineExpr a b c κ (k - 1), splineExpr_size a b c κ (k - 1), ?_, heval, ?_, ?_, ?_⟩
  · rw [splineExpr_size]
    have hdiv := Nat.div_add_mod (L + 3) 8
    omega
  · intro x hx; rw [heval]; exact hbd x hx
  · rw [hfun]; exact hlip
  · intro x hx; rw [heval]; exact (herr x hx).1.trans (herr x hx).2

end Lemma4a

#print axioms Lemma4a.interp_error_convex_knots
#print axioms Lemma4a.interp_sub_le
#print axioms Lemma4a.abs_interp_le
#print axioms Lemma4a.interp_lipschitzOnWith
#print axioms Lemma4a.hinge_representation
#print axioms Lemma4a.knots_of_nodes
#print axioms Lemma4a.lemma4a
#print axioms Lemma4a.lemma4a_tree
