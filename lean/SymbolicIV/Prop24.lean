/-
# Proposition 2.4 (perturbed weights) — THEORY.md §4, Proposition 2.4; paper appendix-proofs.tex,
proof of Proposition 2.4.

Setting (abstract, as in the plan's unit U02). `E` is a real inner product space (the instrument
space; finite-dimensionality is not needed), `Z : E` the moment noise, `Θ` a type of parameters
(topology, compactness and nonemptiness enter only in the "minimum attained" step), `G E_ : Θ → E` the population-moment map `θ ↦ √n g(s,θ)/σ` and the empirical-process
map `θ ↦ E_s(θ)`.  The perturbed criterion is a function `q : E → ℝ` with the sandwich
`lm ‖x‖² ≤ q x ≤ lp ‖x‖²`, `0 < lm ≤ lp`, where `lm`, `lp` stand for the paper's λ₋, λ₊
(`λ` is a reserved token in Lean) (this is `n ĝ'Ŵĝ = σ² x'Ŵx`, `x = √n ĝ/σ`, under
`λ₋ σ⁻² I ⪯ Ŵ ⪯ λ₊ σ⁻² I`).  The localization radius is `r' = z (1 + √(lp/lm)) + d`.

Hypotheses of the Lean statements beyond the paper's:
* `0 ≤ dloc`.  Since the fourth pass (2026-10-15) the paper states it ("any bound `d_s^loc ≥ 0`
  with ..." in Proposition 2.1, which Proposition 2.4 inherits), so it is no longer beyond the paper.
  It is needed: when `Θ_s(r')` is empty the supremum alone does not force a sign, (II′) could then
  hold with a negative `π`, and the conclusion would fail.  The sign is what the proof uses
  ("(II′) forces π > 0").
* Self-adjointness of the weight is never used: only the sandwich on `q` enters.  The main theorems
  take a general `q` with the sandwich; `prop24_quadratic_form` instantiates `q x = ⟪x, A x⟫` for a
  continuous linear `A`.
* `W` is defined as `sSup` of the image of the direction set `D` under `v ↦ max ⟪-Z, v⟫ 0`, which is
  the paper's `sup_{v ∈ D} ⟪-Z, v⟫₊`, equal to `0` when `D = ∅` (`Real.sSup_empty`).
* The "minimum is attained" step (passing from a strict inequality at every `θ` to one for
  `J̃_n(s) = min_θ`) uses `[CompactSpace Θ] [Nonempty Θ]` and continuity of `G`, `E_`, as the paper
  does; the pointwise theorems need neither.
Nothing is assumed beyond this; there is no `sorry`.
-/
import Mathlib

open Set

noncomputable section

namespace SymbolicIV.Prop24

variable {E : Type*} [NormedAddCommGroup E]

/-! ## Triangle-inequality steps -/

lemma norm_add₃_ge (Z G E_ : E) : ‖G‖ - ‖Z‖ - ‖E_‖ ≤ ‖Z + G + E_‖ := by
  have h1 : ‖G‖ ≤ ‖Z + G + E_‖ + ‖Z + E_‖ := by
    calc ‖G‖ = ‖(Z + G + E_) - (Z + E_)‖ := by congr 1; abel
      _ ≤ ‖Z + G + E_‖ + ‖Z + E_‖ := norm_sub_le _ _
  have h2 : ‖Z + E_‖ ≤ ‖Z‖ + ‖E_‖ := norm_add_le _ _
  linarith

lemma norm_add_sub_ge (X E_ : E) : ‖X‖ - ‖E_‖ ≤ ‖X + E_‖ := by
  have h1 : ‖X‖ ≤ ‖X + E_‖ + ‖E_‖ := by
    calc ‖X‖ = ‖(X + E_) - E_‖ := by congr 1; abel
      _ ≤ ‖X + E_‖ + ‖E_‖ := norm_sub_le _ _
  linarith

variable [InnerProductSpace ℝ E]
variable {Θ : Type*}

/-! ## Definitions: localized set, directions, `W`, radius `r'` -/

/-- The localized parameter set `Θ_s(r) = {θ : ‖G θ‖ ≤ r}`. -/
def Θloc (G : Θ → E) (r : ℝ) : Set Θ := {θ | ‖G θ‖ ≤ r}

/-- The direction set `D_s(r) = {G θ / ‖G θ‖ : θ ∈ Θ_s(r), G θ ≠ 0}`. -/
def dirs (G : Θ → E) (r : ℝ) : Set E :=
  {v | ∃ θ ∈ Θloc G r, G θ ≠ 0 ∧ v = (‖G θ‖)⁻¹ • G θ}

/-- `W_s = sup_{v ∈ D_s(r)} ⟪-Z, v⟫₊`, equal to `0` when `D_s(r)` is empty. -/
def Wsup (Z : E) (G : Θ → E) (r : ℝ) : ℝ :=
  sSup ((fun v => max (inner ℝ (-Z) v) 0) '' dirs G r)

/-- The perturbed localization radius `r' = z (1 + √(lp/lm)) + d`. -/
def rad' (z d lm lp : ℝ) : ℝ := z * (1 + Real.sqrt (lp / lm)) + d

/-! ## Elementary facts about `D` and `W` -/

lemma norm_eq_one_of_mem_dirs {G : Θ → E} {r : ℝ} {v : E} (hv : v ∈ dirs G r) : ‖v‖ = 1 := by
  obtain ⟨θ, -, hθ, rfl⟩ := hv
  exact norm_smul_inv_norm hθ

lemma bddAbove_image_dirs (Z : E) (G : Θ → E) (r : ℝ) :
    BddAbove ((fun v => max (inner ℝ (-Z) v) 0) '' dirs G r) := by
  refine ⟨‖Z‖, ?_⟩
  rintro y ⟨v, hv, rfl⟩
  have h1 : inner ℝ (-Z) v ≤ ‖-Z‖ * ‖v‖ := real_inner_le_norm _ _
  rw [norm_neg, norm_eq_one_of_mem_dirs hv, mul_one] at h1
  exact max_le h1 (norm_nonneg Z)

lemma le_Wsup {Z : E} {G : Θ → E} {r : ℝ} {v : E} (hv : v ∈ dirs G r) :
    max (inner ℝ (-Z) v) 0 ≤ Wsup Z G r :=
  le_csSup (bddAbove_image_dirs Z G r) (mem_image_of_mem _ hv)

lemma Wsup_le_norm (Z : E) (G : Θ → E) (r : ℝ) : Wsup Z G r ≤ ‖Z‖ := by
  unfold Wsup
  rcases (dirs G r).eq_empty_or_nonempty with h | h
  · rw [h, image_empty, Real.sSup_empty]; exact norm_nonneg Z
  · apply csSup_le (h.image _)
    rintro y ⟨v, hv, rfl⟩
    have h1 : inner ℝ (-Z) v ≤ ‖-Z‖ * ‖v‖ := real_inner_le_norm _ _
    rw [norm_neg, norm_eq_one_of_mem_dirs hv, mul_one] at h1
    exact max_le h1 (norm_nonneg Z)

/-! ## Inside the localized set: the paper's "minimizing over the length ‖G‖" step -/

/-- `‖Z + G‖² ≥ ‖Z‖² − ⟪-Z, v⟫₊²` for `v = G/‖G‖`, `G ≠ 0`. -/
lemma norm_add_sq_ge_dir (Z G : E) (hG : G ≠ 0) :
    ‖Z‖ ^ 2 - (max (inner ℝ (-Z) ((‖G‖)⁻¹ • G)) 0) ^ 2 ≤ ‖Z + G‖ ^ 2 := by
  have ht : 0 < ‖G‖ := norm_pos_iff.mpr hG
  set c := inner ℝ Z ((‖G‖)⁻¹ • G) with hc
  have hZG : inner ℝ Z G = ‖G‖ * c := by
    rw [hc, real_inner_smul_right]; field_simp
  have hneg : inner ℝ (-Z) ((‖G‖)⁻¹ • G) = -c := by rw [inner_neg_left]
  rw [norm_add_sq_real, hZG, hneg]
  rcases le_or_gt 0 c with hc0 | hc0
  · rw [max_eq_right (by linarith)]
    nlinarith [mul_nonneg ht.le hc0, sq_nonneg ‖G‖]
  · rw [max_eq_left (by linarith)]
    nlinarith [sq_nonneg (‖G‖ + c)]

/-- `‖Z + G θ‖² ≥ ‖Z‖² − W²` for `θ` in the localized set (also when `G θ = 0`). -/
lemma norm_add_sq_ge_W (Z : E) (G : Θ → E) (r : ℝ) {θ : Θ} (hθ : θ ∈ Θloc G r) :
    ‖Z‖ ^ 2 - (Wsup Z G r) ^ 2 ≤ ‖Z + G θ‖ ^ 2 := by
  by_cases hG : G θ = 0
  · rw [hG, add_zero]; nlinarith [sq_nonneg (Wsup Z G r)]
  · have hv : (‖G θ‖)⁻¹ • G θ ∈ dirs G r := ⟨θ, hθ, hG, rfl⟩
    have h1 := norm_add_sq_ge_dir Z (G θ) hG
    have h2 := le_Wsup (Z := Z) hv
    have h3 : 0 ≤ max (inner ℝ (-Z) ((‖G θ‖)⁻¹ • G θ)) 0 := le_max_right _ _
    have h4 : (max (inner ℝ (-Z) ((‖G θ‖)⁻¹ • G θ)) 0) ^ 2 ≤ (Wsup Z G r) ^ 2 :=
      pow_le_pow_left₀ h3 h2 2
    linarith

/-- The inside bound of Proposition 2.1, reused by Proposition 2.4:
`‖Z + G θ + E θ‖² ≥ ‖Z‖² − W² − 2 z dloc` for `θ ∈ Θ_s(r)`. -/
theorem inside_bound (Z : E) (G E_ : Θ → E) (r z dloc : ℝ) (hz : ‖Z‖ ≤ z)
    {θ : Θ} (hθ : θ ∈ Θloc G r) (hE : ‖E_ θ‖ ≤ dloc) :
    ‖Z‖ ^ 2 - (Wsup Z G r) ^ 2 - 2 * z * dloc ≤ ‖Z + G θ + E_ θ‖ ^ 2 := by
  set W := Wsup Z G r
  set a := Real.sqrt (max (‖Z‖ ^ 2 - W ^ 2) 0) with ha_def
  set Δ := ‖E_ θ‖ with hΔ_def
  have hz0 : 0 ≤ z := (norm_nonneg Z).trans hz
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hΔ0 : 0 ≤ Δ := norm_nonneg _
  -- a² = max(‖Z‖² − W², 0) ≥ ‖Z‖² − W²
  have ha_sq : a ^ 2 = max (‖Z‖ ^ 2 - W ^ 2) 0 := Real.sq_sqrt (le_max_right _ _)
  have ha_sq_ge : ‖Z‖ ^ 2 - W ^ 2 ≤ a ^ 2 := by rw [ha_sq]; exact le_max_left _ _
  -- a ≤ ‖Z‖ ≤ z
  have ha_le : a ≤ ‖Z‖ := by
    have : max (‖Z‖ ^ 2 - W ^ 2) 0 ≤ ‖Z‖ ^ 2 :=
      max_le (by nlinarith [sq_nonneg W]) (sq_nonneg _)
    calc a ≤ Real.sqrt (‖Z‖ ^ 2) := Real.sqrt_le_sqrt this
      _ = ‖Z‖ := Real.sqrt_sq (norm_nonneg _)
  have haz : a ≤ z := ha_le.trans hz
  -- ‖Z + G‖ ≥ a
  have hZG : a ≤ ‖Z + G θ‖ := by
    have h1 := norm_add_sq_ge_W Z G r hθ
    have : max (‖Z‖ ^ 2 - W ^ 2) 0 ≤ ‖Z + G θ‖ ^ 2 := max_le h1 (sq_nonneg _)
    calc a ≤ Real.sqrt (‖Z + G θ‖ ^ 2) := Real.sqrt_le_sqrt this
      _ = ‖Z + G θ‖ := Real.sqrt_sq (norm_nonneg _)
  -- N := ‖Z + G + E‖ ≥ max (a − Δ) 0
  set N := ‖Z + G θ + E_ θ‖ with hN_def
  have hN0 : 0 ≤ N := norm_nonneg _
  have hN1 : a - Δ ≤ N := by
    have := norm_add_sub_ge (Z + G θ) (E_ θ)
    linarith
  have hN2 : max (a - Δ) 0 ≤ N := max_le hN1 hN0
  have hm0 : 0 ≤ max (a - Δ) 0 := le_max_right _ _
  have hN3 : (max (a - Δ) 0) ^ 2 ≤ N ^ 2 := pow_le_pow_left₀ hm0 hN2 2
  -- (a − Δ)₊² ≥ a² − 2aΔ
  have hpos : a ^ 2 - 2 * a * Δ ≤ (max (a - Δ) 0) ^ 2 := by
    rcases le_or_gt Δ a with h | h
    · rw [max_eq_left (by linarith)]; nlinarith [sq_nonneg Δ]
    · rw [max_eq_right (by linarith)]; nlinarith [mul_nonneg ha0 hΔ0]
  -- aΔ ≤ z dloc
  have haΔ : a * Δ ≤ z * dloc := mul_le_mul haz hE hΔ0 hz0
  nlinarith

/-! ## Outside the localized set -/

omit [InnerProductSpace ℝ E] in
theorem outside_bound (Z : E) (G E_ : Θ → E) (r z d : ℝ) (hz : ‖Z‖ ≤ z)
    {θ : Θ} (hθ : θ ∉ Θloc G r) (hE : ‖E_ θ‖ ≤ d) :
    r - z - d < ‖Z + G θ + E_ θ‖ := by
  have hG : r < ‖G θ‖ := lt_of_not_ge hθ
  have := norm_add₃_ge Z (G θ) (E_ θ)
  linarith

/-! ## Proposition 2.4 -/

section Main

variable (Z : E) (G E_ : Θ → E) (z d π lm lp : ℝ) (q : E → ℝ)

omit [InnerProductSpace ℝ E] in
/-- Condition (I′): the pointwise squared-norm bound `‖Z + G θ + E θ‖² > (lp/lm) z² + (−π)₊/lm`,
which is inequality (4.2) of the paper at every `θ`. -/
theorem norm_sq_gt_of_I' (hz : ‖Z‖ ≤ z) (hd : ∀ θ, ‖E_ θ‖ ≤ d)
    (a : ℝ) (ha : ∀ θ, a ≤ ‖G θ‖)
    (hI : z + d + Real.sqrt ((lp / lm) * z ^ 2 + max (-π) 0 / lm) < a) (θ : Θ) :
    (lp / lm) * z ^ 2 + max (-π) 0 / lm < ‖Z + G θ + E_ θ‖ ^ 2 := by
  have h1 := norm_add₃_ge Z (G θ) (E_ θ)
  have h2 := ha θ
  have h3 := hd θ
  have hsq : Real.sqrt ((lp / lm) * z ^ 2 + max (-π) 0 / lm) < ‖Z + G θ + E_ θ‖ := by linarith
  exact Real.lt_sq_of_sqrt_lt hsq

omit [InnerProductSpace ℝ E] in
/-- Proposition 2.4 under (I′): `q (Z + G θ + E θ) > lp ‖Z‖² − π` for every `θ`. -/
theorem prop24_I' (hz : ‖Z‖ ≤ z) (hd : ∀ θ, ‖E_ θ‖ ≤ d)
    (hlm : 0 < lm) (hl : lm ≤ lp)
    (hq_lo : ∀ x, lm * ‖x‖ ^ 2 ≤ q x)
    (a : ℝ) (ha : ∀ θ, a ≤ ‖G θ‖)
    (hI : z + d + Real.sqrt ((lp / lm) * z ^ 2 + max (-π) 0 / lm) < a) :
    ∀ θ, lp * ‖Z‖ ^ 2 - π < q (Z + G θ + E_ θ) := by
  intro θ
  have hN := norm_sq_gt_of_I' Z G E_ z d π lm lp hz hd a ha hI θ
  have hlp : 0 < lp := hlm.trans_le hl
  have hz0 : 0 ≤ z := (norm_nonneg Z).trans hz
  have hZz : ‖Z‖ ^ 2 ≤ z ^ 2 := pow_le_pow_left₀ (norm_nonneg Z) hz 2
  have hq := hq_lo (Z + G θ + E_ θ)
  have hS : lm * ((lp / lm) * z ^ 2 + max (-π) 0 / lm) = lp * z ^ 2 + max (-π) 0 := by
    field_simp
  have hmax : -π ≤ max (-π) 0 := le_max_left _ _
  have h1 : lm * ((lp / lm) * z ^ 2 + max (-π) 0 / lm) < lm * ‖Z + G θ + E_ θ‖ ^ 2 :=
    mul_lt_mul_of_pos_left hN hlm
  have h2 : lp * ‖Z‖ ^ 2 ≤ lp * z ^ 2 := mul_le_mul_of_nonneg_left hZz hlp.le
  linarith

/-- Proposition 2.4 under (II′): with the perturbed radius `r'`,
`q (Z + G θ + E θ) > lp ‖Z‖² − π` for every `θ`. -/
theorem prop24_II' (hz : ‖Z‖ ≤ z) (hd : ∀ θ, ‖E_ θ‖ ≤ d)
    (hlm : 0 < lm) (hl : lm ≤ lp)
    (hq_lo : ∀ x, lm * ‖x‖ ^ 2 ≤ q x)
    (dloc : ℝ) (hdloc0 : 0 ≤ dloc)
    (hdloc : ∀ θ ∈ Θloc G (rad' z d lm lp), ‖E_ θ‖ ≤ dloc)
    (hII : (lp - lm) * z ^ 2 + lm * ((Wsup Z G (rad' z d lm lp)) ^ 2 + 2 * z * dloc) < π) :
    ∀ θ, lp * ‖Z‖ ^ 2 - π < q (Z + G θ + E_ θ) := by
  intro θ
  have hlp : 0 < lp := hlm.trans_le hl
  have hz0 : 0 ≤ z := (norm_nonneg Z).trans hz
  have hZz : ‖Z‖ ^ 2 ≤ z ^ 2 := pow_le_pow_left₀ (norm_nonneg Z) hz 2
  have hq := hq_lo (Z + G θ + E_ θ)
  set r := rad' z d lm lp with hr
  set W := Wsup Z G r with hW
  -- (II′) forces π > 0
  have hπ : 0 < π := by
    have h1 : 0 ≤ (lp - lm) * z ^ 2 := mul_nonneg (by linarith) (sq_nonneg z)
    have h2 : 0 ≤ W ^ 2 + 2 * z * dloc := by positivity
    have h3 : 0 ≤ lm * (W ^ 2 + 2 * z * dloc) := mul_nonneg hlm.le h2
    linarith
  by_cases hθ : θ ∈ Θloc G r
  · -- inside: the Proposition 2.1 bound, then the sandwich and ‖Z‖² ≤ z²
    have hin : ‖Z‖ ^ 2 - W ^ 2 - 2 * z * dloc ≤ ‖Z + G θ + E_ θ‖ ^ 2 :=
      inside_bound Z G E_ r z dloc hz hθ (hdloc θ hθ)
    have h1 : lm * (‖Z‖ ^ 2 - W ^ 2 - 2 * z * dloc) ≤ lm * ‖Z + G θ + E_ θ‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hin hlm.le
    have h2 : (lp - lm) * ‖Z‖ ^ 2 ≤ (lp - lm) * z ^ 2 :=
      mul_le_mul_of_nonneg_left hZz (by linarith)
    nlinarith
  · -- outside: ‖Z + G + E‖ > z √(lp/lm), so q > lp z² ≥ lp ‖Z‖² ≥ lp ‖Z‖² − π
    have hout := outside_bound Z G E_ r z d hz hθ (hd θ)
    have hs0 : 0 ≤ Real.sqrt (lp / lm) := Real.sqrt_nonneg _
    have hrz : r - z - d = z * Real.sqrt (lp / lm) := by rw [hr]; unfold rad'; ring
    rw [hrz] at hout
    have hzs0 : 0 ≤ z * Real.sqrt (lp / lm) := mul_nonneg hz0 hs0
    have hN0 : 0 ≤ ‖Z + G θ + E_ θ‖ := norm_nonneg _
    have hsq : (z * Real.sqrt (lp / lm)) ^ 2 < ‖Z + G θ + E_ θ‖ ^ 2 := by
      have := pow_lt_pow_left₀ hout hzs0 (by norm_num : (2 : ℕ) ≠ 0)
      exact this
    have hsq' : (z * Real.sqrt (lp / lm)) ^ 2 = z ^ 2 * (lp / lm) := by
      rw [mul_pow, Real.sq_sqrt (div_nonneg hlp.le hlm.le)]
    have h1 : lm * (z ^ 2 * (lp / lm)) = lp * z ^ 2 := by field_simp
    have h2 : lm * (z ^ 2 * (lp / lm)) < lm * ‖Z + G θ + E_ θ‖ ^ 2 := by
      rw [← hsq']; exact mul_lt_mul_of_pos_left hsq hlm
    have h3 : lp * ‖Z‖ ^ 2 ≤ lp * z ^ 2 := mul_le_mul_of_nonneg_left hZz hlp.le
    linarith

/-- Proposition 2.4: either (I′) or (II′) gives `q (Z + G θ + E θ) > lp ‖Z‖² − π` for every `θ`. -/
theorem prop24 (hz : ‖Z‖ ≤ z) (hd : ∀ θ, ‖E_ θ‖ ≤ d)
    (hlm : 0 < lm) (hl : lm ≤ lp)
    (hq_lo : ∀ x, lm * ‖x‖ ^ 2 ≤ q x)
    (dloc : ℝ) (hdloc0 : 0 ≤ dloc)
    (hdloc : ∀ θ ∈ Θloc G (rad' z d lm lp), ‖E_ θ‖ ≤ dloc)
    (hI_or_II :
      (∃ a, (∀ θ, a ≤ ‖G θ‖) ∧
        z + d + Real.sqrt ((lp / lm) * z ^ 2 + max (-π) 0 / lm) < a) ∨
      (lp - lm) * z ^ 2 + lm * ((Wsup Z G (rad' z d lm lp)) ^ 2 + 2 * z * dloc) < π) :
    ∀ θ, lp * ‖Z‖ ^ 2 - π < q (Z + G θ + E_ θ) := by
  rcases hI_or_II with ⟨a, ha, hI⟩ | hII
  · exact prop24_I' Z G E_ z d π lm lp q hz hd hlm hl hq_lo a ha hI
  · exact prop24_II' Z G E_ z d π lm lp q hz hd hlm hl hq_lo dloc hdloc0 hdloc hII

end Main

/-! ## The criterion comparison (reduction step of the paper's proof) -/

omit [InnerProductSpace ℝ E] in
/-- The paper's reduction: `J̃(s*) ≤ q Z ≤ lp ‖Z‖²` (with `θ*` feasible, `√n ĝ(s*,θ*)/σ = Z`),
`pen(s*) ≤ penbar`, and `J̃(s) > lp ‖Z‖² − (pen(s) − penbar)` give
`J̃(s) + pen(s) > J̃(s*) + pen(s*)`. -/
theorem criterion_comparison (Z : E) (lp : ℝ) (q : E → ℝ) (hq_hi : ∀ x, q x ≤ lp * ‖x‖ ^ 2)
    (Jt Jtstar pen penbar penstar : ℝ)
    (hstar : Jtstar ≤ q Z) (hpen : penstar ≤ penbar)
    (hJ : lp * ‖Z‖ ^ 2 - (pen - penbar) < Jt) :
    Jtstar + penstar < Jt + pen := by
  have := hq_hi Z
  linarith

omit [InnerProductSpace ℝ E] in
/-- The paper's intermediate step (4.2): if `J̃(s) ≥ lm J(s)` and
`J(s) > (lp/lm) ‖Z‖² − π/lm`, then `J̃(s) > lp ‖Z‖² − π`. -/
theorem step_4_2 (Z : E) (lm lp π J Jt : ℝ) (hlm : 0 < lm) (hJt : lm * J ≤ Jt)
    (h42 : (lp / lm) * ‖Z‖ ^ 2 - π / lm < J) : lp * ‖Z‖ ^ 2 - π < Jt := by
  have h1 : lm * ((lp / lm) * ‖Z‖ ^ 2 - π / lm) < lm * J := mul_lt_mul_of_pos_left h42 hlm
  have h2 : lm * ((lp / lm) * ‖Z‖ ^ 2 - π / lm) = lp * ‖Z‖ ^ 2 - π := by field_simp
  linarith

/-- The minimum over a compact nonempty `Θ` of a continuous function is attained, so a strict
inequality at every `θ` gives a strict inequality for the infimum (the paper's `J̃_n(s) = min_θ`). -/
theorem iInf_gt_of_forall_gt [TopologicalSpace Θ] [CompactSpace Θ] [Nonempty Θ] (f : Θ → ℝ) (hf : Continuous f)
    (c : ℝ) (h : ∀ θ, c < f θ) : c < ⨅ θ, f θ := by
  obtain ⟨θ₀, -, hθ₀⟩ := isCompact_univ.exists_isMinOn univ_nonempty hf.continuousOn
  have hbdd : BddBelow (range f) := by
    refine ⟨c, ?_⟩
    rintro y ⟨θ, rfl⟩
    exact (h θ).le
  have hmin : ⨅ θ, f θ = f θ₀ := by
    apply le_antisymm
    · exact ciInf_le hbdd θ₀
    · exact le_ciInf fun θ => hθ₀ (mem_univ θ)
  rw [hmin]
  exact h θ₀

/-- Proposition 2.4 for the quadratic form `q x = ⟪x, A x⟫` of a continuous linear `A`, with the
minimum over `θ` taken (compact `Θ`, continuous `G`, `E_`), and the criterion comparison:
`J̃(s) + pen(s) > J̃(s*) + pen(s*)`, where `J̃(s) = ⨅ θ, ⟪Z + G θ + E θ, A (Z + G θ + E θ)⟫` and
`J̃(s*) ≤ ⟪Z, A Z⟫`. -/
theorem prop24_quadratic_form [TopologicalSpace Θ] [CompactSpace Θ] [Nonempty Θ]
    (Z : E) (G E_ : Θ → E) (hG : Continuous G) (hE : Continuous E_)
    (z d π lm lp : ℝ) (A : E →L[ℝ] E)
    (hz : ‖Z‖ ≤ z) (hd : ∀ θ, ‖E_ θ‖ ≤ d)
    (hlm : 0 < lm) (hl : lm ≤ lp)
    (hA_lo : ∀ x, lm * ‖x‖ ^ 2 ≤ inner ℝ x (A x)) (hA_hi : ∀ x, inner ℝ x (A x) ≤ lp * ‖x‖ ^ 2)
    (dloc : ℝ) (hdloc0 : 0 ≤ dloc)
    (hdloc : ∀ θ ∈ Θloc G (rad' z d lm lp), ‖E_ θ‖ ≤ dloc)
    (hI_or_II :
      (∃ a, (∀ θ, a ≤ ‖G θ‖) ∧
        z + d + Real.sqrt ((lp / lm) * z ^ 2 + max (-π) 0 / lm) < a) ∨
      (lp - lm) * z ^ 2 + lm * ((Wsup Z G (rad' z d lm lp)) ^ 2 + 2 * z * dloc) < π)
    (Jtstar pen penbar penstar : ℝ)
    (hstar : Jtstar ≤ inner ℝ Z (A Z)) (hpen : penstar ≤ penbar) (hπ : π = pen - penbar) :
    Jtstar + penstar <
      (⨅ θ, inner ℝ (Z + G θ + E_ θ) (A (Z + G θ + E_ θ))) + pen := by
  have hpt := prop24 Z G E_ z d π lm lp (fun x => inner ℝ x (A x)) hz hd hlm hl hA_lo
    dloc hdloc0 hdloc hI_or_II
  have hcont : Continuous fun θ => inner ℝ (Z + G θ + E_ θ) (A (Z + G θ + E_ θ)) := by
    have h1 : Continuous fun θ => Z + G θ + E_ θ := (continuous_const.add hG).add hE
    exact h1.inner (A.continuous.comp h1)
  have hinf := iInf_gt_of_forall_gt _ hcont (lp * ‖Z‖ ^ 2 - π) hpt
  have := criterion_comparison Z lp (fun x => inner ℝ x (A x)) hA_hi
    (⨅ θ, inner ℝ (Z + G θ + E_ θ) (A (Z + G θ + E_ θ))) Jtstar pen penbar penstar hstar hpen
    (by rw [← hπ]; exact hinf)
  exact this

end SymbolicIV.Prop24

end

#print axioms SymbolicIV.Prop24.inside_bound
#print axioms SymbolicIV.Prop24.prop24_I'
#print axioms SymbolicIV.Prop24.prop24_II'
#print axioms SymbolicIV.Prop24.prop24
#print axioms SymbolicIV.Prop24.criterion_comparison
#print axioms SymbolicIV.Prop24.step_4_2
#print axioms SymbolicIV.Prop24.iInf_gt_of_forall_gt
#print axioms SymbolicIV.Prop24.prop24_quadratic_form
