import Mathlib

/-!
# Proposition 4: discrete instruments

Formalizes Proposition 4 of THEORY.md (§5, Proposition 4; paper: theory.tex / appendix-proofs.tex,
"Proposition 4"), unit U10 of `FORMALIZATION_PLAN.md`.

## Setting

* `H` is a real vector space of functions (the paper's `L²(P_X)`; no norm is needed here).
* `m : H →ₗ[ℝ] (Fin J → ℝ)` is the conditional-moment map `h ↦ (E[h(X) | Z = z_j])_j` (the paper's
  `μ`); only its linearity is used.
* Part (a): `ψ : Fin p → H` are the basis functions of a linear tree, `linFam ψ θ = ∑ k, θ k • ψ k`
  is `f_s(·;θ)`, `momMat m ψ` is the `J × p` matrix `Ψ = [E(ψ_k(X) | Z = z_j)]`, and `f₀ : H`.
* Part (b): `Φ : E → E'` is the moment map `θ ↦ m(f_s(·;θ))` between complete real normed spaces
  (`ℝ^p → ℝ^J` in the paper); `θb : E`, `Θ : Set E` the parameter set; a law `f₀` enters only through
  its moment vector `y = m f₀ : E'`. (In the lemmas named `prop4b`, `prop4b_fin` and
  `prop4b_statement_trivial` the letter `F` denotes the shifted map `θ ↦ m(f_s(·;θ) − f₀)` of the
  earlier wording of (b), see below.)

## Results

* `prop4a_moment_zero` : if `Ψθ = m f₀` then `m (f_s(·;θ) − f₀) = 0` (the one-line proof of (a)).
* `prop4a` : Proposition 4(a) assembled: under `f₀ ∉ 𝓕_s` (`f₀ ∉ linFam ψ '' Θ`, the family over
  `Θ_s`) and a solution `θ ∈ Θ_s` of `Ψθ = m f₀`, the tree has a parameter with `f_s(·;θ) ≠ f₀` and
  `m(f_s(·;θ) − f₀) = 0`, i.e. (A2_K) fails.
* `momMat_mulVec`, `surjective_of_rank_eq` and `prop4a_exists_solution` : `Ψθ = m(f_s(·;θ))`, a
  `J × p` real matrix of rank `J` is surjective, hence `Ψθ = t` is solvable for every target `t`
  (this is the "rank J" hypothesis of (a) made explicit; the paper additionally assumes that the
  solution lies in `Θ_s`, which is kept as a hypothesis in `prop4a`).
* (`θb` denotes the paper's `θ̄`.)
* `prop4b_ball_subset_image` : Lyusternik–Graves (Mathlib's `HasStrictFDerivAt.map_nhds_eq_of_surj`):
  if `F` is strictly differentiable at `θb` with surjective derivative and `Θ ∈ 𝓝 θb`, there is
  `r > 0` with `ball (F θb) r ⊆ F '' Θ`. This is the content of the proof of (b)
  (`B(F(θb), cρ) ⊆ F(B(θb, ρ))`, `r = cρ`).
* `prop4b_restated` : Proposition 4(b) as now stated in THEORY.md and theory.tex (fourth pass,
  2026-10-15): for `Φ` `C¹` near `θb` with surjective derivative and `θb` interior to `Θ`, there is
  `r > 0`, depending on `Φ`, `θb` and `Θ` only, such that every `y` (the moment vector `m f₀` of any
  law) with `‖Φ θb − y‖ < r` is `Φ θ` for some `θ ∈ Θ`, i.e. `m(f_s(·;θ) − f₀) = 0` by linearity of
  `m`. `prop4b_restated_fin` is the same on `ℝ^p → ℝ^J` with the rank of the Jacobian matrix.
* `prop4b`, `prop4b_fin` : the earlier wording of (b), with the shifted map `F = Φ − m f₀` and `f₀`
  fixed before `r`: `∃ r > 0, ‖F θb‖ < r → ∃ θ ∈ Θ, F θ = 0`. Kept because the ball inclusion they
  return is the informative part; the implication alone is vacuous, see the next item.
* `prop4b_statement_trivial` : the remark that led to the restatement: the *literal* implication
  `∃ r > 0, ‖F θb‖ < r → ∃ θ ∈ Θ, F θ = 0` holds for every map `F` and every `Θ ∋ θb` with no
  differentiability or rank assumption (take `r = ‖F θb‖/2` when `F θb ≠ 0`, and `θ = θb` otherwise).
  The informative statement is `prop4b_ball_subset_image` / `prop4b_restated`, where `r` depends
  only on the local behaviour of `Φ` near `θb` (its derivative and its modulus of strict
  differentiability) and on `Θ`, not on `f₀`.

## Hypotheses beyond the paper's statement

* (a) `m` is only assumed linear (the paper's `m` is linear since conditional expectation is);
  `f₀ ∉ 𝓕_s` is formalized as `f₀ ∉ linFam ψ '' Θ`, exactly the paper's `𝓕_s = {f_s(·;θ) : θ ∈ Θ_s}`.
  (The first version of this file assumed the stronger `f₀ ∉ Set.range (linFam ψ)`; the proof never
  needed it.)
* (b) "`C¹` near `θb`" is `ContDiffAt ℝ 1 F θb`; "Jacobian of rank `J`" is surjectivity of the Fréchet
  derivative (`LinearMap.range (fderiv ℝ F θb) = ⊤`), or in `prop4b_fin` literally the rank of its
  matrix; "`θb` interior to `Θ_s`" is `Θ ∈ 𝓝 θb`. The domain and codomain are complete normed spaces
  (true of `ℝ^p`, `ℝ^J`), as Mathlib's Lyusternik–Graves theorem requires.
-/

open Filter Topology Metric Set

noncomputable section

namespace SymbolicIV.Prop4

/-! ### Part (a): linear families -/

section LinearFamily

variable {H : Type*} [AddCommGroup H] [Module ℝ H] {J p : ℕ}

/-- The linear tree `f_s(·;θ) = ∑_k θ_k ψ_k`. -/
def linFam (ψ : Fin p → H) (θ : Fin p → ℝ) : H := ∑ k, θ k • ψ k

/-- `linFam ψ` as a linear map `ℝ^p →ₗ H`. -/
def linFamₗ (ψ : Fin p → H) : (Fin p → ℝ) →ₗ[ℝ] H where
  toFun := linFam ψ
  map_add' θ η := by simp [linFam, add_smul, Finset.sum_add_distrib]
  map_smul' c θ := by simp [linFam, Finset.smul_sum, smul_smul]

/-- The `J × p` matrix `Ψ = [E(ψ_k(X) | Z = z_j)]_{j,k} = [(m ψ_k)_j]`. -/
def momMat (m : H →ₗ[ℝ] (Fin J → ℝ)) (ψ : Fin p → H) : Matrix (Fin J) (Fin p) ℝ :=
  Matrix.of fun j k => m (ψ k) j

/-- `Ψ θ = m(f_s(·;θ))`. -/
theorem momMat_mulVec (m : H →ₗ[ℝ] (Fin J → ℝ)) (ψ : Fin p → H) (θ : Fin p → ℝ) :
    (momMat m ψ).mulVec θ = m (linFam ψ θ) := by
  ext j
  simp [momMat, linFam, Matrix.mulVec, dotProduct, map_sum, map_smul, mul_comm]

/-- The one-line proof of (a): `m(f_s(·;θ) − f₀) = Ψθ − m(f₀) = 0`. -/
theorem prop4a_moment_zero (m : H →ₗ[ℝ] (Fin J → ℝ)) (ψ : Fin p → H) (f₀ : H) (θ : Fin p → ℝ)
    (h : (momMat m ψ).mulVec θ = m f₀) : m (linFam ψ θ - f₀) = 0 := by
  rw [map_sub, ← momMat_mulVec, h, sub_self]

/-- Proposition 4(a): if `f₀ ∉ 𝓕_s` and `Ψθ = m(f₀)` has a solution `θ ∈ Θ_s`, then (A2_K) fails
at `s`: some `θ ∈ Θ_s` has `f_s(·;θ) ≠ f₀` and `m(f_s(·;θ) − f₀) = 0`. -/
theorem prop4a (m : H →ₗ[ℝ] (Fin J → ℝ)) (ψ : Fin p → H) (f₀ : H) (Θ : Set (Fin p → ℝ))
    (hf₀ : f₀ ∉ linFam ψ '' Θ)
    (hsol : ∃ θ ∈ Θ, (momMat m ψ).mulVec θ = m f₀) :
    ∃ θ ∈ Θ, linFam ψ θ ≠ f₀ ∧ m (linFam ψ θ - f₀) = 0 := by
  obtain ⟨θ, hθ, h⟩ := hsol
  exact ⟨θ, hθ, fun he => hf₀ ⟨θ, hθ, he⟩, prop4a_moment_zero m ψ f₀ θ h⟩

/-- A `J × p` real matrix of rank `J` is surjective (as a map `ℝ^p → ℝ^J`). -/
theorem surjective_of_rank_eq (A : Matrix (Fin J) (Fin p) ℝ) (hA : A.rank = J) :
    Function.Surjective A.mulVec := by
  have hrange : LinearMap.range A.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_fin_fun]
    exact hA
  intro t
  have ht : t ∈ LinearMap.range A.mulVecLin := by rw [hrange]; exact Submodule.mem_top
  obtain ⟨θ, hθ⟩ := ht
  exact ⟨θ, by simpa using hθ⟩

/-- The "rank `J`" hypothesis of (a): if `Ψ` has rank `J` then `Ψθ = t` is solvable for every
target `t ∈ ℝ^J`, in particular for `t = m(f₀)`. -/
theorem prop4a_exists_solution (m : H →ₗ[ℝ] (Fin J → ℝ)) (ψ : Fin p → H)
    (hrank : (momMat m ψ).rank = J) (t : Fin J → ℝ) :
    ∃ θ : Fin p → ℝ, m (linFam ψ θ) = t := by
  obtain ⟨θ, hθ⟩ := surjective_of_rank_eq (momMat m ψ) hrank t
  exact ⟨θ, by rw [← momMat_mulVec, hθ]⟩

end LinearFamily

/-! ### Part (b): general families (Lyusternik–Graves) -/

section General

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']

/-- Lyusternik–Graves, the content of the proof of (b): if `F` is strictly differentiable at `θb`
with surjective derivative `F'` and `Θ` is a neighbourhood of `θb`, then `F(Θ)` contains a ball
around `F(θb)`. -/
theorem prop4b_ball_subset_image (F : E → E') (F' : E →L[ℝ] E') (θb : E) (Θ : Set E)
    (hF : HasStrictFDerivAt F F' θb) (hsurj : LinearMap.range (F' : E →ₗ[ℝ] E') = ⊤) (hΘ : Θ ∈ 𝓝 θb) :
    ∃ r > 0, ball (F θb) r ⊆ F '' Θ := by
  have hmap : map F (𝓝 θb) = 𝓝 (F θb) := hF.map_nhds_eq_of_surj hsurj
  have himg : F '' Θ ∈ 𝓝 (F θb) := by
    rw [← hmap]
    exact image_mem_map hΘ
  exact Metric.mem_nhds_iff.1 himg

/-- Proposition 4(b): `F` is `C¹` near `θb` (`ContDiffAt ℝ 1 F θb`), its derivative at `θb` is onto,
and `θb` is interior to `Θ`; then there is `r > 0` such that `‖F θb‖ < r` implies `F θ = 0` for some
`θ ∈ Θ`. The `r` is that of `prop4b_ball_subset_image`, and the ball inclusion is returned as well. -/
theorem prop4b (F : E → E') (θb : E) (Θ : Set E)
    (hF : ContDiffAt ℝ 1 F θb) (hsurj : LinearMap.range (fderiv ℝ F θb : E →ₗ[ℝ] E') = ⊤) (hΘ : Θ ∈ 𝓝 θb) :
    ∃ r > 0, ball (F θb) r ⊆ F '' Θ ∧ (‖F θb‖ < r → ∃ θ ∈ Θ, F θ = 0) := by
  have hstrict : HasStrictFDerivAt F (fderiv ℝ F θb) θb := hF.hasStrictFDerivAt one_ne_zero
  obtain ⟨r, hr, hball⟩ := prop4b_ball_subset_image F (fderiv ℝ F θb) θb Θ hstrict hsurj hΘ
  refine ⟨r, hr, hball, fun hlt => ?_⟩
  have h0 : (0 : E') ∈ ball (F θb) r := by
    rw [mem_ball, dist_zero_left]
    exact hlt
  obtain ⟨θ, hθ, hFθ⟩ := hball h0
  exact ⟨θ, hθ, hFθ⟩

/-- Proposition 4(b) as restated (THEORY.md §5; theory.tex): `Φ` is `C¹` near `θb`, its derivative
at `θb` is onto, and `θb` is interior to `Θ`; then there is `r > 0`, determined by `Φ`, `θb` and `Θ`
alone, such that every target `y` with `‖Φ θb − y‖ < r` is attained on `Θ`: `Φ θ = y` for some
`θ ∈ Θ`. With `Φ θ = m(f_s(·;θ))` and `y = m f₀` this is `m(f_s(·;θ) − f₀) = 0`. -/
theorem prop4b_restated (Φ : E → E') (θb : E) (Θ : Set E)
    (hΦ : ContDiffAt ℝ 1 Φ θb) (hsurj : LinearMap.range (fderiv ℝ Φ θb : E →ₗ[ℝ] E') = ⊤)
    (hΘ : Θ ∈ 𝓝 θb) :
    ∃ r > 0, ∀ y : E', ‖Φ θb - y‖ < r → ∃ θ ∈ Θ, Φ θ = y := by
  have hstrict : HasStrictFDerivAt Φ (fderiv ℝ Φ θb) θb := hΦ.hasStrictFDerivAt one_ne_zero
  obtain ⟨r, hr, hball⟩ := prop4b_ball_subset_image Φ (fderiv ℝ Φ θb) θb Θ hstrict hsurj hΘ
  refine ⟨r, hr, fun y hy => ?_⟩
  have hmem : y ∈ ball (Φ θb) r := by
    rw [mem_ball, dist_eq_norm, ← norm_neg, neg_sub]
    exact hy
  obtain ⟨θ, hθ, hΦθ⟩ := hball hmem
  exact ⟨θ, hθ, hΦθ⟩

/-- Remark (the reason for the restatement): the literal implication of the earlier wording of (b)
holds for every map `F` and every `Θ ∋ θb`, with no differentiability or rank assumption. -/
theorem prop4b_statement_trivial {X Y : Type*} [NormedAddCommGroup Y] (F : X → Y) (θb : X)
    (Θ : Set X) (hθb : θb ∈ Θ) :
    ∃ r > 0, ‖F θb‖ < r → ∃ θ ∈ Θ, F θ = 0 := by
  by_cases h : F θb = 0
  · exact ⟨1, one_pos, fun _ => ⟨θb, hθb, h⟩⟩
  · have hpos : 0 < ‖F θb‖ := norm_pos_iff.2 h
    refine ⟨‖F θb‖ / 2, by positivity, fun hlt => ?_⟩
    exact absurd hlt (not_lt.2 (by linarith))

end General

/-! ### Part (b) on `ℝ^p → ℝ^J` with the rank of the Jacobian matrix -/

section Fin

variable {p J : ℕ}

/-- Proposition 4(b) on `ℝ^p → ℝ^J` with the hypothesis "Jacobian of rank `J`" stated as the rank
of the matrix `LinearMap.toMatrix' (fderiv ℝ F θb)` of the derivative. -/
theorem prop4b_fin (F : (Fin p → ℝ) → (Fin J → ℝ)) (θb : Fin p → ℝ) (Θ : Set (Fin p → ℝ))
    (hF : ContDiffAt ℝ 1 F θb)
    (hrank : (LinearMap.toMatrix' (fderiv ℝ F θb : (Fin p → ℝ) →ₗ[ℝ] (Fin J → ℝ))).rank = J)
    (hΘ : Θ ∈ 𝓝 θb) :
    ∃ r > 0, ball (F θb) r ⊆ F '' Θ ∧ (‖F θb‖ < r → ∃ θ ∈ Θ, F θ = 0) := by
  apply prop4b F θb Θ hF _ hΘ
  rw [LinearMap.range_eq_top]
  intro t
  obtain ⟨θ, hθ⟩ := surjective_of_rank_eq _ hrank t
  refine ⟨θ, ?_⟩
  rw [← hθ, LinearMap.toMatrix'_mulVec]

/-- `prop4b_restated` on `ℝ^p → ℝ^J` with "Jacobian of rank `J`" as the rank of the matrix of the
derivative. -/
theorem prop4b_restated_fin (Φ : (Fin p → ℝ) → (Fin J → ℝ)) (θb : Fin p → ℝ) (Θ : Set (Fin p → ℝ))
    (hΦ : ContDiffAt ℝ 1 Φ θb)
    (hrank : (LinearMap.toMatrix' (fderiv ℝ Φ θb : (Fin p → ℝ) →ₗ[ℝ] (Fin J → ℝ))).rank = J)
    (hΘ : Θ ∈ 𝓝 θb) :
    ∃ r > 0, ∀ y : Fin J → ℝ, ‖Φ θb - y‖ < r → ∃ θ ∈ Θ, Φ θ = y := by
  apply prop4b_restated Φ θb Θ hΦ _ hΘ
  rw [LinearMap.range_eq_top]
  intro t
  obtain ⟨θ, hθ⟩ := surjective_of_rank_eq _ hrank t
  refine ⟨θ, ?_⟩
  rw [← hθ, LinearMap.toMatrix'_mulVec]

end Fin

end SymbolicIV.Prop4

end

#print axioms SymbolicIV.Prop4.prop4a
#print axioms SymbolicIV.Prop4.prop4a_exists_solution
#print axioms SymbolicIV.Prop4.prop4b_ball_subset_image
#print axioms SymbolicIV.Prop4.prop4b
#print axioms SymbolicIV.Prop4.prop4b_fin
#print axioms SymbolicIV.Prop4.prop4b_restated
#print axioms SymbolicIV.Prop4.prop4b_restated_fin
#print axioms SymbolicIV.Prop4.prop4b_statement_trivial
