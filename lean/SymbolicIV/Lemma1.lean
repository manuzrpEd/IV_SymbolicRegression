import Mathlib

/-!
# Lemma 1: identification on a compact class (THEORY.md §1, Lemma 1)

Formalized: Lemma 1 (a), (b), (c) of THEORY.md (paper: Lemma 1 of `theory.tex`), plus the
stretch goal "(A3) ⇒ continuity into L²".

## Abstract setting of the required part (`section Required`)

* `H`, `H'` are real normed spaces (the paper: `H = L²(P_X)`, `H' = L²` of the instrument side);
  `T : H →L[ℝ] H'` is a continuous linear map (the paper's conditional-expectation operator).
  The paper's bound `‖T‖ ≤ 1` is not needed: only continuity of `T` is used.
* `S` is a finite type of trees; for each `s`, `Θ s` is a compact topological space and
  `φ s : Θ s → H` is `θ ↦ f_s(·;θ)`. Continuity of each `φ s` is a hypothesis of the required part
  (it is the conclusion of Lemma 1(a)'s first sentence, proved from (A3) in the stretch part).
* (A2) is `A2 T φ f₀ : ∀ s θ, T (φ s θ - f₀) = 0 → φ s θ = f₀`.
* A tree is wrong (`Wrong φ f₀ s`) if `φ s θ ≠ f₀` for every `θ`; the class `F_L` is
  `classFL φ = ⋃ s, range (φ s)`.

## Hypotheses added beyond the paper

* Required part: none beyond the modelling choices above. `Θ s` may be empty (since the fifth
  pass the paper states that `Θ_s` is nonempty and that minima over empty sets are `+∞`; the
  statements here remain true, vacuously, for an empty `Θ s`). Part (a) is proved from the
  continuity hypothesis alone, (b) and (c) use (A2), as the paper now states.
* Stretch part (`section Stretch`): the parameter space `Θ` is assumed first countable
  (`FirstCountableTopology Θ`), which holds for the paper's compact subsets of `ℝ^p`; this is
  what lets continuity be checked along sequences, as in the paper's proof. The measure `μ` (the
  paper's `P_X`) is assumed finite (`IsFiniteMeasure μ`; `P_X` is a probability measure), and each
  `f_s(·;θ)` is assumed a.e. strongly measurable (`AEStronglyMeasurable`), which is the
  measurability clause of (A3) since the fourth pass (it is no longer beyond the paper).

## Discrepancies found

None. The paper's proof goes through as written.
-/

open Set Filter Topology MeasureTheory

namespace SymbolicIV.Lemma1

section Required

variable {H H' : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup H'] [NormedSpace ℝ H']
variable {S : Type*} [Fintype S]
variable {Θ : S → Type*} [∀ s, TopologicalSpace (Θ s)] [∀ s, CompactSpace (Θ s)]

/-- A tree `s` is *wrong* if no parameter value reproduces `f₀` (i.e. `s ∉ 𝒮₀`). -/
def Wrong (φ : ∀ s, Θ s → H) (f₀ : H) (s : S) : Prop := ∀ θ, φ s θ ≠ f₀

/-- The formula class `F_L = ⋃_s F_s`, `F_s = {f_s(·;θ) : θ ∈ Θ_s}`. -/
def classFL (φ : ∀ s, Θ s → H) : Set H := ⋃ s, Set.range (φ s)

/-- Restricted identification (A2) on the class `F_L`: `T(f - f₀) = 0` implies `f = f₀`. -/
def A2 (T : H →L[ℝ] H') (φ : ∀ s, Θ s → H) (f₀ : H) : Prop :=
  ∀ s θ, T (φ s θ - f₀) = 0 → φ s θ = f₀

omit [NormedSpace ℝ H] [Fintype S] in
/-- Lemma 1(a), first half: each `F_s` is compact (continuous image of a compact set). -/
theorem isCompact_range_tree (φ : ∀ s, Θ s → H) (s : S) (hφ : Continuous (φ s)) :
    IsCompact (Set.range (φ s)) :=
  isCompact_range hφ

omit [NormedSpace ℝ H] in
/-- Lemma 1(a), second half: `F_L` is compact (finite union of compact sets). -/
theorem isCompact_classFL (φ : ∀ s, Θ s → H) (hφ : ∀ s, Continuous (φ s)) :
    IsCompact (classFL φ) :=
  isCompact_iUnion fun s => isCompact_range (hφ s)

omit [Fintype S] in
/-- Lemma 1(b), one tree: a wrong tree has a positive separation
`δ_s = min_θ ‖T(f_s(·;θ) - f₀)‖² > 0`. -/
theorem separation_wrong (T : H →L[ℝ] H') (φ : ∀ s, Θ s → H) (f₀ : H)
    (hA2 : A2 T φ f₀) {s : S} (hφ : Continuous (φ s)) (hs : Wrong φ f₀ s) :
    ∃ δ > 0, ∀ θ, δ ≤ ‖T (φ s θ - f₀)‖ ^ 2 := by
  rcases isEmpty_or_nonempty (Θ s) with h | h
  · exact ⟨1, one_pos, fun θ => (IsEmpty.false θ).elim⟩
  · have hc : Continuous fun θ => ‖T (φ s θ - f₀)‖ ^ 2 :=
      ((T.continuous.comp (hφ.sub continuous_const)).norm).pow 2
    obtain ⟨θ₀, -, hθ₀⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hc.continuousOn
    refine ⟨‖T (φ s θ₀ - f₀)‖ ^ 2, ?_, fun θ => hθ₀ (Set.mem_univ θ)⟩
    have hne : T (φ s θ₀ - f₀) ≠ 0 := fun h0 => hs θ₀ (hA2 s θ₀ h0)
    exact pow_pos (norm_pos_iff.mpr hne) 2

/-- Lemma 1(b), all trees: a common separation `δ_L = min_{s wrong} δ_s > 0`. -/
theorem separation_common (T : H →L[ℝ] H') (φ : ∀ s, Θ s → H) (f₀ : H)
    (hA2 : A2 T φ f₀) (hφ : ∀ s, Continuous (φ s)) :
    ∃ δL > 0, ∀ s, Wrong φ f₀ s → ∀ θ, δL ≤ ‖T (φ s θ - f₀)‖ ^ 2 := by
  classical
  have hδ : ∀ s, ∃ δ > 0, Wrong φ f₀ s → ∀ θ, δ ≤ ‖T (φ s θ - f₀)‖ ^ 2 := by
    intro s
    by_cases hs : Wrong φ f₀ s
    · obtain ⟨δ, hδpos, h⟩ := separation_wrong T φ f₀ hA2 (hφ s) hs
      exact ⟨δ, hδpos, fun _ => h⟩
    · exact ⟨1, one_pos, fun h => (hs h).elim⟩
  choose δ hδpos hδ using hδ
  rcases isEmpty_or_nonempty S with hS | hS
  · exact ⟨1, one_pos, fun s => (IsEmpty.false s).elim⟩
  · refine ⟨Finset.univ.inf' Finset.univ_nonempty δ, ?_, ?_⟩
    · exact (Finset.lt_inf'_iff _).mpr fun s _ => hδpos s
    · intro s hs θ
      exact (Finset.inf'_le δ (Finset.mem_univ s)).trans (hδ s hs θ)

/-- Lemma 1(c): the modulus `ω_L(ε) = inf {‖T(f - f₀)‖² : f ∈ F_L, ‖f - f₀‖ ≥ ε}` is positive. -/
theorem modulus_pos (T : H →L[ℝ] H') (φ : ∀ s, Θ s → H) (f₀ : H)
    (hA2 : A2 T φ f₀) (hφ : ∀ s, Continuous (φ s)) {ε : ℝ} (hε : 0 < ε) :
    ∃ ω > 0, ∀ f ∈ classFL φ, ε ≤ ‖f - f₀‖ → ω ≤ ‖T (f - f₀)‖ ^ 2 := by
  set K : Set H := classFL φ ∩ {f | ε ≤ ‖f - f₀‖} with hKdef
  have hK : IsCompact K :=
    (isCompact_classFL φ hφ).inter_right
      (isClosed_le continuous_const ((continuous_id.sub continuous_const).norm))
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · refine ⟨1, one_pos, fun f hf hεf => ?_⟩
    have : f ∈ K := ⟨hf, hεf⟩
    rw [hKe] at this
    exact this.elim
  · have hc : Continuous fun f : H => ‖T (f - f₀)‖ ^ 2 :=
      ((T.continuous.comp (continuous_id.sub continuous_const)).norm).pow 2
    obtain ⟨f₁, hf₁K, hmin⟩ := hK.exists_isMinOn hKne hc.continuousOn
    refine ⟨‖T (f₁ - f₀)‖ ^ 2, ?_, fun f hf hεf => hmin (⟨hf, hεf⟩ : f ∈ K)⟩
    have hne : T (f₁ - f₀) ≠ 0 := by
      intro h0
      obtain ⟨hf₁FL, hεf₁⟩ := hf₁K
      obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hf₁FL
      obtain ⟨θ, hθ⟩ := hs
      have h1 : f₁ = f₀ := by
        rw [← hθ] at h0 ⊢
        exact hA2 s θ h0
      have h2 : ‖f₁ - f₀‖ = 0 := by rw [h1, sub_self, norm_zero]
      have h3 : ε ≤ ‖f₁ - f₀‖ := hεf₁
      linarith
    exact pow_pos (norm_pos_iff.mpr hne) 2

end Required

section Stretch

/-! ### Stretch: (A3) ⇒ continuity of `θ ↦ f(·;θ)` into `L²(μ)`

`f : Θ → X → ℝ` with `θ ↦ f θ x` continuous for every `x` and `|f θ x| ≤ F x` with `F ∈ L²(μ)`.
The proof is the paper's: along a sequence `θ_k → θ`, pointwise convergence plus the envelope give
`L²` convergence (dominated convergence, here through uniform integrability of a dominated family). -/

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- A family dominated by one `L^p` function is `L^p` (the envelope gives `f(·;θ) ∈ L²`). -/
theorem memLp_of_envelope {ι : Type*} (g : ι → X → ℝ)
    (hmeas : ∀ i, AEStronglyMeasurable (g i) μ) (F : X → ℝ) {p : ENNReal} (hF : MemLp F p μ)
    (hbound : ∀ i x, |g i x| ≤ F x) (i : ι) : MemLp (g i) p μ :=
  hF.mono' (hmeas i) (Eventually.of_forall fun x => by
    simpa [Real.norm_eq_abs] using hbound i x)

/-- A family dominated by one `L^p` function is uniformly integrable. -/
theorem unifIntegrable_of_envelope {ι : Type*} (g : ι → X → ℝ)
    (hmeas : ∀ i, AEStronglyMeasurable (g i) μ) (F : X → ℝ) {p : ENNReal} (hp : 1 ≤ p)
    (hp' : p ≠ ⊤) (hF : MemLp F p μ) (hbound : ∀ i x, |g i x| ≤ F x) :
    UnifIntegrable g p μ := by
  refine unifIntegrable_of hp hp' hmeas fun ε hε => ?_
  obtain ⟨M, hM⟩ := hF.eLpNorm_indicator_norm_ge_le hε
  refine ⟨Real.toNNReal M, fun i => le_trans ?_ hM⟩
  have hset : NullMeasurableSet {x | Real.toNNReal M ≤ ‖g i x‖₊} μ :=
    nullMeasurableSet_le aemeasurable_const (hmeas i).nnnorm.aemeasurable
  refine eLpNorm_mono ((hmeas i).indicator₀ hset) fun x => ?_
  by_cases hx : x ∈ {x | Real.toNNReal M ≤ ‖g i x‖₊}
  · have hFx : 0 ≤ F x := (abs_nonneg _).trans (hbound i x)
    have h1 : ‖g i x‖ ≤ F x := by rw [Real.norm_eq_abs]; exact hbound i x
    have hM' : M ≤ ‖g i x‖ := by
      have : (Real.toNNReal M : ℝ) ≤ ((‖g i x‖₊ : NNReal) : ℝ) := by exact_mod_cast hx
      calc M ≤ (Real.toNNReal M : ℝ) := Real.le_coe_toNNReal M
        _ ≤ ‖g i x‖ := this
    have hx' : x ∈ {x | M ≤ ‖F x‖₊} := by
      show M ≤ ((‖F x‖₊ : NNReal) : ℝ)
      rw [coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg hFx]
      exact hM'.trans h1
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx', Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg hFx]
    exact hbound i x
  · rw [Set.indicator_of_notMem hx, norm_zero]
    exact norm_nonneg _

variable [IsFiniteMeasure μ]
variable {Θ : Type*} [TopologicalSpace Θ] [FirstCountableTopology Θ]

/-- The map `θ ↦ f(·;θ)` into `L²(μ)`. -/
noncomputable def toL2 (f : Θ → X → ℝ) (hf : ∀ θ, MemLp (f θ) 2 μ) (θ : Θ) : Lp ℝ 2 μ :=
  (hf θ).toLp (f θ)

/-- Lemma 1(a), first sentence, from (A3): pointwise continuity in `θ` plus a square-integrable
envelope give continuity of `θ ↦ f(·;θ)` into `L²(μ)`. -/
theorem continuous_toL2 (f : Θ → X → ℝ) (hmeas : ∀ θ, AEStronglyMeasurable (f θ) μ)
    (hcont : ∀ x, Continuous fun θ => f θ x) (F : X → ℝ) (hF : MemLp F 2 μ)
    (hbound : ∀ θ x, |f θ x| ≤ F x) :
    Continuous (toL2 f (memLp_of_envelope f hmeas F hF hbound)) := by
  have hmem := memLp_of_envelope f hmeas F hF hbound
  rw [continuous_iff_seqContinuous]
  intro u θ hu
  show Tendsto (fun n => (hmem (u n)).toLp (f (u n))) atTop (𝓝 ((hmem θ).toLp (f θ)))
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun n => f (u n)) (fun n => hmem (u n)) (f θ) (hmem θ)]
  refine tendsto_Lp_finite_of_tendsto_ae one_le_two ENNReal.ofNat_ne_top (fun n => hmeas (u n))
    (hmem θ) ?_ ?_
  · exact unifIntegrable_of_envelope (fun n => f (u n)) (fun n => hmeas (u n)) F one_le_two
      ENNReal.ofNat_ne_top hF (fun n x => hbound (u n) x)
  · exact Eventually.of_forall fun x => ((hcont x).tendsto θ).comp hu

/-- Lemma 1(a) in full from (A3): with `Θ` compact, the class `F_s = {f(·;θ)} ⊆ L²(μ)` is compact. -/
theorem isCompact_range_toL2 [CompactSpace Θ] (f : Θ → X → ℝ)
    (hmeas : ∀ θ, AEStronglyMeasurable (f θ) μ)
    (hcont : ∀ x, Continuous fun θ => f θ x) (F : X → ℝ) (hF : MemLp F 2 μ)
    (hbound : ∀ θ x, |f θ x| ≤ F x) :
    IsCompact (Set.range (toL2 f (memLp_of_envelope f hmeas F hF hbound))) :=
  isCompact_range (continuous_toL2 f hmeas hcont F hF hbound)

end Stretch

end SymbolicIV.Lemma1

#print axioms SymbolicIV.Lemma1.isCompact_classFL
#print axioms SymbolicIV.Lemma1.separation_wrong
#print axioms SymbolicIV.Lemma1.separation_common
#print axioms SymbolicIV.Lemma1.modulus_pos
#print axioms SymbolicIV.Lemma1.continuous_toL2
#print axioms SymbolicIV.Lemma1.isCompact_range_toL2
