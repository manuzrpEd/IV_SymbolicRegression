import Mathlib

/-!
# Theorem 3(a) (THEORY.md §6): fixed `L`, misspecified law

This file formalizes Theorem 3(a) of THEORY.md (paper: Theorem 3(a) of `theory.tex`): with (A0) and
(A2) dropped, the penalized estimator converges in probability to the pseudo-true set
`F* = argmin_{F_L} Q`, in the sense `Q(f̂) →_p Q*` and `inf_{f ∈ F*} ‖f̂ − f‖ →_p 0`.

**Setting.** `X` a metric space (the function space `L²(P_X)`; only its metric is used), `F : Set X`
compact and nonempty (the class `F_L`, compact by Lemma 1(a)), `Q : X → ℝ` continuous on `F` (the
population criterion). `Qstar := inf_{F} Q` and `Fstar := {f ∈ F | Q f = Qstar}`.

**Required items of the plan (U07).**
* `Fstar_nonempty`, `isCompact_Fstar`: `F*` is nonempty and compact.
* `Qstar_le`: `Q f ≥ Q*` on `F` (the "by definition" half of step 1).
* `exists_gap`: step 2, for every `ε > 0` there is `η > 0` with `Q f ≥ Q* + η` whenever `f ∈ F`
  is at distance `≥ ε` from every point of `F*`; `exists_gap_infDist` is the same with
  `inf_{g ∈ F*} dist f g ≥ ε`.
* `basic_inequality`: step 1, if `sup_F |Q_n − Q| ≤ R` and `Q_n(f̂) ≤ Q_n(f*) + η'` for some
  `f* ∈ F*`, then `Q(f̂) ≤ Q* + 2R + η'`.

**Stretch (in-probability wrapper), proved.**
* `tendsto_infDist_of_tendsto_Q`: if `P(Q(f̂_n) ≥ Q* + η) → 0` for every `η > 0`, then
  `P(inf_{g ∈ F*} dist(f̂_n, g) ≥ ε) → 0` for every `ε > 0`.
* `tendsto_Q_fhat`: `P(Q(f̂_n) ≥ Q* + η) → 0` from the uniform law `R_n →_p 0`, the slack
  `η'_n →_p 0` (the paper's `σ̂² max_s pen_n(s)/n`, which is `o_p(1)` by `κ_n/n → 0` and
  `σ̂² = O_p(1)`), and the event `A_n` ("`Ŝ` contains a tree of some `f* ∈ F*`") of probability
  tending to one on which the argmin inequality `Q_n(f̂) ≤ Q_n(f*) + η'_n` holds.
* `theorem3a`: both conclusions together.

## Hypotheses added beyond the paper (modelling choices)

* `Q` is only assumed continuous on `F` (`ContinuousOn`), as in the paper's statement.
* Sample objects are functions of the sample point `ω`: `Q_n`, `R_n`, `η'_n`, `f̂_n`. No
  measurability is assumed: probabilities are outer measures `μ.real` of a finite measure `μ`, and
  only monotonicity and finite subadditivity are used. "`P(A_n) → 1`" is therefore stated as
  "`P(A_nᶜ) → 0`" and convergence in probability as "`P(|·| ≥ δ) → 0` for all `δ > 0`".
* The argmin step `Q̂_ŝ ≤ Q_n(f*) + σ̂² max_s pen_n(s)/n` (U06 item 1) is taken as the hypothesis
  `hgood` on the good event `A_n`, with the slack `η'_n` an arbitrary sequence that is `o_p(1)`.
* `f̂_n(ω) ∈ F` for all `n, ω` (the estimator ranges over the class).
-/

open Filter Topology MeasureTheory Metric

namespace SymbolicIV.Thm3a

variable {X : Type*} [MetricSpace X]

/-- `Q* := inf_{f ∈ F} Q f`. -/
noncomputable def Qstar (F : Set X) (Q : X → ℝ) : ℝ := sInf (Q '' F)

/-- `F* := argmin_F Q = {f ∈ F | Q f = Q*}`. -/
def Fstar (F : Set X) (Q : X → ℝ) : Set X := {f ∈ F | Q f = Qstar F Q}

section Deterministic

variable {F : Set X} {Q : X → ℝ}

/-- `Q f ≥ Q*` for `f ∈ F` (the image is bounded below by compactness and continuity). -/
theorem Qstar_le (hF : IsCompact F) (hQ : ContinuousOn Q F) {f : X} (hf : f ∈ F) :
    Qstar F Q ≤ Q f :=
  csInf_le (hF.bddBelow_image hQ) (Set.mem_image_of_mem Q hf)

/-- A minimizer of `Q` on `F` lies in `F*`. -/
theorem mem_Fstar_of_isMinOn (hF : IsCompact F) (hQ : ContinuousOn Q F) {f : X} (hf : f ∈ F)
    (hmin : IsMinOn Q F f) : f ∈ Fstar F Q := by
  refine ⟨hf, le_antisymm ?_ (Qstar_le hF hQ hf)⟩
  apply le_csInf (Set.Nonempty.image Q ⟨f, hf⟩)
  rintro _ ⟨g, hg, rfl⟩
  exact hmin hg

/-- `F*` is nonempty (extreme value theorem). -/
theorem Fstar_nonempty (hF : IsCompact F) (hFne : F.Nonempty) (hQ : ContinuousOn Q F) :
    (Fstar F Q).Nonempty := by
  obtain ⟨f, hf, hmin⟩ := hF.exists_isMinOn hFne hQ
  exact ⟨f, mem_Fstar_of_isMinOn hF hQ hf hmin⟩

omit [MetricSpace X] in
/-- `F* ⊆ F`. -/
theorem Fstar_subset : Fstar F Q ⊆ F := fun _ hf => hf.1

/-- `F*` is compact: a closed subset (level set of a continuous function) of the compact `F`. -/
theorem isCompact_Fstar (hF : IsCompact F) (hQ : ContinuousOn Q F) : IsCompact (Fstar F Q) := by
  have hclosed : IsClosed (F ∩ Q ⁻¹' {Qstar F Q}) :=
    hQ.preimage_isClosed_of_isClosed hF.isClosed isClosed_singleton
  have heq : Fstar F Q = F ∩ Q ⁻¹' {Qstar F Q} := by
    ext f; simp [Fstar]
  rw [heq]
  exact hF.of_isClosed_subset hclosed Set.inter_subset_left

/-- Step 2 of the proof: by compactness and continuity, for every `ε > 0`,
`inf {Q f : f ∈ F, dist(f, F*) ≥ ε} > Q*`. -/
theorem exists_gap (hF : IsCompact F) (hQ : ContinuousOn Q F) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ f ∈ F, (∀ g ∈ Fstar F Q, ε ≤ dist f g) → Qstar F Q + η ≤ Q f := by
  set K : Set X := F ∩ {f | ∀ g ∈ Fstar F Q, ε ≤ dist f g} with hKdef
  have hKclosed : IsClosed {f : X | ∀ g ∈ Fstar F Q, ε ≤ dist f g} := by
    have : {f : X | ∀ g ∈ Fstar F Q, ε ≤ dist f g} = ⋂ g ∈ Fstar F Q, {f | ε ≤ dist f g} := by
      ext f; simp
    rw [this]
    exact isClosed_biInter fun g _ =>
      isClosed_le continuous_const (continuous_id.dist continuous_const)
  have hK : IsCompact K := hF.inter_right hKclosed
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · refine ⟨1, one_pos, fun f hf hεf => ?_⟩
    have : f ∈ K := ⟨hf, hεf⟩
    rw [hKe] at this
    exact this.elim
  · obtain ⟨f₁, hf₁K, hmin⟩ := hK.exists_isMinOn hKne (hQ.mono Set.inter_subset_left)
    obtain ⟨hf₁F, hf₁far⟩ := hf₁K
    have hge : Qstar F Q ≤ Q f₁ := Qstar_le hF hQ hf₁F
    have hne : Q f₁ ≠ Qstar F Q := by
      intro h0
      have hmem : f₁ ∈ Fstar F Q := ⟨hf₁F, h0⟩
      have := hf₁far f₁ hmem
      rw [dist_self] at this
      linarith
    refine ⟨Q f₁ - Qstar F Q, by
      have := lt_of_le_of_ne hge (Ne.symm hne)
      linarith, fun f hf hεf => ?_⟩
    have : Q f₁ ≤ Q f := hmin (⟨hf, hεf⟩ : f ∈ K)
    linarith

/-- Step 2 in the paper's form, with `inf_{g ∈ F*} dist f g ≥ ε`. -/
theorem exists_gap_infDist (hF : IsCompact F) (hFne : F.Nonempty) (hQ : ContinuousOn Q F)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ f ∈ F, ε ≤ infDist f (Fstar F Q) → Qstar F Q + η ≤ Q f := by
  obtain ⟨η, hη, h⟩ := exists_gap hF hQ hε
  refine ⟨η, hη, fun f hf hεf => h f hf ?_⟩
  exact fun g hg => (le_infDist (Fstar_nonempty hF hFne hQ)).1 hεf hg

omit [MetricSpace X] in
/-- Step 1 of the proof: the basic inequality. If `|Q_n − Q| ≤ R` on `F`, `f* ∈ F*`, and
`Q_n(f̂) ≤ Q_n(f*) + η'`, then `Q(f̂) ≤ Q* + 2R + η'`. -/
theorem basic_inequality {Qn : X → ℝ} {R η' : ℝ} (hunif : ∀ f ∈ F, |Qn f - Q f| ≤ R)
    {fhat fstar : X} (hfhat : fhat ∈ F) (hfstar : fstar ∈ Fstar F Q)
    (hargmin : Qn fhat ≤ Qn fstar + η') :
    Q fhat ≤ Qstar F Q + 2 * R + η' := by
  obtain ⟨hfstarF, hQstar⟩ := hfstar
  have h1 := abs_le.1 (hunif fhat hfhat)
  have h2 := abs_le.1 (hunif fstar hfstarF)
  linarith [h1.1, h1.2, h2.1, h2.2]

end Deterministic

section Probabilistic

/-! ### The in-probability wrapper (stretch goal)

`Ω` is the sample space with a finite measure `μ`; `fhat n ω ∈ F` is the estimator at sample size
`n`. Probabilities are `μ.real` of (not necessarily measurable) sets. -/

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
variable {F : Set X} {Q : X → ℝ}

/-- If `P(Q(f̂_n) ≥ Q* + η) → 0` for every `η > 0`, then
`P(inf_{g ∈ F*} dist(f̂_n, g) ≥ ε) → 0` for every `ε > 0`. -/
theorem tendsto_infDist_of_tendsto_Q (hF : IsCompact F) (hFne : F.Nonempty)
    (hQ : ContinuousOn Q F) {fhat : ℕ → Ω → X} (hfhat : ∀ n ω, fhat n ω ∈ F)
    (hQconv : ∀ η > 0, Tendsto (fun n => μ.real {ω | Qstar F Q + η ≤ Q (fhat n ω)}) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => μ.real {ω | ε ≤ infDist (fhat n ω) (Fstar F Q)}) atTop (𝓝 0) := by
  obtain ⟨η, hη, hgap⟩ := exists_gap_infDist hF hFne hQ hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hQconv η hη)
    (fun n => measureReal_nonneg) (fun n => ?_)
  refine measureReal_mono (fun ω hω => ?_) (measure_ne_top μ _)
  exact hgap _ (hfhat n ω) hω

omit [MetricSpace X] in
/-- Convergence of the criterion: `P(Q(f̂_n) ≥ Q* + η) → 0` for every `η > 0`, from
* the uniform law of large numbers (C2): `|Q_n(f) − Q(f)| ≤ R_n` on `F` with `R_n →_p 0`;
* the argmin inequality `Q_n(f̂_n) ≤ Q_n(f*) + η'_n` for some `f* ∈ F*` on the event `A_n`
  ("`Ŝ` contains a tree of some `f* ∈ F*`") with `P(A_nᶜ) → 0`, and slack `η'_n →_p 0`. -/
theorem tendsto_Q_fhat {fhat : ℕ → Ω → X} (hfhat : ∀ n ω, fhat n ω ∈ F)
    {Qn : ℕ → Ω → X → ℝ} {R η' : ℕ → Ω → ℝ} {A : ℕ → Set Ω}
    (hunif : ∀ n ω, ∀ f ∈ F, |Qn n ω f - Q f| ≤ R n ω)
    (hR : ∀ δ > 0, Tendsto (fun n => μ.real {ω | δ ≤ R n ω}) atTop (𝓝 0))
    (hη' : ∀ δ > 0, Tendsto (fun n => μ.real {ω | δ ≤ η' n ω}) atTop (𝓝 0))
    (hA : Tendsto (fun n => μ.real (A n)ᶜ) atTop (𝓝 0))
    (hgood : ∀ n, ∀ ω ∈ A n, ∃ fstar ∈ Fstar F Q, Qn n ω (fhat n ω) ≤ Qn n ω fstar + η' n ω)
    {η : ℝ} (hη : 0 < η) :
    Tendsto (fun n => μ.real {ω | Qstar F Q + η ≤ Q (fhat n ω)}) atTop (𝓝 0) := by
  have hsub : ∀ n, {ω | Qstar F Q + η ≤ Q (fhat n ω)} ⊆
      ((A n)ᶜ ∪ {ω | η / 4 ≤ R n ω}) ∪ {ω | η / 2 ≤ η' n ω} := by
    intro n ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_ofPred_eq, not_or, not_le] at hcon
    obtain ⟨⟨hAω, hRω⟩, hηω⟩ := hcon
    obtain ⟨fstar, hfstar, hargmin⟩ := hgood n ω (not_not.1 hAω)
    have := basic_inequality (hunif n ω) (hfhat n ω) hfstar hargmin
    have hω' : Qstar F Q + η ≤ Q (fhat n ω) := hω
    linarith
  have hlim : Tendsto (fun n => (μ.real (A n)ᶜ + μ.real {ω | η / 4 ≤ R n ω}) +
      μ.real {ω | η / 2 ≤ η' n ω}) atTop (𝓝 0) := by
    have := (hA.add (hR (η / 4) (by positivity))).add (hη' (η / 2) (by positivity))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun n => measureReal_nonneg) (fun n => ?_)
  calc μ.real {ω | Qstar F Q + η ≤ Q (fhat n ω)}
      ≤ μ.real (((A n)ᶜ ∪ {ω | η / 4 ≤ R n ω}) ∪ {ω | η / 2 ≤ η' n ω}) :=
        measureReal_mono (hsub n)
    _ ≤ μ.real ((A n)ᶜ ∪ {ω | η / 4 ≤ R n ω}) + μ.real {ω | η / 2 ≤ η' n ω} :=
        measureReal_union_le _ _
    _ ≤ (μ.real (A n)ᶜ + μ.real {ω | η / 4 ≤ R n ω}) + μ.real {ω | η / 2 ≤ η' n ω} := by
        gcongr
        exact measureReal_union_le _ _

/-- **Theorem 3(a).** Under the hypotheses of `tendsto_Q_fhat`, `Q(f̂_n) →_p Q*` and
`inf_{f ∈ F*} dist(f̂_n, f) →_p 0`. (Since `Q(f̂_n) ≥ Q*` always, the first statement is
`P(Q(f̂_n) ≥ Q* + η) → 0` for every `η > 0`.) -/
theorem theorem3a (hF : IsCompact F) (hFne : F.Nonempty) (hQ : ContinuousOn Q F)
    {fhat : ℕ → Ω → X} (hfhat : ∀ n ω, fhat n ω ∈ F)
    {Qn : ℕ → Ω → X → ℝ} {R η' : ℕ → Ω → ℝ} {A : ℕ → Set Ω}
    (hunif : ∀ n ω, ∀ f ∈ F, |Qn n ω f - Q f| ≤ R n ω)
    (hR : ∀ δ > 0, Tendsto (fun n => μ.real {ω | δ ≤ R n ω}) atTop (𝓝 0))
    (hη' : ∀ δ > 0, Tendsto (fun n => μ.real {ω | δ ≤ η' n ω}) atTop (𝓝 0))
    (hA : Tendsto (fun n => μ.real (A n)ᶜ) atTop (𝓝 0))
    (hgood : ∀ n, ∀ ω ∈ A n, ∃ fstar ∈ Fstar F Q, Qn n ω (fhat n ω) ≤ Qn n ω fstar + η' n ω) :
    (∀ n ω, Qstar F Q ≤ Q (fhat n ω)) ∧
    (∀ η > 0, Tendsto (fun n => μ.real {ω | Qstar F Q + η ≤ Q (fhat n ω)}) atTop (𝓝 0)) ∧
    (∀ ε > 0, Tendsto (fun n => μ.real {ω | ε ≤ infDist (fhat n ω) (Fstar F Q)}) atTop (𝓝 0)) := by
  have hQconv : ∀ η > 0,
      Tendsto (fun n => μ.real {ω | Qstar F Q + η ≤ Q (fhat n ω)}) atTop (𝓝 0) :=
    fun η hη => tendsto_Q_fhat hfhat hunif hR hη' hA hgood hη
  exact ⟨fun n ω => Qstar_le hF hQ (hfhat n ω), hQconv,
    fun ε hε => tendsto_infDist_of_tendsto_Q hF hFne hQ hfhat hQconv hε⟩

end Probabilistic

end SymbolicIV.Thm3a

#print axioms SymbolicIV.Thm3a.Fstar_nonempty
#print axioms SymbolicIV.Thm3a.isCompact_Fstar
#print axioms SymbolicIV.Thm3a.exists_gap
#print axioms SymbolicIV.Thm3a.basic_inequality
#print axioms SymbolicIV.Thm3a.tendsto_infDist_of_tendsto_Q
#print axioms SymbolicIV.Thm3a.tendsto_Q_fhat
#print axioms SymbolicIV.Thm3a.theorem3a
