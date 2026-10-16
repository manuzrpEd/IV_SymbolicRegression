import Mathlib

/-!
# Theorem 2, the conditioning clause (THEORY.md §4, Lemma 3 and the proof of Theorem 2)

This file formalizes the one sentence of the proof of Theorem 2 that the first run left unchecked
(lean/REPORT.md, "What remains unverified by Lean", the tower-property clause):

  "The bounds of Lemma 3(b) and (d) are conditional on `Z_{1:n}` on the event of (a); their failure
  events are taken within (a) and integrated, which gives the same `e^{-t}`."

Lemma 3(b) and 3(d) (THEORY.md §4, Concentration) are bounds of the form
`P(B | Z_{1:n}) ≤ e^{-t}` valid on the event `A` of Lemma 3(a), where `B` is the failure event of
(b) (respectively (d)). The proof of Theorem 2 then intersects five events and
reaches probability at least `1 - 5 e^{-t}`. What is checked here:

1. `condProb_bound_integrates`: if `A ∈ σ(Z_{1:n})`, `B` is measurable and
   `P(B | Z_{1:n}) ≤ ε` a.e. on `A`, then `P(A ∩ B) ≤ ε P(A) ≤ ε` ("taken within (a) and
   integrated"). The proof is the tower property in its set-integral form,
   `∫_A 1_B dP = ∫_A P(B | Z_{1:n}) dP ≤ ε P(A)`.
2. `five_events`: with `A` the event of (a), `Bb`, `Bd` the failure events of (b) and (d) (with the
   conditional bounds of item 1 at `ε = e^{-t}`), and `Cc`, `Cc'` the failure events of the two
   applications of (c) (unconditional bounds `e^{-t}`), the good event
   `G := A ∩ Bbᶜ ∩ Ccᶜ ∩ Cc'ᶜ ∩ Bdᶜ` has `P(Gᶜ) ≤ 5 e^{-t}`.
3. `five_events_for_assembly`: the five sets `E₀ := A`, `E₁ := (A ∩ Bb)ᶜ`, `E₂ := Ccᶜ`,
   `E₃ := Cc'ᶜ`, `E₄ := (A ∩ Bd)ᶜ` each satisfy `P(Eᵢᶜ) ≤ e^{-t}` and `⋂ᵢ Eᵢ = G`. This is exactly
   the form (`∀ i : Fin 5, P (A i)ᶜ ≤ e^{-t}`) in which `Thm2Assembly.prob_not_mem_le` consumes the
   five events, so the two files compose without a gap. (That file is not imported; the project
   convention is one self-contained file per unit.)

## Setting

* `Ω` a measurable space `m0` with a probability measure `μ` (the sample space);
* `m ≤ m0` a sub-σ-algebra, standing for `σ(Z_{1:n})`; the conditional probability
  `P(B | Z_{1:n})` is Mathlib's conditional expectation `μ[1_B | m]` of the indicator of `B`;
* `A` an `m`-measurable set (the event of Lemma 3(a) is a function of `Z_{1:n}`, since `Σ̂` is);
* `B`, `Bb`, `Bd`, `Cc`, `Cc'` measurable sets.

## Hypotheses added beyond the paper's statement

* Measurability: `A` is `σ(Z_{1:n})`-measurable, the failure events are measurable. The paper
  treats these as events and conditions on `Z_{1:n}`, which presupposes exactly this.
* The conditional bound is taken in the almost-everywhere form
  `∀ᵐ ω ∂μ, ω ∈ A → μ[1_B | m] ω ≤ ε`, which is the only meaningful reading of a statement about a
  conditional probability (defined up to null sets). The paper's "on the event in (a)" is read as
  "a.e. on `A`".
* `0 ≤ ε` (automatic for `ε = e^{-t}`) is used only to pass from `ε P(A)` to `ε` and to the
  `ℝ≥0∞` form; it is not needed for `P(A ∩ B) ≤ ε P(A)` itself.
* `μ` is a probability measure (the paper's `P`). The identity `P(A ∩ B) = ∫_A P(B | Z_{1:n}) dP`
  needs `μ.trim hm` σ-finite, which Mathlib derives from finiteness of `μ`.
* Probabilities are written in `ℝ≥0∞` as `ENNReal.ofReal (Real.exp (-t))`, as in
  `Thm2Assembly.lean`; real-valued restatements are given.

No hypothesis of the paper was weakened and no conclusion was strengthened. In particular the
paper's `e^{-t}` for (b) and (d) is recovered unchanged, and nothing about the sets `Cc`, `Cc'`
beyond their unconditional bounds is used.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SymbolicIV.Thm2Conditioning

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- `P(A ∩ B)`, as a real number, is the integral over `A` of the indicator of `B`. -/
theorem toReal_measure_inter_eq_setIntegral (A : Set Ω) {B : Set Ω} (hB : MeasurableSet[m0] B) :
    (μ (A ∩ B)).toReal = ∫ ω in A, B.indicator (fun _ => (1 : ℝ)) ω ∂μ := by
  rw [setIntegral_indicator hB, setIntegral_const, smul_eq_mul, mul_one, measureReal_def]

/-- **Required item 1.** A conditional bound `P(B | m) ≤ ε` a.e. on an `m`-measurable event `A`
integrates to `P(A ∩ B) ≤ ε P(A)`. This is the sentence "their failure events are taken within (a)
and integrated" (THEORY.md §4, proof of Theorem 2), i.e. the tower property. -/
theorem condProb_bound_integrates [IsProbabilityMeasure μ] {m : MeasurableSpace Ω} (hm : m ≤ m0)
    {A B : Set Ω} (hA : MeasurableSet[m] A) (hB : MeasurableSet[m0] B) (ε : ℝ)
    (hcond : ∀ᵐ ω ∂μ, ω ∈ A → (μ[B.indicator (fun _ => (1 : ℝ)) | m]) ω ≤ ε) :
    (μ (A ∩ B)).toReal ≤ ε * (μ A).toReal := by
  have hint : Integrable (B.indicator (fun _ => (1 : ℝ))) μ := (integrable_const 1).indicator hB
  have hAm0 : MeasurableSet[m0] A := hm A hA
  calc (μ (A ∩ B)).toReal
      = ∫ ω in A, B.indicator (fun _ => (1 : ℝ)) ω ∂μ := toReal_measure_inter_eq_setIntegral A hB
    _ = ∫ ω in A, (μ[B.indicator (fun _ => (1 : ℝ)) | m]) ω ∂μ :=
        (setIntegral_condExp hm hint hA).symm
    _ ≤ ∫ _ω in A, ε ∂μ :=
        setIntegral_mono_on_ae integrable_condExp.integrableOn (integrable_const ε).integrableOn
          hAm0 hcond
    _ = ε * (μ A).toReal := by rw [setIntegral_const, smul_eq_mul, mul_comm, measureReal_def]

/-- Corollary of item 1 on a probability measure: `P(A ∩ B) ≤ ε`, "which gives the same `e^{-t}`"
(THEORY.md §4, proof of Theorem 2). -/
theorem condProb_bound_integrates_le [IsProbabilityMeasure μ] {m : MeasurableSpace Ω}
    (hm : m ≤ m0) {A B : Set Ω} (hA : MeasurableSet[m] A) (hB : MeasurableSet[m0] B) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hcond : ∀ᵐ ω ∂μ, ω ∈ A → (μ[B.indicator (fun _ => (1 : ℝ)) | m]) ω ≤ ε) :
    (μ (A ∩ B)).toReal ≤ ε := by
  have h := condProb_bound_integrates hm hA hB ε hcond
  have hA1 : (μ A).toReal ≤ 1 := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
  calc (μ (A ∩ B)).toReal ≤ ε * (μ A).toReal := h
    _ ≤ ε * 1 := by gcongr
    _ = ε := mul_one ε

/-- Item 1 in `ℝ≥0∞`: `μ (A ∩ B) ≤ ENNReal.ofReal ε * μ A`. -/
theorem condProb_bound_integrates_ennreal [IsProbabilityMeasure μ] {m : MeasurableSpace Ω}
    (hm : m ≤ m0) {A B : Set Ω} (hA : MeasurableSet[m] A) (hB : MeasurableSet[m0] B) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hcond : ∀ᵐ ω ∂μ, ω ∈ A → (μ[B.indicator (fun _ => (1 : ℝ)) | m]) ω ≤ ε) :
    μ (A ∩ B) ≤ ENNReal.ofReal ε * μ A := by
  have h := condProb_bound_integrates hm hA hB ε hcond
  calc μ (A ∩ B) = ENNReal.ofReal (μ (A ∩ B)).toReal := (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal (ε * (μ A).toReal) := ENNReal.ofReal_le_ofReal h
    _ = ENNReal.ofReal ε * ENNReal.ofReal (μ A).toReal := ENNReal.ofReal_mul hε
    _ = ENNReal.ofReal ε * μ A := by rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- Item 1 in `ℝ≥0∞` on a probability measure: `μ (A ∩ B) ≤ ENNReal.ofReal ε`. -/
theorem condProb_bound_integrates_ennreal_le [IsProbabilityMeasure μ] {m : MeasurableSpace Ω}
    (hm : m ≤ m0) {A B : Set Ω} (hA : MeasurableSet[m] A) (hB : MeasurableSet[m0] B) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hcond : ∀ᵐ ω ∂μ, ω ∈ A → (μ[B.indicator (fun _ => (1 : ℝ)) | m]) ω ≤ ε) :
    μ (A ∩ B) ≤ ENNReal.ofReal ε := by
  calc μ (A ∩ B) ≤ ENNReal.ofReal ε * μ A := condProb_bound_integrates_ennreal hm hA hB hε hcond
    _ ≤ ENNReal.ofReal ε * 1 := by gcongr; exact prob_le_one
    _ = ENNReal.ofReal ε := mul_one _

/-! ### The five events of Theorem 2 -/

/-- The good event of Theorem 2's proof: (a) holds, and none of (b), (c), (c′), (d) fails. -/
def goodEvent (A Bb Cc Cc' Bd : Set Ω) : Set Ω := A ∩ Bbᶜ ∩ Ccᶜ ∩ Cc'ᶜ ∩ Bdᶜ

/-- The five events in the form consumed by `Thm2Assembly.prob_not_mem_le`: the failures of (b) and
(d) are "taken within (a)". -/
def assemblyEvents (A Bb Cc Cc' Bd : Set Ω) : Fin 5 → Set Ω :=
  ![A, (A ∩ Bb)ᶜ, Ccᶜ, Cc'ᶜ, (A ∩ Bd)ᶜ]

/-- The intersection of the five assembly events is the good event. -/
theorem iInter_assemblyEvents (A Bb Cc Cc' Bd : Set Ω) :
    ⋂ i, assemblyEvents A Bb Cc Cc' Bd i = goodEvent A Bb Cc Cc' Bd := by
  ext ω
  simp only [assemblyEvents, goodEvent, Set.mem_iInter, Fin.forall_fin_succ, IsEmpty.forall_iff,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Set.mem_compl_iff, Set.mem_inter_iff, and_true]
  tauto

/-- **Required item 3.** Under the hypotheses of Theorem 2's proof, each of the five assembly events
fails with probability at most `e^{-t}`. -/
theorem five_events_for_assembly [IsProbabilityMeasure μ] {m : MeasurableSpace Ω} (hm : m ≤ m0)
    {A Bb Cc Cc' Bd : Set Ω} (hA : MeasurableSet[m] A) (hBb : MeasurableSet[m0] Bb)
    (hBd : MeasurableSet[m0] Bd) (t : ℝ)
    (ha : μ Aᶜ ≤ ENNReal.ofReal (Real.exp (-t)))
    (hb : ∀ᵐ ω ∂μ, ω ∈ A → (μ[Bb.indicator (fun _ => (1 : ℝ)) | m]) ω ≤ Real.exp (-t))
    (hc : μ Cc ≤ ENNReal.ofReal (Real.exp (-t)))
    (hc' : μ Cc' ≤ ENNReal.ofReal (Real.exp (-t)))
    (hd : ∀ᵐ ω ∂μ, ω ∈ A → (μ[Bd.indicator (fun _ => (1 : ℝ)) | m]) ω ≤ Real.exp (-t)) :
    ∀ i, μ (assemblyEvents A Bb Cc Cc' Bd i)ᶜ ≤ ENNReal.ofReal (Real.exp (-t)) := by
  have hε : 0 ≤ Real.exp (-t) := (Real.exp_pos _).le
  have hb' := condProb_bound_integrates_ennreal_le hm hA hBb hε hb
  have hd' := condProb_bound_integrates_ennreal_le hm hA hBd hε hd
  intro i
  fin_cases i <;> simp only [assemblyEvents, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
    Matrix.tail_cons, compl_compl, Fin.mk_one, Fin.isValue, Fin.reduceFinMk]
  · exact ha
  · exact hb'
  · exact hc
  · exact hc'
  · exact hd'

/-- **Required item 2.** `P(Gᶜ) ≤ 5 e^{-t}` for the good event `G`: the union bound over the five
assembly events (THEORY.md §4, proof of Theorem 2). -/
theorem five_events [IsProbabilityMeasure μ] {m : MeasurableSpace Ω} (hm : m ≤ m0)
    {A Bb Cc Cc' Bd : Set Ω} (hA : MeasurableSet[m] A) (hBb : MeasurableSet[m0] Bb)
    (hBd : MeasurableSet[m0] Bd) (t : ℝ)
    (ha : μ Aᶜ ≤ ENNReal.ofReal (Real.exp (-t)))
    (hb : ∀ᵐ ω ∂μ, ω ∈ A → (μ[Bb.indicator (fun _ => (1 : ℝ)) | m]) ω ≤ Real.exp (-t))
    (hc : μ Cc ≤ ENNReal.ofReal (Real.exp (-t)))
    (hc' : μ Cc' ≤ ENNReal.ofReal (Real.exp (-t)))
    (hd : ∀ᵐ ω ∂μ, ω ∈ A → (μ[Bd.indicator (fun _ => (1 : ℝ)) | m]) ω ≤ Real.exp (-t)) :
    μ (goodEvent A Bb Cc Cc' Bd)ᶜ ≤ 5 * ENNReal.ofReal (Real.exp (-t)) := by
  have hE := five_events_for_assembly hm hA hBb hBd t ha hb hc hc' hd
  rw [← iInter_assemblyEvents, Set.compl_iInter]
  calc μ (⋃ i, (assemblyEvents A Bb Cc Cc' Bd i)ᶜ)
      ≤ ∑ i, μ (assemblyEvents A Bb Cc Cc' Bd i)ᶜ := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _i : Fin 5, ENNReal.ofReal (Real.exp (-t)) := Finset.sum_le_sum (fun i _ => hE i)
    _ = 5 * ENNReal.ofReal (Real.exp (-t)) := by
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]

/-- Real-valued restatement of item 2: `P(Gᶜ) ≤ 5 e^{-t}`, hence `P(G) ≥ 1 - 5 e^{-t}`. -/
theorem five_events_real [IsProbabilityMeasure μ] {m : MeasurableSpace Ω} (hm : m ≤ m0)
    {A Bb Cc Cc' Bd : Set Ω} (hA : MeasurableSet[m] A) (hBb : MeasurableSet[m0] Bb)
    (hBd : MeasurableSet[m0] Bd) (t : ℝ)
    (ha : μ Aᶜ ≤ ENNReal.ofReal (Real.exp (-t)))
    (hb : ∀ᵐ ω ∂μ, ω ∈ A → (μ[Bb.indicator (fun _ => (1 : ℝ)) | m]) ω ≤ Real.exp (-t))
    (hc : μ Cc ≤ ENNReal.ofReal (Real.exp (-t)))
    (hc' : μ Cc' ≤ ENNReal.ofReal (Real.exp (-t)))
    (hd : ∀ᵐ ω ∂μ, ω ∈ A → (μ[Bd.indicator (fun _ => (1 : ℝ)) | m]) ω ≤ Real.exp (-t)) :
    (μ (goodEvent A Bb Cc Cc' Bd)ᶜ).toReal ≤ 5 * Real.exp (-t) := by
  have h := five_events hm hA hBb hBd t ha hb hc hc' hd
  have hfin : (5 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-t)) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top
  have h' := ENNReal.toReal_mono hfin h
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le, ENNReal.toReal_ofNat] at h'

end SymbolicIV.Thm2Conditioning

#print axioms SymbolicIV.Thm2Conditioning.condProb_bound_integrates
#print axioms SymbolicIV.Thm2Conditioning.condProb_bound_integrates_le
#print axioms SymbolicIV.Thm2Conditioning.condProb_bound_integrates_ennreal
#print axioms SymbolicIV.Thm2Conditioning.condProb_bound_integrates_ennreal_le
#print axioms SymbolicIV.Thm2Conditioning.iInter_assemblyEvents
#print axioms SymbolicIV.Thm2Conditioning.five_events_for_assembly
#print axioms SymbolicIV.Thm2Conditioning.five_events
#print axioms SymbolicIV.Thm2Conditioning.five_events_real
