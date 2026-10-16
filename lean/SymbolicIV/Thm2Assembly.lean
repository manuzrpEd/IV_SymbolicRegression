import Mathlib

/-!
# Theorem 2, assembly of the five events (THEORY.md §4)

This file formalizes the *assembly* step of Theorem 2: given the five concentration events of
Lemma 3 (each failing with probability at most `e^{-t}`) and the conclusion that Proposition 2.1
delivers on their intersection (every tree outside `S₀ᵐⁱⁿ` has a strictly larger criterion than
every minimal true tree), the selected tree `ŝ` is minimal and true whenever the candidate set
meets `S₀ᵐⁱⁿ`, and

  `P(ŝ ∉ S₀ᵐⁱⁿ) ≤ 5 e^{-t} + P(Ŝ ∩ S₀ᵐⁱⁿ = ∅)`.

It also formalizes the tree-specific union bound used for the events (c), (c′), (d) of the proof
(`P(B s) ≤ e^{-t_s}` and `∑ s, e^{-t_s} ≤ e^{-t}` give `P(⋃ s, B s) ≤ e^{-t}`), and the full
assembly with tree-specific levels (last paragraph of the proof).

## Setting (abstract, as in FORMALIZATION_PLAN.md, unit U03)

* `Ω` a measurable space with a measure `P` (a probability measure where the paper's
  "probability at least `1 - 5e^{-t}`" is restated, otherwise any measure);
* `S` a finite type of trees, `Smin : Set S` the minimal true trees;
* `Shat ω : Finset S` the candidate set produced by the search at sample `ω` (it may depend on
  the data), `shat ω` the selected tree, `crit ω s` the criterion `crit_n(s)`;
* `A i`, `i : Fin 5`, the five events, with `P (A i)ᶜ ≤ e^{-t}`;
* `hsep`: on `⋂ i, A i`, every `s ∉ Smin` and every `s' ∈ Smin` satisfy `crit ω s' < crit ω s`
  (this is what Proposition 2.1 gives under (I) or (II); it is the input of this unit, not re-proved
  here).

## Hypotheses added beyond the paper's statement

* `hmem : ∀ ω, (Shat ω).Nonempty → shat ω ∈ Shat ω` and
  `hmin : ∀ ω, ∀ s ∈ Shat ω, crit ω (shat ω) ≤ crit ω s`: the paper's "ŝ := argmin over Ŝ".
  Nothing is assumed about `shat ω` when `Shat ω` is empty (the paper leaves it undefined there);
  such `ω` fall in the search-failure event.
* Probabilities are written in `ℝ≥0∞` as `ENNReal.ofReal (Real.exp (-t))`; a real-valued
  restatement (`P.real`) is given for a finite measure.
* No measurability of the events, of `shat`, or of `Shat` is needed for the main bound (outer-measure
  monotonicity and subadditivity suffice). The only place where measurability is used is the
  restatement `P (⋂ i, A i) ≥ 1 - 5 e^{-t}` (`inter_prob_ge`), which needs `MeasurableSet (A i)`
  and a probability measure, exactly as the paper's phrase "an event of probability at least …"
  presupposes.

No hypothesis of the paper was weakened and no conclusion was strengthened.
-/

open MeasureTheory

namespace SymbolicIV.Thm2Assembly

variable {Ω : Type*} [MeasurableSpace Ω] {S : Type*} [Fintype S]

omit [MeasurableSpace Ω] [Fintype S] in
/-- **Required item 1.** On the intersection of the events, if the candidate set contains a
minimal true tree, the selected tree is minimal and true. This is the sentence
"So every `s ∉ S₀ᵐⁱⁿ` has `crit_n(s) > crit_n(s*)`. Because the bounds are uniform over `S_L`, this
holds whichever candidate set the search produced" (THEORY.md §4, proof of Theorem 2). The index type of the
events is arbitrary here. -/
theorem selected_mem_of_inter
    (Smin : Set S) (Shat : Ω → Finset S) (shat : Ω → S) (crit : Ω → S → ℝ)
    {ι : Type*} (A : ι → Set Ω)
    (hmem : ∀ ω, (Shat ω).Nonempty → shat ω ∈ Shat ω)
    (hmin : ∀ ω, ∀ s ∈ Shat ω, crit ω (shat ω) ≤ crit ω s)
    (hsep : ∀ ω ∈ ⋂ i, A i, ∀ s, s ∉ Smin → ∀ s' ∈ Smin, crit ω s' < crit ω s)
    (ω : Ω) (hω : ω ∈ ⋂ i, A i) (hne : ((Shat ω : Set S) ∩ Smin).Nonempty) :
    shat ω ∈ Smin := by
  obtain ⟨s', hs'S, hs'min⟩ := hne
  have hs'S' : s' ∈ Shat ω := by simpa using hs'S
  have _ := hmem ω ⟨s', hs'S'⟩
  by_contra h
  have h1 := hsep ω hω (shat ω) h s' hs'min
  have h2 := hmin ω s' hs'S'
  linarith

omit [MeasurableSpace Ω] [Fintype S] in
/-- The event inclusion behind the bound: if the selected tree is not minimal and true, then either
one of the five events failed or the candidate set missed `Smin`. -/
theorem not_mem_subset
    (Smin : Set S) (Shat : Ω → Finset S) (shat : Ω → S) (crit : Ω → S → ℝ)
    {ι : Type*} (A : ι → Set Ω)
    (hmem : ∀ ω, (Shat ω).Nonempty → shat ω ∈ Shat ω)
    (hmin : ∀ ω, ∀ s ∈ Shat ω, crit ω (shat ω) ≤ crit ω s)
    (hsep : ∀ ω ∈ ⋂ i, A i, ∀ s, s ∉ Smin → ∀ s' ∈ Smin, crit ω s' < crit ω s) :
    {ω | shat ω ∉ Smin} ⊆ (⋃ i, (A i)ᶜ) ∪ {ω | (Shat ω : Set S) ∩ Smin = ∅} := by
  intro ω hω
  by_cases hΩ : ω ∈ ⋂ i, A i
  · right
    by_contra hne
    exact hω (selected_mem_of_inter Smin Shat shat crit A hmem hmin hsep ω hΩ
      (Set.nonempty_iff_ne_empty.mpr hne))
  · left
    rw [← Set.compl_iInter]
    exact hΩ

/-- Five failure probabilities of at most `e^{-t}` each sum to at most `5 e^{-t}`. -/
theorem sum_five_le (P : Measure Ω) (A : Fin 5 → Set Ω) (t : ℝ)
    (hA : ∀ i, P (A i)ᶜ ≤ ENNReal.ofReal (Real.exp (-t))) :
    P (⋃ i, (A i)ᶜ) ≤ 5 * ENNReal.ofReal (Real.exp (-t)) := by
  calc P (⋃ i, (A i)ᶜ) ≤ ∑ i, P (A i)ᶜ := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _i : Fin 5, ENNReal.ofReal (Real.exp (-t)) := Finset.sum_le_sum (fun i _ => hA i)
    _ = 5 * ENNReal.ofReal (Real.exp (-t)) := by
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]

omit [Fintype S] in
/-- **Required item 2.** The bound of Theorem 2 (THEORY.md §4):
`P(ŝ ∉ S₀ᵐⁱⁿ) ≤ 5 e^{-t} + P(Ŝ ∩ S₀ᵐⁱⁿ = ∅)`. -/
theorem prob_not_mem_le (P : Measure Ω)
    (Smin : Set S) (Shat : Ω → Finset S) (shat : Ω → S) (crit : Ω → S → ℝ)
    (A : Fin 5 → Set Ω) (t : ℝ)
    (hA : ∀ i, P (A i)ᶜ ≤ ENNReal.ofReal (Real.exp (-t)))
    (hmem : ∀ ω, (Shat ω).Nonempty → shat ω ∈ Shat ω)
    (hmin : ∀ ω, ∀ s ∈ Shat ω, crit ω (shat ω) ≤ crit ω s)
    (hsep : ∀ ω ∈ ⋂ i, A i, ∀ s, s ∉ Smin → ∀ s' ∈ Smin, crit ω s' < crit ω s) :
    P {ω | shat ω ∉ Smin}
      ≤ 5 * ENNReal.ofReal (Real.exp (-t)) + P {ω | (Shat ω : Set S) ∩ Smin = ∅} := by
  calc P {ω | shat ω ∉ Smin}
      ≤ P ((⋃ i, (A i)ᶜ) ∪ {ω | (Shat ω : Set S) ∩ Smin = ∅}) :=
        measure_mono (not_mem_subset Smin Shat shat crit A hmem hmin hsep)
    _ ≤ P (⋃ i, (A i)ᶜ) + P {ω | (Shat ω : Set S) ∩ Smin = ∅} := measure_union_le _ _
    _ ≤ 5 * ENNReal.ofReal (Real.exp (-t)) + P {ω | (Shat ω : Set S) ∩ Smin = ∅} := by
        gcongr
        exact sum_five_le P A t hA

omit [Fintype S] in
/-- Real-valued restatement of item 2 for a finite measure. -/
theorem prob_not_mem_le_real (P : Measure Ω) [IsFiniteMeasure P]
    (Smin : Set S) (Shat : Ω → Finset S) (shat : Ω → S) (crit : Ω → S → ℝ)
    (A : Fin 5 → Set Ω) (t : ℝ)
    (hA : ∀ i, P (A i)ᶜ ≤ ENNReal.ofReal (Real.exp (-t)))
    (hmem : ∀ ω, (Shat ω).Nonempty → shat ω ∈ Shat ω)
    (hmin : ∀ ω, ∀ s ∈ Shat ω, crit ω (shat ω) ≤ crit ω s)
    (hsep : ∀ ω ∈ ⋂ i, A i, ∀ s, s ∉ Smin → ∀ s' ∈ Smin, crit ω s' < crit ω s) :
    P.real {ω | shat ω ∉ Smin}
      ≤ 5 * Real.exp (-t) + P.real {ω | (Shat ω : Set S) ∩ Smin = ∅} := by
  have h := prob_not_mem_le P Smin Shat shat crit A t hA hmem hmin hsep
  have hfin : 5 * ENNReal.ofReal (Real.exp (-t)) + P {ω | (Shat ω : Set S) ∩ Smin = ∅} ≠ ⊤ := by
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top,
      measure_ne_top _ _⟩
  have h' := ENNReal.toReal_mono hfin h
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top) (measure_ne_top _ _),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] at h'
  simpa [Measure.real] using h'

/-- The paper's phrase "an event of probability at least `1 - 5e^{-t}`": with measurable events and
a probability measure, `P (⋂ i, A i) ≥ 1 - 5 e^{-t}`. -/
theorem inter_prob_ge (P : Measure Ω) [IsProbabilityMeasure P] (A : Fin 5 → Set Ω) (t : ℝ)
    (hAm : ∀ i, MeasurableSet (A i))
    (hA : ∀ i, P (A i)ᶜ ≤ ENNReal.ofReal (Real.exp (-t))) :
    1 - 5 * ENNReal.ofReal (Real.exp (-t)) ≤ P (⋂ i, A i) := by
  have hm : MeasurableSet (⋂ i, A i) := MeasurableSet.iInter hAm
  have hc : P (⋂ i, A i)ᶜ ≤ 5 * ENNReal.ofReal (Real.exp (-t)) := by
    rw [Set.compl_iInter]
    exact sum_five_le P A t hA
  have h1 : P (⋂ i, A i) = 1 - P (⋂ i, A i)ᶜ := by
    rw [prob_compl_eq_one_sub hm, ENNReal.sub_sub_cancel ENNReal.one_ne_top prob_le_one]
  rw [h1]
  exact tsub_le_tsub_left hc _

/-- **Required item 3.** The tree-specific union bound (THEORY.md §4, proof of Theorem 2): events
`B s` with `P (B s) ≤ e^{-t_s}` and `∑ s, e^{-t_s} ≤ e^{-t}` give `P (⋃ s, B s) ≤ e^{-t}`. -/
theorem union_bound_tree_specific (P : Measure Ω) (B : S → Set Ω) (ts : S → ℝ) (t : ℝ)
    (hB : ∀ s, P (B s) ≤ ENNReal.ofReal (Real.exp (-(ts s))))
    (hsum : ∑ s, Real.exp (-(ts s)) ≤ Real.exp (-t)) :
    P (⋃ s, B s) ≤ ENNReal.ofReal (Real.exp (-t)) := by
  calc P (⋃ s, B s) ≤ ∑ s, P (B s) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ s, ENNReal.ofReal (Real.exp (-(ts s))) := Finset.sum_le_sum (fun s _ => hB s)
    _ = ENNReal.ofReal (∑ s, Real.exp (-(ts s))) :=
        (ENNReal.ofReal_sum_of_nonneg (fun s _ => (Real.exp_pos _).le)).symm
    _ ≤ ENNReal.ofReal (Real.exp (-t)) := ENNReal.ofReal_le_ofReal hsum

/-- The common level `t_L := t + log |S_L|` of the paper satisfies `∑ s, e^{-t_L} ≤ e^{-t}`
(with equality), so it is a special case of the tree-specific levels. -/
theorem sum_exp_common_level [Nonempty S] (t : ℝ) :
    ∑ _s : S, Real.exp (-(t + Real.log (Fintype.card S))) ≤ Real.exp (-t) := by
  have hcard : (0 : ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
  have hexp : Real.exp (-(t + Real.log (Fintype.card S))) = Real.exp (-t) / Fintype.card S := by
    rw [neg_add, Real.exp_add, Real.exp_neg (Real.log _), Real.exp_log hcard, div_eq_mul_inv]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hexp, mul_div_assoc', mul_comm,
    mul_div_assoc, div_self hcard.ne', mul_one]

/-- **Theorem 2 with tree-specific levels** (THEORY.md §4, last sentences of the proof of Theorem 2): each of the five
events is an intersection over trees of per-tree events `G i s` whose failure probability is at most
`e^{-t_{i,s}}`, with `∑ s, e^{-t_{i,s}} ≤ e^{-t}` for each `i`. (An event that is not tree-specific,
such as (a) or (b), is recovered with `G i s := A i` for all `s` and `t_{i,s} := t + log |S|`, by
`sum_exp_common_level`.) -/
theorem prob_not_mem_le_tree_specific (P : Measure Ω)
    (Smin : Set S) (Shat : Ω → Finset S) (shat : Ω → S) (crit : Ω → S → ℝ)
    (G : Fin 5 → S → Set Ω) (ts : Fin 5 → S → ℝ) (t : ℝ)
    (hG : ∀ i s, P (G i s)ᶜ ≤ ENNReal.ofReal (Real.exp (-(ts i s))))
    (hsum : ∀ i, ∑ s, Real.exp (-(ts i s)) ≤ Real.exp (-t))
    (hmem : ∀ ω, (Shat ω).Nonempty → shat ω ∈ Shat ω)
    (hmin : ∀ ω, ∀ s ∈ Shat ω, crit ω (shat ω) ≤ crit ω s)
    (hsep : ∀ ω ∈ ⋂ i, ⋂ s, G i s, ∀ s, s ∉ Smin → ∀ s' ∈ Smin, crit ω s' < crit ω s) :
    P {ω | shat ω ∉ Smin}
      ≤ 5 * ENNReal.ofReal (Real.exp (-t)) + P {ω | (Shat ω : Set S) ∩ Smin = ∅} := by
  refine prob_not_mem_le P Smin Shat shat crit (fun i => ⋂ s, G i s) t ?_ hmem hmin hsep
  intro i
  rw [Set.compl_iInter]
  exact union_bound_tree_specific P (fun s => (G i s)ᶜ) (ts i) t (hG i) (hsum i)

end SymbolicIV.Thm2Assembly

#print axioms SymbolicIV.Thm2Assembly.selected_mem_of_inter
#print axioms SymbolicIV.Thm2Assembly.prob_not_mem_le
#print axioms SymbolicIV.Thm2Assembly.prob_not_mem_le_real
#print axioms SymbolicIV.Thm2Assembly.inter_prob_ge
#print axioms SymbolicIV.Thm2Assembly.union_bound_tree_specific
#print axioms SymbolicIV.Thm2Assembly.prob_not_mem_le_tree_specific
