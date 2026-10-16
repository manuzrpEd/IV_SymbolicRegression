import Mathlib

/-!
# Corollary 2.2, the algebra, and the tree-count arithmetic

Formalizes the pure real-number and counting steps of THEORY.md §4 (the derivation of
Corollary 2.2, "why a structure term") and §0, "How many trees" (the bound `log |S_L| ≤ L log(3m) + log 2` on
the number of trees). Unit U04 of `lean/FORMALIZATION_PLAN.md`.

Notation. `m` is the number of node labels, `L` the maximal tree size, `ℓ s` the size of tree `s`,
`t` the confidence level, `c := ρ (1 + ε_n(t))` (written as a single nonnegative real), `κ := κ_n`,
`w` the structure-penalty weight, `ℓ₀ := ℓ̄₀` the size of the largest minimal true tree, `k := k_s`,
`z := z_t`, `dloc := d^loc_{s,t_s}`, `ps p0 := p_s, p_0`. The tree-specific level is
`tLevel t L m ℓs := t + log L + ℓs · log (3m)` (the paper's `t_s`).

Results.
1. `sum_weights_le`, `weighted_union_bound`: the weights `(3m)^(-ℓ_s) / L` sum to at most one when
   `1 ≤ ℓ_s ≤ L` and there are at most `(3m)^k` trees of size `k`.
2. `exp_neg_tLevel`, `sum_exp_neg_tLevel_le`: `exp(-t_s) = exp(-t) (3m)^(-ℓ_s) / L`, hence
   `∑_s exp(-t_s) ≤ exp(-t)`.
3. `two_sqrt_mul_le`, `expand_II`: `2√(kt) ≤ k + t` and the expansion of the right side of (II).
4. `condition_II_of_cancel`: the cancellation of the size terms for
   `w ≥ 3 ρ(1+ε) log(3m)/log m`, giving (II) at the tree-specific level for every `ℓ_s ≥ 0`.
5. `geom_sum_le_two_mul_pow`, `tree_count_sum_le`, `log_tree_count_le`: `∑_{k ≤ L} a^k ≤ 2 a^L` for
   `a ≥ 2`, and `log (∑_{k ≤ L} (3m)^k) ≤ L log(3m) + log 2`; `log_card_le` applies this to a finite
   set of trees with the fiber bound of item 1.

Hypotheses added beyond the paper's text (all implicit there):
- `1 ≤ m` (so that `3m ≥ 2 > 0`, `log(3m) ≥ 0`, and the weights are positive); item 4 uses `2 ≤ m`,
  which the paper does not state in so many words but uses (step 3 divides by `log m`; the alphabet
  has `m = 10` labels, and any alphabet with a binary operator and a variable has `m ≥ 2`).
- `1 ≤ L` wherever `log L` appears (so that `log L ≥ 0` and `exp(-log L) = 1/L`); item 1 does not
  need it.
- `0 ≤ k`, `0 ≤ t` and `0 ≤ ρ(1+ε)` for the AM–GM step `2√(k t_s) ≤ k + t_s` and for multiplying
  by `ρ(1+ε)`; these are the paper's standing sign conventions (`k_s` is a dimension, `t > 0`,
  `ρ > 0`, `ε_n(t) > 0`).
- `0 ≤ ℓ_s` in item 4, as the plan asks (the paper's `ℓ_s` is a positive integer).
No hypothesis is weakened and no conclusion strengthened relative to those two passages.
-/

namespace SymbolicIV.Cor22

open Finset Real

/-! ### 1. Weighted union bound -/

/-- The unnormalized weights `(3m)^(-ℓ_s)` sum to at most `L` when every size lies in `[1, L]` and
there are at most `(3m)^k` trees of size `k`. -/
theorem sum_weights_le {S : Type*} [Fintype S] (ℓ : S → ℕ) (L m : ℕ) (hm : 1 ≤ m)
    (hℓ : ∀ s, 1 ≤ ℓ s ∧ ℓ s ≤ L)
    (hcount : ∀ k, (({s ∈ (univ : Finset S) | ℓ s = k}).card : ℝ) ≤ (3 * (m : ℝ)) ^ k) :
    ∑ s, (3 * (m : ℝ)) ^ (-(ℓ s : ℤ)) ≤ L := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hpos : (0 : ℝ) < 3 * m := by linarith
  calc ∑ s, (3 * (m : ℝ)) ^ (-(ℓ s : ℤ))
      = ∑ k ∈ Icc 1 L, ∑ s ∈ (univ : Finset S) with ℓ s = k, (3 * (m : ℝ)) ^ (-(k : ℤ)) :=
        (Finset.sum_fiberwise_of_maps_to' (t := Finset.Icc 1 L) (g := ℓ)
          (fun s _ => by simpa [Finset.mem_Icc] using hℓ s)
          (fun k : ℕ => (3 * (m : ℝ)) ^ (-(k : ℤ)))).symm
    _ = ∑ k ∈ Icc 1 L, (({s ∈ (univ : Finset S) | ℓ s = k}).card : ℝ) * (3 * (m : ℝ)) ^ (-(k : ℤ)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ k ∈ Icc 1 L, (1 : ℝ) := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [zpow_neg, zpow_natCast]
        have hk : (0 : ℝ) < (3 * (m : ℝ)) ^ k := pow_pos hpos k
        calc (({s ∈ (univ : Finset S) | ℓ s = k}).card : ℝ) * ((3 * (m : ℝ)) ^ k)⁻¹
            ≤ (3 * (m : ℝ)) ^ k * ((3 * (m : ℝ)) ^ k)⁻¹ :=
              mul_le_mul_of_nonneg_right (hcount k) (inv_nonneg.2 hk.le)
          _ = 1 := mul_inv_cancel₀ hk.ne'
    _ = L := by simp

/-- Item 1: the weights `(3m)^(-ℓ_s) / L` sum to at most one. -/
theorem weighted_union_bound {S : Type*} [Fintype S] (ℓ : S → ℕ) (L m : ℕ) (hm : 1 ≤ m)
    (hℓ : ∀ s, 1 ≤ ℓ s ∧ ℓ s ≤ L)
    (hcount : ∀ k, (({s ∈ (univ : Finset S) | ℓ s = k}).card : ℝ) ≤ (3 * (m : ℝ)) ^ k) :
    ∑ s, (3 * (m : ℝ)) ^ (-(ℓ s : ℤ)) / L ≤ 1 := by
  rw [← Finset.sum_div]
  exact div_le_one_of_le₀ (sum_weights_le ℓ L m hm hℓ hcount) (Nat.cast_nonneg L)

/-! ### 2. The tree-specific level `t_s` -/

/-- `t_s := t + log L + ℓ_s log(3m)`. -/
noncomputable def tLevel (t : ℝ) (L m : ℕ) (ℓs : ℝ) : ℝ :=
  t + Real.log L + ℓs * Real.log (3 * m)

/-- Item 2, the identity `exp(-t_s) = exp(-t) (3m)^(-ℓ_s) / L`. -/
theorem exp_neg_tLevel (t : ℝ) (L m : ℕ) (hL : 1 ≤ L) (hm : 1 ≤ m) (ℓs : ℕ) :
    Real.exp (-(tLevel t L m ℓs)) = Real.exp (-t) * (3 * (m : ℝ)) ^ (-(ℓs : ℤ)) / L := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hpos : (0 : ℝ) < 3 * m := by linarith
  unfold tLevel
  rw [neg_add, neg_add, Real.exp_add, Real.exp_add, Real.exp_neg (Real.log L), Real.exp_log hL',
    Real.exp_neg (ℓs * Real.log (3 * m)), Real.exp_nat_mul, Real.exp_log hpos, zpow_neg,
    zpow_natCast]
  ring

/-- Item 2, the consequence: `∑_s exp(-t_s) ≤ exp(-t)`. -/
theorem sum_exp_neg_tLevel_le {S : Type*} [Fintype S] (ℓ : S → ℕ) (t : ℝ) (L m : ℕ)
    (hL : 1 ≤ L) (hm : 1 ≤ m) (hℓ : ∀ s, 1 ≤ ℓ s ∧ ℓ s ≤ L)
    (hcount : ∀ k, (({s ∈ (univ : Finset S) | ℓ s = k}).card : ℝ) ≤ (3 * (m : ℝ)) ^ k) :
    ∑ s, Real.exp (-(tLevel t L m (ℓ s))) ≤ Real.exp (-t) := by
  calc ∑ s, Real.exp (-(tLevel t L m (ℓ s)))
      = Real.exp (-t) * ∑ s, (3 * (m : ℝ)) ^ (-(ℓ s : ℤ)) / L := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [exp_neg_tLevel t L m hL hm (ℓ s), mul_div_assoc]
    _ ≤ Real.exp (-t) * 1 :=
        mul_le_mul_of_nonneg_left (weighted_union_bound ℓ L m hm hℓ hcount) (Real.exp_pos _).le
    _ = Real.exp (-t) := mul_one _

/-! ### 3. Expanding condition (II) -/

/-- AM–GM in the form `2√(kt) ≤ k + t`. -/
theorem two_sqrt_mul_le (k t : ℝ) (hk : 0 ≤ k) (ht : 0 ≤ t) :
    2 * Real.sqrt (k * t) ≤ k + t := by
  rw [Real.sqrt_mul hk]
  nlinarith [Real.sq_sqrt hk, Real.sq_sqrt ht, sq_nonneg (Real.sqrt k - Real.sqrt t)]

/-- `t_s ≥ 0` when `t ≥ 0`, `L ≥ 1`, `m ≥ 1` and `ℓ_s ≥ 0`. -/
theorem tLevel_nonneg (t : ℝ) (L m : ℕ) (hL : 1 ≤ L) (hm : 1 ≤ m) (ℓs : ℝ) (ht : 0 ≤ t)
    (hℓs : 0 ≤ ℓs) : 0 ≤ tLevel t L m ℓs := by
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hm' : (1 : ℝ) ≤ 3 * (m : ℝ) := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  unfold tLevel
  have := Real.log_nonneg hL'
  have := Real.log_nonneg hm'
  positivity

/-- Item 3: with `c := ρ(1+ε) ≥ 0`, the right side of (II) at level `t_s` is at most
`c (2k + 3t + 3 log L) + 3 c ℓ_s log(3m)`. -/
theorem expand_II (c k t : ℝ) (L m : ℕ) (hL : 1 ≤ L) (hm : 1 ≤ m) (ℓs : ℝ)
    (hc : 0 ≤ c) (hk : 0 ≤ k) (ht : 0 ≤ t) (hℓs : 0 ≤ ℓs) :
    c * (k + 2 * Real.sqrt (k * tLevel t L m ℓs) + 2 * tLevel t L m ℓs)
      ≤ c * (2 * k + 3 * t + 3 * Real.log L) + 3 * c * ℓs * Real.log (3 * m) := by
  have hts := tLevel_nonneg t L m hL hm ℓs ht hℓs
  have h1 := two_sqrt_mul_le k _ hk hts
  have h2 : c * (k + 2 * Real.sqrt (k * tLevel t L m ℓs) + 2 * tLevel t L m ℓs)
      ≤ c * (2 * k + 3 * tLevel t L m ℓs) :=
    mul_le_mul_of_nonneg_left (by linarith) hc
  unfold tLevel at h2 ⊢
  linarith

/-! ### 4. Cancelling the size terms -/

/-- Item 4: for `m ≥ 2`, `w ≥ 3 ρ(1+ε) log(3m) / log m` and the size-free gap condition, condition
(II) holds at the tree-specific level `t_s` for every `ℓ_s ≥ 0`. -/
theorem condition_II_of_cancel (c κ w ℓ₀ k t z dloc ps p0 : ℝ) (L m : ℕ) (hL : 1 ≤ L) (hm : 2 ≤ m)
    (hc : 0 ≤ c) (hk : 0 ≤ k) (ht : 0 ≤ t)
    (hw : w ≥ 3 * c * Real.log (3 * m) / Real.log m)
    (hgap : (ps - p0) * κ
      > w * ℓ₀ * Real.log m + c * (2 * k + 3 * t + 3 * Real.log L) + 2 * z * dloc)
    (ℓs : ℝ) (hℓs : 0 ≤ ℓs) :
    (ps - p0) * κ + w * (ℓs - ℓ₀) * Real.log m
      > c * (k + 2 * Real.sqrt (k * tLevel t L m ℓs) + 2 * tLevel t L m ℓs) + 2 * z * dloc := by
  have hm1 : (1 : ℝ) < m := by exact_mod_cast hm
  have hlogm : 0 < Real.log m := Real.log_pos hm1
  have hw' : 3 * c * Real.log (3 * m) ≤ w * Real.log m := by
    rwa [ge_iff_le, div_le_iff₀ hlogm] at hw
  have h3 := expand_II c k t L m hL (by omega) ℓs hc hk ht hℓs
  have h4 := mul_le_mul_of_nonneg_left hw' hℓs
  nlinarith [h3, h4, hgap]

/-! ### 5. The tree count -/

/-- `∑_{k=0}^{L} a^k ≤ 2 a^L` for `a ≥ 2`. -/
theorem geom_sum_le_two_mul_pow (a : ℝ) (ha : 2 ≤ a) (L : ℕ) :
    ∑ k ∈ range (L + 1), a ^ k ≤ 2 * a ^ L := by
  induction L with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have ha0 : 0 ≤ a ^ n := pow_nonneg (by linarith) n
    have : 2 * a ^ n ≤ a ^ (n + 1) := by rw [pow_succ]; nlinarith
    linarith

/-- Item 5, first half: `∑_{k=0}^{L} (3m)^k ≤ 2 (3m)^L` for `m ≥ 1`. -/
theorem tree_count_sum_le (m L : ℕ) (hm : 1 ≤ m) :
    ∑ k ∈ range (L + 1), (3 * (m : ℝ)) ^ k ≤ 2 * (3 * (m : ℝ)) ^ L := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  exact geom_sum_le_two_mul_pow _ (by linarith) L

/-- Item 5, second half: `log (∑_{k=0}^{L} (3m)^k) ≤ L log(3m) + log 2`. -/
theorem log_tree_count_le (m L : ℕ) (hm : 1 ≤ m) :
    Real.log (∑ k ∈ range (L + 1), (3 * (m : ℝ)) ^ k) ≤ L * Real.log (3 * m) + Real.log 2 := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hpos : (0 : ℝ) < 3 * m := by linarith
  have hsum : (0 : ℝ) < ∑ k ∈ range (L + 1), (3 * (m : ℝ)) ^ k :=
    Finset.sum_pos (fun k _ => pow_pos hpos k) (Finset.nonempty_range_iff.2 (Nat.succ_ne_zero L))
  calc Real.log (∑ k ∈ range (L + 1), (3 * (m : ℝ)) ^ k)
      ≤ Real.log (2 * (3 * (m : ℝ)) ^ L) := Real.log_le_log hsum (tree_count_sum_le m L hm)
    _ = L * Real.log (3 * m) + Real.log 2 := by
        rw [Real.log_mul (by norm_num) (pow_pos hpos L).ne', Real.log_pow]; ring

/-- The tree count as the paper states it (§0): a finite set of trees with sizes in
`[1, L]` and at most `(3m)^k` trees of size `k` has at most `∑_{k=0}^{L} (3m)^k ≤ 2 (3m)^L`
elements, hence `log |S_L| ≤ L log(3m) + log 2` (when the set is nonempty). -/
theorem card_le_tree_count {S : Type*} [Fintype S] (ℓ : S → ℕ) (L m : ℕ)
    (hℓ : ∀ s, 1 ≤ ℓ s ∧ ℓ s ≤ L)
    (hcount : ∀ k, (({s ∈ (univ : Finset S) | ℓ s = k}).card : ℝ) ≤ (3 * (m : ℝ)) ^ k) :
    (Fintype.card S : ℝ) ≤ ∑ k ∈ range (L + 1), (3 * (m : ℝ)) ^ k := by
  have h1 : (Fintype.card S : ℝ) = ∑ k ∈ Icc 1 L, (({s ∈ (univ : Finset S) | ℓ s = k}).card : ℝ) := by
    calc (Fintype.card S : ℝ) = ∑ s : S, (1 : ℝ) := by simp
      _ = ∑ k ∈ Icc 1 L, ∑ s ∈ (univ : Finset S) with ℓ s = k, (1 : ℝ) :=
        (Finset.sum_fiberwise_of_maps_to' (t := Finset.Icc 1 L) (g := ℓ)
          (fun s _ => by simpa [Finset.mem_Icc] using hℓ s) (fun _ : ℕ => (1 : ℝ))).symm
      _ = ∑ k ∈ Icc 1 L, (({s ∈ (univ : Finset S) | ℓ s = k}).card : ℝ) := by simp
  rw [h1]
  calc ∑ k ∈ Icc 1 L, (({s ∈ (univ : Finset S) | ℓ s = k}).card : ℝ)
      ≤ ∑ k ∈ Icc 1 L, (3 * (m : ℝ)) ^ k := Finset.sum_le_sum fun k _ => hcount k
    _ ≤ ∑ k ∈ range (L + 1), (3 * (m : ℝ)) ^ k := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun k _ _ => by positivity
        intro k hk
        simp only [Finset.mem_Icc] at hk
        simp only [Finset.mem_range]
        omega

theorem log_card_le {S : Type*} [Fintype S] [Nonempty S] (ℓ : S → ℕ) (L m : ℕ) (hm : 1 ≤ m)
    (hℓ : ∀ s, 1 ≤ ℓ s ∧ ℓ s ≤ L)
    (hcount : ∀ k, (({s ∈ (univ : Finset S) | ℓ s = k}).card : ℝ) ≤ (3 * (m : ℝ)) ^ k) :
    Real.log (Fintype.card S) ≤ L * Real.log (3 * m) + Real.log 2 := by
  have hpos : (0 : ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
  exact (Real.log_le_log hpos (card_le_tree_count ℓ L m hℓ hcount)).trans (log_tree_count_le m L hm)

end SymbolicIV.Cor22

#print axioms SymbolicIV.Cor22.weighted_union_bound
#print axioms SymbolicIV.Cor22.sum_exp_neg_tLevel_le
#print axioms SymbolicIV.Cor22.expand_II
#print axioms SymbolicIV.Cor22.condition_II_of_cancel
#print axioms SymbolicIV.Cor22.log_tree_count_le
#print axioms SymbolicIV.Cor22.log_card_le
