import Mathlib

/-!
# The tree count: at most `(3m)^ℓ` trees of size `ℓ` (THEORY.md §0)

Formalized: the counting bound of THEORY.md "How many trees" (paper: the formula class
`𝒮_L` and `log|𝒮_L| ≤ L log(3m) + log 2`), unit U12 of `FORMALIZATION_PLAN.md`.

## Modelling

* `ExprTree m` is the inductive type of expression trees over an alphabet of `m` labels: a leaf
  (one label), a unary node (one label, one child) or a binary node (one label, two children).
  Labels are not matched to arities, so this is exactly the overcount the paper describes
  ("labels must match arities" is ignored). The paper's trees over an alphabet of `m` symbols
  form a subset of `ExprTree m`, so every bound below applies to them.
* `size t` is the number of nodes (`ℓ_s`).
* `word t` is the preorder sequence of (arity, label) pairs, a Łukasiewicz word in
  `List (Fin 3 × Fin m)`; it has length `size t` and determines `t` (`word_injective`), which is
  the injection of the plan into `Fin ℓ → Fin 3 × Fin m` (`codeFin`, `codeFin_injective`).

## Results

* `finite_size_eq`: trees of size `ℓ` form a finite type.
* `card_size_eq_le`: `#{t : size t = ℓ} ≤ (3m)^ℓ`.
* `card_size_le_le_sum`: `#{t : size t ≤ L} ≤ ∑_{k ≤ L} (3m)^k`.
* `geom_sum_le_two_mul_pow`: `∑_{k ≤ L} q^k ≤ 2 q^L` for `q ≥ 2`.
* `card_size_le_le`: `#{t : size t ≤ L} ≤ 2 (3m)^L`. The paper states this for `3m ≥ 2`; here no
  hypothesis on `m` is needed, since for `m = 0` there are no trees at all.
* `log_card_size_le_le`: `log #{t : size t ≤ L} ≤ L log(3m) + log 2`, the form the paper uses
  (with the convention `Real.log 0 = 0` of Mathlib, which makes the statement true also when the
  class is empty).

## Hypotheses added beyond the paper

None. The sharper Motzkin bound (stretch goal) is not formalized; the paper only uses `3^ℓ`.

## Discrepancies found

None. The count is an overcount, exactly as the paper says.
-/

namespace SymbolicIV.TreeCount

/-- Expression trees over an alphabet of `m` labels: a leaf, a unary node or a binary node, each
carrying one label. Arities and labels are not matched (the paper's overcount). -/
inductive ExprTree (m : ℕ) : Type
  | leaf (a : Fin m) : ExprTree m
  | unary (a : Fin m) (t : ExprTree m) : ExprTree m
  | binary (a : Fin m) (t u : ExprTree m) : ExprTree m

namespace ExprTree

variable {m : ℕ}

/-- Number of nodes. -/
def size : ExprTree m → ℕ
  | leaf _ => 1
  | unary _ t => t.size + 1
  | binary _ t u => t.size + u.size + 1

/-- Preorder sequence of (arity, label) pairs: the Łukasiewicz word of the tree. -/
def word : ExprTree m → List (Fin 3 × Fin m)
  | leaf a => [(0, a)]
  | unary a t => (1, a) :: t.word
  | binary a t u => (2, a) :: (t.word ++ u.word)

theorem length_word (t : ExprTree m) : t.word.length = t.size := by
  induction t with
  | leaf a => simp [word, size]
  | unary a t ih => simp [word, size, ih]
  | binary a t u iht ihu => simp [word, size, iht, ihu]

/-- Prefix-freeness: a Łukasiewicz word followed by anything determines the tree and the rest. -/
theorem word_append_inj (t : ExprTree m) :
    ∀ (t' : ExprTree m) (l l' : List (Fin 3 × Fin m)),
      t.word ++ l = t'.word ++ l' → t = t' ∧ l = l' := by
  induction t with
  | leaf a =>
    intro t' l l' h
    cases t' with
    | leaf b =>
      simp only [word, List.cons_append, List.nil_append, List.cons.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨-, rfl⟩, rfl⟩ := h
      exact ⟨rfl, rfl⟩
    | unary b t' =>
      simp only [word, List.cons_append, List.nil_append, List.cons.injEq, Prod.mk.injEq] at h
      exact absurd h.1.1 (by decide)
    | binary b t' u' =>
      simp only [word, List.cons_append, List.nil_append, List.cons.injEq, Prod.mk.injEq] at h
      exact absurd h.1.1 (by decide)
  | unary a t ih =>
    intro t' l l' h
    cases t' with
    | leaf b =>
      simp only [word, List.cons_append, List.nil_append, List.cons.injEq, Prod.mk.injEq] at h
      exact absurd h.1.1 (by decide)
    | unary b t' =>
      simp only [word, List.cons_append, List.cons.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨-, rfl⟩, h⟩ := h
      obtain ⟨rfl, rfl⟩ := ih _ _ _ h
      exact ⟨rfl, rfl⟩
    | binary b t' u' =>
      simp only [word, List.cons_append, List.cons.injEq, Prod.mk.injEq] at h
      exact absurd h.1.1 (by decide)
  | binary a t u iht ihu =>
    intro t' l l' h
    cases t' with
    | leaf b =>
      simp only [word, List.cons_append, List.nil_append, List.cons.injEq, Prod.mk.injEq] at h
      exact absurd h.1.1 (by decide)
    | unary b t' =>
      simp only [word, List.cons_append, List.cons.injEq, Prod.mk.injEq] at h
      exact absurd h.1.1 (by decide)
    | binary b t' u' =>
      simp only [word, List.cons_append, List.cons.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨-, rfl⟩, h⟩ := h
      rw [List.append_assoc, List.append_assoc] at h
      obtain ⟨rfl, h1⟩ := iht _ _ _ h
      obtain ⟨rfl, rfl⟩ := ihu _ _ _ h1
      exact ⟨rfl, rfl⟩

theorem word_injective : Function.Injective (word : ExprTree m → List (Fin 3 × Fin m)) := by
  intro t t' h
  exact (word_append_inj t t' [] [] (by simpa using h)).1

/-- The Łukasiewicz word of a tree of size `ℓ`, as a vector of length `ℓ`. -/
def code (ℓ : ℕ) (t : {t : ExprTree m // t.size = ℓ}) : List.Vector (Fin 3 × Fin m) ℓ :=
  ⟨t.1.word, by rw [length_word, t.2]⟩

theorem code_injective (ℓ : ℕ) : Function.Injective (code (m := m) ℓ) := by
  intro t t' h
  exact Subtype.ext (word_injective (congrArg Subtype.val h))

/-- The plan's injection of the trees of size `ℓ` into `Fin ℓ → Fin 3 × Fin m`. -/
def codeFin (ℓ : ℕ) (t : {t : ExprTree m // t.size = ℓ}) : Fin ℓ → Fin 3 × Fin m :=
  Equiv.vectorEquivFin _ _ (code ℓ t)

theorem codeFin_injective (ℓ : ℕ) : Function.Injective (codeFin (m := m) ℓ) :=
  (Equiv.vectorEquivFin _ _).injective.comp (code_injective ℓ)

/-- Trees of size `ℓ` form a finite type. -/
instance finite_size_eq (ℓ : ℕ) : Finite {t : ExprTree m // t.size = ℓ} :=
  Finite.of_injective _ (code_injective ℓ)

/-- At most `(3m)^ℓ` trees of size `ℓ`. -/
theorem card_size_eq_le (ℓ : ℕ) : Nat.card {t : ExprTree m // t.size = ℓ} ≤ (3 * m) ^ ℓ := by
  calc Nat.card {t : ExprTree m // t.size = ℓ}
      ≤ Nat.card (List.Vector (Fin 3 × Fin m) ℓ) :=
        Nat.card_le_card_of_injective _ (code_injective ℓ)
    _ = (3 * m) ^ ℓ := by simp [Nat.card_eq_fintype_card]

/-- The Łukasiewicz word of a tree of size at most `L`, tagged by its size. -/
def codeLe (L : ℕ) (t : {t : ExprTree m // t.size ≤ L}) :
    Σ k : Fin (L + 1), List.Vector (Fin 3 × Fin m) k :=
  ⟨⟨t.1.size, Nat.lt_succ_of_le t.2⟩, ⟨t.1.word, length_word _⟩⟩

theorem codeLe_injective (L : ℕ) : Function.Injective (codeLe (m := m) L) := by
  intro t t' h
  have hw : t.1.word = t'.1.word :=
    congrArg (fun p : Σ k : Fin (L + 1), List.Vector (Fin 3 × Fin m) k => p.2.1) h
  exact Subtype.ext (word_injective hw)

instance finite_size_le (L : ℕ) : Finite {t : ExprTree m // t.size ≤ L} :=
  Finite.of_injective _ (codeLe_injective L)

/-- `#{trees of size ≤ L} ≤ ∑_{k ≤ L} (3m)^k`. -/
theorem card_size_le_le_sum (L : ℕ) :
    Nat.card {t : ExprTree m // t.size ≤ L} ≤ ∑ k ∈ Finset.range (L + 1), (3 * m) ^ k := by
  calc Nat.card {t : ExprTree m // t.size ≤ L}
      ≤ Nat.card (Σ k : Fin (L + 1), List.Vector (Fin 3 × Fin m) k) :=
        Nat.card_le_card_of_injective _ (codeLe_injective L)
    _ = ∑ k : Fin (L + 1), (3 * m) ^ (k : ℕ) := by
        rw [Nat.card_sigma]; simp [Nat.card_eq_fintype_card]
    _ = ∑ k ∈ Finset.range (L + 1), (3 * m) ^ k :=
        Fin.sum_univ_eq_sum_range (fun k => (3 * m) ^ k) (L + 1)

/-- Geometric sum: `∑_{k ≤ L} q^k ≤ 2 q^L` for `q ≥ 2`. -/
theorem geom_sum_le_two_mul_pow (q : ℕ) (hq : 2 ≤ q) (L : ℕ) :
    ∑ k ∈ Finset.range (L + 1), q ^ k ≤ 2 * q ^ L := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ]
    have h2 : 2 * q ^ L ≤ q ^ (L + 1) := by
      rw [pow_succ, mul_comm]
      exact Nat.mul_le_mul_left _ hq
    calc ∑ k ∈ Finset.range (L + 1), q ^ k + q ^ (L + 1)
        ≤ 2 * q ^ L + q ^ (L + 1) := Nat.add_le_add_right ih _
      _ ≤ q ^ (L + 1) + q ^ (L + 1) := Nat.add_le_add_right h2 _
      _ = 2 * q ^ (L + 1) := by ring

/-- There are no trees over an empty alphabet. -/
instance : IsEmpty (ExprTree 0) :=
  ⟨fun t => by
    induction t with
    | leaf a => exact a.elim0
    | unary a _ _ => exact a.elim0
    | binary a _ _ _ _ => exact a.elim0⟩

/-- `|𝒮_L| ≤ 2 (3m)^L`. The paper assumes `3m ≥ 2`; the bound holds for every `m`. -/
theorem card_size_le_le (L : ℕ) :
    Nat.card {t : ExprTree m // t.size ≤ L} ≤ 2 * (3 * m) ^ L := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have : IsEmpty {t : ExprTree 0 // t.size ≤ L} := Subtype.isEmpty_of_false (fun t => isEmptyElim t)
    simp
  · calc Nat.card {t : ExprTree m // t.size ≤ L}
        ≤ ∑ k ∈ Finset.range (L + 1), (3 * m) ^ k := card_size_le_le_sum L
      _ ≤ 2 * (3 * m) ^ L := geom_sum_le_two_mul_pow (3 * m) (by omega) L

/-- `log |𝒮_L| ≤ L log(3m) + log 2` (THEORY.md §0). -/
theorem log_card_size_le_le (L : ℕ) :
    Real.log (Nat.card {t : ExprTree m // t.size ≤ L}) ≤ L * Real.log (3 * m) + Real.log 2 := by
  have hlog3m : 0 ≤ Real.log (3 * m) := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · exact Real.log_nonneg (by
        have : (1 : ℝ) ≤ m := by exact_mod_cast hm
        linarith)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rcases Nat.eq_zero_or_pos (Nat.card {t : ExprTree m // t.size ≤ L}) with h0 | hpos
  · rw [h0]; simp; positivity
  · have hle : (Nat.card {t : ExprTree m // t.size ≤ L} : ℝ) ≤ 2 * (3 * m) ^ L := by
      exact_mod_cast card_size_le_le (m := m) L
    have hposR : (0 : ℝ) < Nat.card {t : ExprTree m // t.size ≤ L} := by exact_mod_cast hpos
    have h3m : ((3 * m : ℕ) : ℝ) ^ L ≠ 0 := by
      intro h
      have : (0 : ℝ) < 2 * ((3 * m : ℕ) : ℝ) ^ L := by
        push_cast at hle ⊢; linarith
      rw [h] at this; simp at this
    calc Real.log (Nat.card {t : ExprTree m // t.size ≤ L})
        ≤ Real.log (2 * ((3 * m : ℕ) : ℝ) ^ L) := Real.log_le_log hposR (by push_cast at hle ⊢; exact hle)
      _ = Real.log 2 + L * Real.log (3 * m) := by
        rw [Real.log_mul (by norm_num) h3m, Real.log_pow]; push_cast; ring
      _ = L * Real.log (3 * m) + Real.log 2 := by ring

end ExprTree

end SymbolicIV.TreeCount

#print axioms SymbolicIV.TreeCount.ExprTree.card_size_eq_le
#print axioms SymbolicIV.TreeCount.ExprTree.card_size_le_le_sum
#print axioms SymbolicIV.TreeCount.ExprTree.card_size_le_le
#print axioms SymbolicIV.TreeCount.ExprTree.log_card_size_le_le
