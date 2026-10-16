import Mathlib

/-!
# Proposition 3.3, the Proposition 5 event logic, and Proposition 5(c)

Formalizes unit U11 of `FORMALIZATION_PLAN.md`:

* Proposition 3.3 of THEORY.md (§6, after Lemma 4): rates reduce to a modulus on the sieve.
* Proposition 5(a)–(b) of THEORY.md (§3.2): the event logic that turns the
  `χ²_K` limit of `AR_{s₀}(θ₀)` into the coverage bound, for an arbitrary (random) candidate set.
* Proposition 5(c), deterministic part: the bound `‖ĝ‖² ≤ χ² B_n / n` on the unrejected moments.

## Part 1: Proposition 3.3 (`SymbolicIV.Prop33`)

* `sieveModulus Hn f₀ A ε := ⨅ {‖A (f - f₀)‖² : f ∈ Hn, ‖f - f₀‖ ≥ ε}`, with values in `EReal`
  (so that the infimum over an empty set is `+∞`, the paper's convention) — `A` stands for
  `Π_{K_n} T`, of which only the values `A (f - f₀)` are used.
* `modulusInv ω q := sup {ε : ω ε ≤ q}` in `EReal` (the paper's generalized inverse).
* `sieveModulus_mono` : the modulus is nondecreasing.
* `sieveModulus_le_of_mem` : `ω_n(‖f̂ - f₀‖) ≤ Q_{K_n}(f̂) = ‖A (f̂ - f₀)‖²` for `f̂ ∈ H_n`
  (the paper's "by definition").
* `prop33` : for any `ω : ℝ → EReal` and `Q` with `ω ‖f̂ - f₀‖ ≤ Q`, `‖f̂ - f₀‖ ≤ ω⁻¹(Q)`.
* `prop33_sieve` : the two combined, `‖f̂ - f₀‖ ≤ ω_n⁻¹(Q_{K_n}(f̂))`.
* `prop33_real` : the same with a real-valued `ω` and `ωinv q := sSup {ε | ω ε ≤ q}` in `ℝ`, under
  the explicit boundedness `BddAbove {ε | ω ε ≤ Q}` that the real `sSup` needs.

The second bound of Proposition 3.3 (`Q_{K_n}(f̂) ≤ inf ‖f - f₀‖² + 2R_n + η_n`) is Step 3 of
Theorem 3's proof and belongs to the Theorem 3 units, not here.

## Part 2: Proposition 5(a)–(b), event logic (`SymbolicIV.Prop5Events`)

* `S AR ω := ⨅ θ, AR θ ω` (the S statistic of the true tree), `Cset Ŝ S c ω := {s ∈ Ŝ ω | S s ω ≤ c}`
  (the formula confidence set with critical value `c`).
* `S_le_AR` : `S_{s₀} ≤ AR_{s₀}(θ₀)` (needs `θ₀ ∈ Θ_{s₀}` and the statistic bounded below, which
  holds since `AR ≥ 0`).
* `event_subset_a` : `{s₀ ∈ Ŝ, s₀ ∉ C_α} ⊆ {AR_{s₀}(θ₀) > c}`, whatever the candidate set.
* `event_subset_b` : `E ∩ {s₀ ∉ C_α} ⊆ {AR_{s₀}(θ₀) > c}` with `E = {ŝ wrong, s₀ ∈ Ŝ}`.
* `prob_le_a`, `prob_le_b` : the probability inequalities, for any measure (no measurability needed).
* `limsup_le_a`, `limsup_le_b` : along a sequence of sample sizes, `limsup P_n(...) ≤ α` whenever
  `limsup P_n(AR_{s₀}(θ₀) > c) ≤ α` (the latter is what the `χ²_K` limit of (a) gives and is the
  hypothesis; the CLT and Slutsky are not re-proved).

## Part 3: Proposition 5(c), deterministic part (`SymbolicIV.Prop5c`)

`E` is a real inner product space (the instrument space `ℝ^K`).

* `inner_sq_le_of_posForm` : Cauchy–Schwarz for the semi-inner product `⟪T v, w⟫` of a symmetric
  positive `T` (via the discriminant).
* `norm_sq_le_opNorm_mul_inner` : for a symmetric positive `T : E →L[ℝ] E` and `T y = x`,
  `‖x‖² ≤ ‖T‖ ⟪x, y⟫`, i.e. `⟪x, Ω̂⁻¹ x⟫ ≥ ‖x‖² / ‖Ω̂‖` (`inner_inv_ge` states it with `Ω̂⁻¹`
  for a continuous linear equivalence).
* `weight b r := n⁻¹ ∑ᵢ rᵢ² (bᵢ ⊗ bᵢ)` (the paper's `Ω̂_s(θ)` with residuals `rᵢ = yᵢ - f_s(Xᵢ;θ)`);
  `weight_symm`, `weight_pos` : it is symmetric and positive semidefinite.
* `norm_weight_le` : `‖Ω̂‖ ≤ ζ² n⁻¹ ∑ rᵢ²` when `‖bᵢ‖ ≤ ζ`.
* `sum_sq_resid_le` : `∑ (yᵢ - Fᵢ)² ≤ 2 ∑ (yᵢ² + Fᵢ²)` (from `(a - b)² ≤ 2a² + 2b²`).
* `prop5c_norm_sq_le` : if `AR = n ⟪ĝ, y⟫ ≤ c` with `Ω̂ y = ĝ` (that is, `y = Ω̂⁻¹ ĝ`) and
  `|f(Xᵢ)| ≤ F(Xᵢ)`, then `‖ĝ‖² ≤ c B_n / n` with `B_n := 2 ζ² n⁻¹ ∑ (yᵢ² + F(Xᵢ)²)`.

Stretch (winsorized-weight algebra), `SymbolicIV.Prop5c.inner_inv_mono` and `capped_form_ge`:
for `0 ≺ Ω_c ⪯ Ω`, `⟪Ω⁻¹ w, w⟫ ≤ ⟪Ω_c⁻¹ w, w⟫`, hence with `S = Ω^{1/2}` (a symmetric invertible
square root, given as data with `S ∘ S = Ω`), `⟪Ω_c⁻¹ S ξ, S ξ⟫ ≥ ‖ξ‖²`, i.e. `ξ'Aξ ≥ ξ'ξ`, and
`⟪A ξ, ξ⟫ ≤ ‖A‖ ‖ξ‖²`. The identification `‖A‖ = 1/λ_min(Ω_c Ω⁻¹)` is not formalized.

## Hypotheses beyond the paper's statements

* Proposition 3.3: none for the `EReal` version. The real version (`prop33_real`) adds
  `BddAbove {ε | ω ε ≤ Q}`, which the paper has implicitly (`ω_n = +∞` beyond the diameter of
  `H_n`, so the set is bounded by that diameter; Lean's real `sSup` of an unbounded set is `0`).
* Proposition 5(a)–(b): the statistic `AR θ ω` is real-valued with `0 ≤ AR θ ω` for all `θ`, which
  makes the infimum over `Θ` a real number. The paper's convention `AR_s(θ) := +∞` where `Ω̂_s(θ)` is
  singular is therefore not modelled here: the Lean statements cover the case where `Ω̂_s(θ)` is
  positive definite at every `θ` (a `+∞` value could only enlarge `AR` and the infimum, so the
  event inclusions of (a) and (b) hold a fortiori). `S` is the infimum, as in the paper since the
  fifth pass (the minimum need not be attained once the `+∞` convention is used). The `χ²_K` limit enters only through
  `limsup P_n(AR_{s₀}(θ₀) > c) ≤ α`. Candidate sets and the selected tree are arbitrary functions of
  the sample point, no measurability is assumed (none is needed: the outer-measure monotonicity
  suffices).
* Proposition 5(c): `ĝ = Ω̂ y` for some `y` (the paper's `Ω̂⁻¹ ĝ`; this is where `Ω̂` is assumed
  invertible, as in the paper's definition of `AR`), `‖bᵢ‖ ≤ ζ` (the paper's `sup_z ‖b(z)‖ ≤ ζ_K`),
  `|f(Xᵢ)| ≤ F(Xᵢ)` (the envelope of (A3)), `0 < n`. The stochastic part (`B_n = O_p(1)`,
  the uniform deviation `R_n` of (C2), and Lemma 1(c)) is not in this unit.
* Stretch: the square root `Ω^{1/2}` is not constructed; `capped_form_ge` takes a symmetric `S`
  with `S ∘ S = Ω` as data (it exists by the spectral theorem), and takes `y = S⁻¹ ξ`, `z = Ω_c⁻¹ S ξ`
  through the equations `S y = ξ`, `Ω_c z = S ξ` (invertibility of `Ω` and `Ω_c`, which the paper's
  `0 ≺ Ω_c ⪯ Ω` gives). `inner_inv_mono` needs only `Ω_c ⪰ 0` symmetric and `Ω_c ⪯ Ω`.
-/

open scoped RealInnerProductSpace

noncomputable section

/-! ## Part 1: Proposition 3.3 -/

namespace SymbolicIV.Prop33

variable {H H' : Type*} [NormedAddCommGroup H] [NormedAddCommGroup H']

/-- The sieve modulus `ω_n(ε) = inf {‖Π_{K_n} T (f - f₀)‖² : f ∈ H_n, ‖f - f₀‖ ≥ ε}`, in `EReal`
(`+∞` when no `f ∈ H_n` is `ε`-far from `f₀`). -/
def sieveModulus (Hn : Set H) (f₀ : H) (A : H → H') (ε : ℝ) : EReal :=
  sInf ((fun f : H => ((‖A (f - f₀)‖ ^ 2 : ℝ) : EReal)) '' {f | f ∈ Hn ∧ ε ≤ ‖f - f₀‖})

/-- The generalized inverse `ω⁻¹(q) = sup {ε : ω ε ≤ q}`. -/
def modulusInv (ω : ℝ → EReal) (q : EReal) : EReal :=
  sSup ((fun ε : ℝ => (ε : EReal)) '' {ε | ω ε ≤ q})

/-- The modulus is nondecreasing in `ε`. -/
theorem sieveModulus_mono (Hn : Set H) (f₀ : H) (A : H → H') :
    Monotone (sieveModulus Hn f₀ A) := by
  intro ε₁ ε₂ h
  unfold sieveModulus
  apply sInf_le_sInf
  apply Set.image_mono
  intro f hf
  exact ⟨hf.1, le_trans h hf.2⟩

/-- `ω_n(‖f̂ - f₀‖) ≤ ‖Π_{K_n} T (f̂ - f₀)‖²` for `f̂ ∈ H_n`: the paper's "by definition". -/
theorem sieveModulus_le_of_mem {Hn : Set H} {f₀ : H} (A : H → H') {fhat : H} (hf : fhat ∈ Hn) :
    sieveModulus Hn f₀ A ‖fhat - f₀‖ ≤ ((‖A (fhat - f₀)‖ ^ 2 : ℝ) : EReal) := by
  unfold sieveModulus
  apply sInf_le
  exact ⟨fhat, ⟨hf, le_rfl⟩, rfl⟩

/-- Proposition 3.3, abstract form: if `ω(‖f̂ - f₀‖) ≤ Q` then `‖f̂ - f₀‖ ≤ ω⁻¹(Q)`. -/
theorem prop33 (ω : ℝ → EReal) {fhat f₀ : H} {Q : EReal} (hQ : ω ‖fhat - f₀‖ ≤ Q) :
    ((‖fhat - f₀‖ : ℝ) : EReal) ≤ modulusInv ω Q := by
  unfold modulusInv
  apply le_sSup
  exact ⟨‖fhat - f₀‖, hQ, rfl⟩

/-- Proposition 3.3 for the sieve modulus: `‖f̂ - f₀‖ ≤ ω_n⁻¹(Q_{K_n}(f̂))` with
`Q_{K_n}(f̂) = ‖Π_{K_n} T (f̂ - f₀)‖²`. -/
theorem prop33_sieve {Hn : Set H} {f₀ : H} (A : H → H') {fhat : H} (hf : fhat ∈ Hn) :
    ((‖fhat - f₀‖ : ℝ) : EReal) ≤
      modulusInv (sieveModulus Hn f₀ A) ((‖A (fhat - f₀)‖ ^ 2 : ℝ) : EReal) :=
  prop33 _ (sieveModulus_le_of_mem A hf)

/-- Proposition 3.3 with a real-valued modulus and `ωinv q := sSup {ε | ω ε ≤ q}` in `ℝ`; the
boundedness hypothesis is what the real `sSup` needs. -/
theorem prop33_real (ω : ℝ → ℝ) {fhat f₀ : H} {Q : ℝ} (hQ : ω ‖fhat - f₀‖ ≤ Q)
    (hbdd : BddAbove {ε | ω ε ≤ Q}) :
    ‖fhat - f₀‖ ≤ sSup {ε | ω ε ≤ Q} :=
  le_csSup hbdd hQ

end SymbolicIV.Prop33

/-! ## Part 2: Proposition 5(a)–(b), the event logic -/

namespace SymbolicIV.Prop5Events

open MeasureTheory Filter

variable {Ω : Type*} {Tree : Type*}

/-- The S statistic `S_s = inf_{θ ∈ Θ_s} AR_s(θ)` of a tree whose statistic is `AR : Θ → Ω → ℝ`. -/
def S {Θ : Type*} (AR : Θ → Ω → ℝ) (ω : Ω) : ℝ := ⨅ θ, AR θ ω

/-- The formula confidence set `C_α = {s ∈ Ŝ : S_s ≤ c}` for a (random) candidate set `Ŝ` and
S statistics `Sstat s`. -/
def Cset (Shat : Ω → Set Tree) (Sstat : Tree → Ω → ℝ) (c : ℝ) (ω : Ω) : Set Tree :=
  {s | s ∈ Shat ω ∧ Sstat s ω ≤ c}

/-- `S_{s₀} ≤ AR_{s₀}(θ₀)` for `θ₀ ∈ Θ_{s₀}`, using that the statistic is nonnegative (so that the
infimum is a genuine lower bound). -/
theorem S_le_AR {Θ : Type*} (AR : Θ → Ω → ℝ) (hnn : ∀ θ ω, 0 ≤ AR θ ω) (θ₀ : Θ) (ω : Ω) :
    S AR ω ≤ AR θ₀ ω :=
  ciInf_le ⟨0, by rintro _ ⟨θ, rfl⟩; exact hnn θ ω⟩ θ₀

section Events

variable {Θ : Type*} (AR : Θ → Ω → ℝ) (hnn : ∀ θ ω, 0 ≤ AR θ ω) (θ₀ : Θ)
  (Shat : Ω → Set Tree) (Sstat : Tree → Ω → ℝ) (s₀ : Tree) (hS : Sstat s₀ = S AR) (c : ℝ)

include hnn hS

/-- (a) `{s₀ ∈ Ŝ, s₀ ∉ C_α} ⊆ {AR_{s₀}(θ₀) > c}`, whatever the candidate set. -/
theorem event_subset_a :
    {ω | s₀ ∈ Shat ω ∧ s₀ ∉ Cset Shat Sstat c ω} ⊆ {ω | c < AR θ₀ ω} := by
  intro ω ⟨hmem, hnot⟩
  by_contra hle
  have hle : AR θ₀ ω ≤ c := not_lt.mp hle
  apply hnot
  refine ⟨hmem, ?_⟩
  rw [hS]
  exact le_trans (S_le_AR AR hnn θ₀ ω) hle

/-- (b) with `E = {ŝ ∉ S₀ (wrong tree), s₀ ∈ Ŝ}`: `E ∩ {s₀ ∉ C_α} ⊆ {AR_{s₀}(θ₀) > c}`. -/
theorem event_subset_b (shat : Ω → Tree) (S₀ : Set Tree) :
    {ω | shat ω ∉ S₀ ∧ s₀ ∈ Shat ω} ∩ {ω | s₀ ∉ Cset Shat Sstat c ω} ⊆ {ω | c < AR θ₀ ω} := by
  intro ω ⟨⟨_, hmem⟩, hnot⟩
  exact event_subset_a AR hnn θ₀ Shat Sstat s₀ hS c ⟨hmem, hnot⟩

/-- (a), probability form, for any measure. -/
theorem prob_le_a [MeasurableSpace Ω] (μ : Measure Ω) :
    μ {ω | s₀ ∈ Shat ω ∧ s₀ ∉ Cset Shat Sstat c ω} ≤ μ {ω | c < AR θ₀ ω} :=
  measure_mono (event_subset_a AR hnn θ₀ Shat Sstat s₀ hS c)

/-- (b), probability form, for any measure. -/
theorem prob_le_b [MeasurableSpace Ω] (μ : Measure Ω) (shat : Ω → Tree) (S₀ : Set Tree) :
    μ ({ω | shat ω ∉ S₀ ∧ s₀ ∈ Shat ω} ∩ {ω | s₀ ∉ Cset Shat Sstat c ω}) ≤
      μ {ω | c < AR θ₀ ω} :=
  measure_mono (event_subset_b AR hnn θ₀ Shat Sstat s₀ hS c shat S₀)

end Events

section Limsup

variable [MeasurableSpace Ω]

/-- (a), asymptotic form. Along a sequence indexed by `n` (sample size), with statistics `AR n`,
candidate sets `Shat n`, S statistics `Sstat n` and probabilities `μ n`: if
`limsup P_n(AR_{s₀}(θ₀) > c) ≤ α` (what the `χ²_K` limit gives with `c = χ²_{K,1-α}`), then
`limsup P_n(s₀ ∈ Ŝ, s₀ ∉ C_α) ≤ α`. -/
theorem limsup_le_a {Θ : Type*} (AR : ℕ → Θ → Ω → ℝ) (hnn : ∀ n θ ω, 0 ≤ AR n θ ω) (θ₀ : Θ)
    (Shat : ℕ → Ω → Set Tree) (Sstat : ℕ → Tree → Ω → ℝ) (s₀ : Tree)
    (hS : ∀ n, Sstat n s₀ = S (AR n)) (c : ℝ) (μ : ℕ → Measure Ω) (α : ENNReal)
    (hlim : limsup (fun n => μ n {ω | c < AR n θ₀ ω}) atTop ≤ α) :
    limsup (fun n => μ n {ω | s₀ ∈ Shat n ω ∧ s₀ ∉ Cset (Shat n) (Sstat n) c ω}) atTop ≤ α :=
  le_trans (limsup_le_limsup (Eventually.of_forall fun n =>
    prob_le_a (AR n) (hnn n) θ₀ (Shat n) (Sstat n) s₀ (hS n) c (μ n))) hlim

/-- (b), asymptotic form: `limsup P_n(E ∩ {s₀ ∉ C_α}) ≤ α` under the same hypothesis. -/
theorem limsup_le_b {Θ : Type*} (AR : ℕ → Θ → Ω → ℝ) (hnn : ∀ n θ ω, 0 ≤ AR n θ ω) (θ₀ : Θ)
    (Shat : ℕ → Ω → Set Tree) (Sstat : ℕ → Tree → Ω → ℝ) (s₀ : Tree)
    (hS : ∀ n, Sstat n s₀ = S (AR n)) (c : ℝ) (μ : ℕ → Measure Ω) (α : ENNReal)
    (shat : ℕ → Ω → Tree) (S₀ : Set Tree)
    (hlim : limsup (fun n => μ n {ω | c < AR n θ₀ ω}) atTop ≤ α) :
    limsup (fun n => μ n ({ω | shat n ω ∉ S₀ ∧ s₀ ∈ Shat n ω} ∩
      {ω | s₀ ∉ Cset (Shat n) (Sstat n) c ω})) atTop ≤ α :=
  le_trans (limsup_le_limsup (Eventually.of_forall fun n =>
    prob_le_b (AR n) (hnn n) θ₀ (Shat n) (Sstat n) s₀ (hS n) c (μ n) (shat n) S₀)) hlim

end Limsup

end SymbolicIV.Prop5Events

/-! ## Part 3: Proposition 5(c), deterministic part -/

namespace SymbolicIV.Prop5c

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A symmetric positive semidefinite operator (the paper's `Ω̂ ⪰ 0`, `Ω̂' = Ω̂`). -/
structure IsSymmPos (T : E →L[ℝ] E) : Prop where
  symm : ∀ v w, ⟪T v, w⟫ = ⟪v, T w⟫
  nonneg : ∀ v, 0 ≤ ⟪T v, v⟫

/-- Cauchy–Schwarz for the semi-inner product `(v, w) ↦ ⟪T v, w⟫` of a symmetric positive `T`,
via the discriminant of `t ↦ ⟪T (y - t z), y - t z⟫ ≥ 0`. -/
theorem inner_sq_le_of_posForm {T : E →L[ℝ] E} (hT : IsSymmPos T) (y z : E) :
    ⟪T y, z⟫ ^ 2 ≤ ⟪T y, y⟫ * ⟪T z, z⟫ := by
  have hs : ⟪T z, y⟫ = ⟪T y, z⟫ := by rw [hT.symm, real_inner_comm]
  have h : ∀ t : ℝ, 0 ≤ ⟪T z, z⟫ * (t * t) + (-2 * ⟪T y, z⟫) * t + ⟪T y, y⟫ := by
    intro t
    have h0 := hT.nonneg (y - t • z)
    have e : ⟪T (y - t • z), y - t • z⟫ =
        ⟪T z, z⟫ * (t * t) + (-2 * ⟪T y, z⟫) * t + ⟪T y, y⟫ := by
      simp only [map_sub, map_smul, inner_sub_left, inner_sub_right, real_inner_smul_left,
        real_inner_smul_right, hs]
      ring
    linarith
  have hd := discrim_le_zero h
  unfold discrim at hd
  nlinarith

/-- `‖x‖² ≤ ‖T‖ ⟪x, y⟫` when `T y = x`, for a symmetric positive `T`: with `y = Ω̂⁻¹ x` this is
`⟪x, Ω̂⁻¹ x⟫ ≥ ‖x‖² / ‖Ω̂‖`. -/
theorem norm_sq_le_opNorm_mul_inner {T : E →L[ℝ] E} (hT : IsSymmPos T) {x y : E}
    (hxy : T y = x) : ‖x‖ ^ 2 ≤ ‖T‖ * ⟪x, y⟫ := by
  have h1 := inner_sq_le_of_posForm hT y x
  rw [hxy, real_inner_self_eq_norm_sq] at h1
  have h2 : ⟪T x, x⟫ ≤ ‖T‖ * ‖x‖ ^ 2 := by
    calc ⟪T x, x⟫ ≤ ‖T x‖ * ‖x‖ := real_inner_le_norm _ _
      _ ≤ ‖T‖ * ‖x‖ * ‖x‖ := by gcongr; exact T.le_opNorm x
      _ = ‖T‖ * ‖x‖ ^ 2 := by ring
  have hxy0 : 0 ≤ ⟪x, y⟫ := by
    rw [← hxy]; exact hT.nonneg y
  have hT0 : 0 ≤ ‖T‖ := norm_nonneg _
  by_cases hx : ‖x‖ = 0
  · rw [hx]; simp; positivity
  · have hpos : 0 < ‖x‖ ^ 2 := by positivity
    have h3 : ‖x‖ ^ 2 * ‖x‖ ^ 2 ≤ ‖x‖ ^ 2 * (‖T‖ * ⟪x, y⟫) := by
      calc ‖x‖ ^ 2 * ‖x‖ ^ 2 = (‖x‖ ^ 2) ^ 2 := by ring
        _ ≤ ⟪x, y⟫ * ⟪T x, x⟫ := h1
        _ ≤ ⟪x, y⟫ * (‖T‖ * ‖x‖ ^ 2) := by gcongr
        _ = ‖x‖ ^ 2 * (‖T‖ * ⟪x, y⟫) := by ring
    exact le_of_mul_le_mul_left h3 hpos

/-- The paper's form: for an invertible symmetric positive `Ω̂`, `⟪x, Ω̂⁻¹ x⟫ ≥ ‖x‖² / ‖Ω̂‖`. -/
theorem inner_inv_ge (T : E ≃L[ℝ] E) (hT : IsSymmPos (T : E →L[ℝ] E)) (x : E) :
    ‖x‖ ^ 2 / ‖(T : E →L[ℝ] E)‖ ≤ ⟪x, T.symm x⟫ := by
  have hx : (T : E →L[ℝ] E) (T.symm x) = x := T.apply_symm_apply x
  have h := norm_sq_le_opNorm_mul_inner hT hx
  have hnn : 0 ≤ ⟪x, T.symm x⟫ := by
    have h0 := hT.nonneg (T.symm x)
    rwa [hx] at h0
  rcases (norm_nonneg (T : E →L[ℝ] E)).eq_or_lt with h0 | h0
  · rw [← h0, div_zero]; exact hnn
  · rw [div_le_iff₀ h0]; linarith [mul_comm ‖(T : E →L[ℝ] E)‖ ⟪x, T.symm x⟫]

/-- The rank-one map `v ↦ ⟪b, v⟫ b` (the matrix `b b'`). -/
def rankOne (b : E) : E →L[ℝ] E := (innerSL ℝ b).smulRight b

theorem rankOne_apply (b v : E) : rankOne b v = ⟪b, v⟫ • b := by
  simp [rankOne]

theorem norm_rankOne (b : E) : ‖rankOne b‖ = ‖b‖ ^ 2 := by
  rw [rankOne, ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm, sq]

/-- The GMM weight `Ω̂ = n⁻¹ ∑ᵢ rᵢ² bᵢ bᵢ'` built from instruments `bᵢ` and residuals `rᵢ`. -/
def weight {ι : Type*} (s : Finset ι) (n : ℝ) (b : ι → E) (r : ι → ℝ) : E →L[ℝ] E :=
  (1 / n) • ∑ i ∈ s, (r i ^ 2) • rankOne (b i)

theorem weight_apply {ι : Type*} (s : Finset ι) (n : ℝ) (b : ι → E) (r : ι → ℝ) (v : E) :
    weight s n b r v = (1 / n) • ∑ i ∈ s, (r i ^ 2) • (⟪b i, v⟫ • b i) := by
  simp [weight, rankOne_apply]

/-- `Ω̂` is symmetric and positive semidefinite. -/
theorem weight_isSymmPos {ι : Type*} (s : Finset ι) {n : ℝ} (hn : 0 ≤ n) (b : ι → E)
    (r : ι → ℝ) : IsSymmPos (weight s n b r) where
  symm v w := by
    simp only [weight_apply, real_inner_smul_left, real_inner_smul_right, sum_inner, inner_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [real_inner_comm (b i) v]
    ring
  nonneg v := by
    simp only [weight_apply, real_inner_smul_left, sum_inner]
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (sq_nonneg _) (mul_self_nonneg _)

/-- `‖Ω̂‖ ≤ ζ² n⁻¹ ∑ rᵢ²` when `‖bᵢ‖ ≤ ζ`. -/
theorem norm_weight_le {ι : Type*} (s : Finset ι) {n : ℝ} (hn : 0 ≤ n) (b : ι → E) (r : ι → ℝ)
    {ζ : ℝ} (hζ : ∀ i ∈ s, ‖b i‖ ≤ ζ) :
    ‖weight s n b r‖ ≤ ζ ^ 2 * ((1 / n) * ∑ i ∈ s, r i ^ 2) := by
  unfold weight
  rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  calc (1 / n) * ‖∑ i ∈ s, r i ^ 2 • rankOne (b i)‖
      ≤ (1 / n) * ∑ i ∈ s, ‖r i ^ 2 • rankOne (b i)‖ := by
        gcongr; exact norm_sum_le _ _
    _ = (1 / n) * ∑ i ∈ s, r i ^ 2 * ‖b i‖ ^ 2 := by
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        rw [norm_smul, norm_rankOne, Real.norm_of_nonneg (sq_nonneg _)]
    _ ≤ (1 / n) * ∑ i ∈ s, r i ^ 2 * ζ ^ 2 := by
        gcongr with i hi
        exact hζ i hi
    _ = ζ ^ 2 * ((1 / n) * ∑ i ∈ s, r i ^ 2) := by
        rw [← Finset.sum_mul]; ring

/-- `∑ (yᵢ - Fᵢ)² ≤ 2 ∑ (yᵢ² + Fᵢ²)`. -/
theorem sum_sq_resid_le {ι : Type*} (s : Finset ι) (y F : ι → ℝ) :
    ∑ i ∈ s, (y i - F i) ^ 2 ≤ 2 * ∑ i ∈ s, (y i ^ 2 + F i ^ 2) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  nlinarith [sq_nonneg (y i + F i)]

/-- Proposition 5(c), deterministic part. With residuals `rᵢ = yᵢ - f(Xᵢ)`, weight
`Ω̂ = weight s n b r`, moments `ĝ = Ω̂ w` (so `w = Ω̂⁻¹ ĝ`), `AR = n ⟪ĝ, Ω̂⁻¹ ĝ⟫ ≤ c`,
`‖bᵢ‖ ≤ ζ` and the envelope `|f(Xᵢ)| ≤ F(Xᵢ)`:
`‖ĝ‖² ≤ c B_n / n` with `B_n = 2 ζ² n⁻¹ ∑ (yᵢ² + F(Xᵢ)²)`. -/
theorem prop5c_norm_sq_le {ι : Type*} (s : Finset ι) {n : ℝ} (hn : 0 < n) (b : ι → E)
    (y f F : ι → ℝ) {ζ : ℝ} (hζ : ∀ i ∈ s, ‖b i‖ ≤ ζ) (hF : ∀ i ∈ s, |f i| ≤ F i)
    {ghat w : E} (hw : weight s n b (fun i => y i - f i) w = ghat)
    {c : ℝ} (hAR : n * ⟪ghat, w⟫ ≤ c) :
    ‖ghat‖ ^ 2 ≤ c * (2 * ζ ^ 2 * ((1 / n) * ∑ i ∈ s, (y i ^ 2 + F i ^ 2))) / n := by
  have hsp := weight_isSymmPos s hn.le b (fun i => y i - f i)
  have h1 := norm_sq_le_opNorm_mul_inner hsp hw
  have h2 := norm_weight_le s hn.le b (fun i => y i - f i) hζ
  have h3 : ∑ i ∈ s, (y i - f i) ^ 2 ≤ 2 * ∑ i ∈ s, (y i ^ 2 + F i ^ 2) := by
    refine le_trans (sum_sq_resid_le s y f)
      (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi => ?_) (by norm_num))
    have h4 : |f i| ^ 2 ≤ F i ^ 2 := by gcongr; exact hF i hi
    rw [sq_abs] at h4
    linarith
  have hinner : 0 ≤ ⟪ghat, w⟫ := by
    rw [← hw]; exact hsp.nonneg w
  have hc : 0 ≤ c := le_trans (by positivity) hAR
  have hΩ0 : 0 ≤ ‖weight s n b (fun i => y i - f i)‖ := norm_nonneg _
  have hB : ‖weight s n b (fun i => y i - f i)‖ ≤
      2 * ζ ^ 2 * ((1 / n) * ∑ i ∈ s, (y i ^ 2 + F i ^ 2)) := by
    refine le_trans h2 ?_
    have : (1 / n) * ∑ i ∈ s, (y i - f i) ^ 2 ≤ (1 / n) * (2 * ∑ i ∈ s, (y i ^ 2 + F i ^ 2)) := by
      gcongr
    nlinarith [sq_nonneg ζ]
  rw [le_div_iff₀ hn]
  calc ‖ghat‖ ^ 2 * n ≤ ‖weight s n b (fun i => y i - f i)‖ * ⟪ghat, w⟫ * n := by gcongr
    _ = ‖weight s n b (fun i => y i - f i)‖ * (n * ⟪ghat, w⟫) := by ring
    _ ≤ ‖weight s n b (fun i => y i - f i)‖ * c := by gcongr
    _ ≤ (2 * ζ ^ 2 * ((1 / n) * ∑ i ∈ s, (y i ^ 2 + F i ^ 2))) * c := by gcongr
    _ = c * (2 * ζ ^ 2 * ((1 / n) * ∑ i ∈ s, (y i ^ 2 + F i ^ 2))) := by ring

/-! ### Stretch: the winsorized-weight algebra -/

/-- Operator monotonicity of the inverse on quadratic forms: if `0 ⪯ Ω_c ⪯ Ω` (`Ω_c` symmetric;
nothing is needed of `Ω` beyond the domination), `Ω y = w` and `Ω_c z = w` (so `y = Ω⁻¹ w`,
`z = Ω_c⁻¹ w`), then `⟪Ω⁻¹ w, w⟫ ≤ ⟪Ω_c⁻¹ w, w⟫`. -/
theorem inner_inv_mono {Ω Ωc : E →L[ℝ] E} (hΩc : IsSymmPos Ωc)
    (hle : ∀ v, ⟪Ωc v, v⟫ ≤ ⟪Ω v, v⟫) {w y z : E} (hy : Ω y = w) (hz : Ωc z = w) :
    ⟪y, w⟫ ≤ ⟪z, w⟫ := by
  -- ⟪y, w⟫ = ⟪Ω_c y, z⟫, and Cauchy–Schwarz for Ω_c
  have e1 : ⟪y, w⟫ = ⟪Ωc y, z⟫ := by rw [← hz, hΩc.symm]
  have e2 : ⟪Ωc y, y⟫ ≤ ⟪y, w⟫ := by rw [← hy, real_inner_comm (Ω y) y]; exact hle y
  have e3 : ⟪Ωc z, z⟫ = ⟪z, w⟫ := by rw [← hz, real_inner_comm]
  have cs := inner_sq_le_of_posForm hΩc y z
  rw [← e1, e3] at cs
  have hyw : 0 ≤ ⟪y, w⟫ := le_trans (hΩc.nonneg y) e2
  have hzw : 0 ≤ ⟪z, w⟫ := by rw [← e3]; exact hΩc.nonneg z
  rcases hyw.eq_or_lt with h0 | h0
  · rw [← h0]; exact hzw
  · have : ⟪y, w⟫ * ⟪y, w⟫ ≤ ⟪y, w⟫ * ⟪z, w⟫ := by
      calc ⟪y, w⟫ * ⟪y, w⟫ = ⟪y, w⟫ ^ 2 := by ring
        _ ≤ ⟪Ωc y, y⟫ * ⟪z, w⟫ := cs
        _ ≤ ⟪y, w⟫ * ⟪z, w⟫ := by gcongr
    exact le_of_mul_le_mul_left this h0

/-- The capped statistic's limit form dominates `‖ξ‖²`: with `S = Ω^{1/2}` symmetric and
`S ∘ S = Ω`, `0 ⪯ Ω_c ⪯ Ω`, `S y = ξ` (so `y = S⁻¹ ξ`) and `Ω_c z = S ξ` (so `z = Ω_c⁻¹ S ξ`),
`ξ' Ω^{1/2} Ω_c⁻¹ Ω^{1/2} ξ = ⟪z, S ξ⟫ ≥ ‖ξ‖²`. -/
theorem capped_form_ge {S Ω Ωc : E →L[ℝ] E} (hS : ∀ v w, ⟪S v, w⟫ = ⟪v, S w⟫)
    (hSS : ∀ v, Ω v = S (S v)) (hΩc : IsSymmPos Ωc) (hle : ∀ v, ⟪Ωc v, v⟫ ≤ ⟪Ω v, v⟫)
    {ξ y z : E} (hy : S y = ξ) (hz : Ωc z = S ξ) :
    ‖ξ‖ ^ 2 ≤ ⟪z, S ξ⟫ := by
  have hΩy : Ω y = S ξ := by rw [hSS, hy]
  have h := inner_inv_mono hΩc hle hΩy hz
  calc ‖ξ‖ ^ 2 = ⟪ξ, ξ⟫ := (real_inner_self_eq_norm_sq ξ).symm
    _ = ⟪y, S ξ⟫ := by rw [← hy, hS, hy]
    _ ≤ ⟪z, S ξ⟫ := h

/-- The matching upper bound `ξ' A ξ ≤ ‖A‖ ‖ξ‖²` for any operator `A`. -/
theorem capped_form_le (A : E →L[ℝ] E) (ξ : E) : ⟪A ξ, ξ⟫ ≤ ‖A‖ * ‖ξ‖ ^ 2 :=
  calc ⟪A ξ, ξ⟫ ≤ ‖A ξ‖ * ‖ξ‖ := real_inner_le_norm _ _
    _ ≤ ‖A‖ * ‖ξ‖ * ‖ξ‖ := by gcongr; exact A.le_opNorm ξ
    _ = ‖A‖ * ‖ξ‖ ^ 2 := by ring

end SymbolicIV.Prop5c

end

#print axioms SymbolicIV.Prop33.prop33_sieve
#print axioms SymbolicIV.Prop33.prop33_real
#print axioms SymbolicIV.Prop5Events.limsup_le_a
#print axioms SymbolicIV.Prop5Events.limsup_le_b
#print axioms SymbolicIV.Prop5c.inner_inv_ge
#print axioms SymbolicIV.Prop5c.prop5c_norm_sq_le
#print axioms SymbolicIV.Prop5c.capped_form_ge
#print axioms SymbolicIV.Prop5c.capped_form_le
