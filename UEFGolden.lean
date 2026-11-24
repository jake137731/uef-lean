/-
  THE UNIFIED EXISTENCE FRAMEWORK — Chapter 14, Theorem 19, the golden ratio, in Lean 4 with Mathlib

  Jake McDonough, Institute for Higher Thinking, Louisville, Kentucky, USA

  Source: UEF Release, 01_Manuscript.pdf, evidence Chapter 14: the binary partition
  O = ker(Φ), C = Ω \ O (14.2), the recursive partition uₙ₋₁ = rₙ + uₙ (Step 3c),
  the constant ratio xₙ = x (Step 4c), and full self-similarity x = (1 − x)/x
  (Step 4d), whose unique solution in (0, 1) is Ξ̄* = φ⁻¹ = (√5 − 1)/2.
-/
import Mathlib

namespace UEF.Golden

/-! ## 14.2 — The Lagrangian forces a binary partition -/

/-- O = ker(Φ) = {ω : ξᵢ(ω) = 0 for all i}, C = Ω \ O = {ω : ∃i, ξᵢ(ω) > 0}. With
    non-negative defects these are complementary, exhaustive and mutually exclusive:
    there is no third region. -/
theorem binary_partition {Ω : Type*} (Φ : Ω → Fin 7 → ℝ) (nonneg : ∀ ω i, 0 ≤ Φ ω i) (ω : Ω) :
    ((∀ i, Φ ω i = 0) ∨ (∃ i, 0 < Φ ω i)) ∧ ¬ ((∀ i, Φ ω i = 0) ∧ (∃ i, 0 < Φ ω i)) := by
  constructor
  · by_cases h : ∀ i, Φ ω i = 0
    · exact Or.inl h
    · push_neg at h
      obtain ⟨i, hi⟩ := h
      exact Or.inr ⟨i, lt_of_le_of_ne (nonneg ω i) (Ne.symm hi)⟩
  · rintro ⟨h0, i, hi⟩
    rw [h0 i] at hi
    exact lt_irrefl 0 hi

/-! ## Step 3c and Step 4c — the recursive partition with constant ratio -/

/-- With u₋₁ = 1 and constant ratio x: uₙ = xⁿ⁺¹, rₙ = uₙ₋₁ − uₙ = xⁿ(1 − x). -/
def u (x : ℝ) (n : ℕ) : ℝ := x ^ (n + 1)
def r (x : ℝ) (n : ℕ) : ℝ := x ^ n * (1 - x)

/-- Level 0: total system = r₀ + u₀ = (1 − Ξ̄) + Ξ̄ = 1. -/
theorem level_zero (x : ℝ) : r x 0 + u x 0 = 1 := by
  simp [r, u]

/-- Level n: uₙ₋₁ = rₙ + uₙ. What was unresolved at level n − 1 either resolves at
    level n or remains unresolved: each level is a conservation law. -/
theorem level_conservation (x : ℝ) (n : ℕ) : u x n = r x (n + 1) + u x (n + 1) := by
  simp only [u, r]
  ring

/-- Down to any depth N, the resolved parts and what remains unresolved add up to the
    whole: r₀ + r₁ + … + r_N + u_N = 1. -/
theorem whole (x : ℝ) (N : ℕ) : (∑ n ∈ Finset.range (N + 1), r x n) + u x N = 1 := by
  induction N with
  | zero => simp [r, u]
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have := level_conservation x N
    linarith

/-! ## Step 4d — full self-similarity, and Theorem 19 -/

theorem sqrt5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)

theorem one_lt_sqrt5 : 1 < Real.sqrt 5 := by
  rw [show (1 : ℝ) = Real.sqrt 1 by simp]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

theorem sqrt5_lt_three : Real.sqrt 5 < 3 := by
  rw [show (3 : ℝ) = Real.sqrt 9 by rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

/-- φ⁻¹ = (√5 − 1)/2 lies in (0, 1). -/
theorem invPhi_in_unit : 0 < (Real.sqrt 5 - 1) / 2 ∧ (Real.sqrt 5 - 1) / 2 < 1 := by
  constructor <;> linarith [one_lt_sqrt5, sqrt5_lt_three]

/-- Inter-level ratio = intra-level ratio: x = (1 − x)/x is x² + x − 1 = 0. -/
theorem self_similar_iff (x : ℝ) (hx : 0 < x) : x = (1 - x) / x ↔ x ^ 2 + x - 1 = 0 := by
  rw [eq_div_iff hx.ne']
  constructor <;> intro h <;> nlinarith [h]

/-- The same equation as a continued fraction: x = 1/(1 + x). -/
theorem continued_fraction (x : ℝ) (hx : 0 < x) : x = (1 - x) / x ↔ x = 1 / (1 + x) := by
  rw [self_similar_iff x hx, eq_div_iff (by linarith)]
  constructor <;> intro h <;> nlinarith [h]

/-- Theorem 19 — The golden ratio pre-collapse equilibrium. The only x in (0, 1) with
    x = (1 − x)/x is Ξ̄* = φ⁻¹ = (√5 − 1)/2. No other value is consistent. -/
theorem theorem19 (x : ℝ) (h0 : 0 < x) (hself : x = (1 - x) / x) : x = (Real.sqrt 5 - 1) / 2 := by
  have hq := (self_similar_iff x h0).mp hself
  have hfac : (x - (Real.sqrt 5 - 1) / 2) * (x + (Real.sqrt 5 + 1) / 2) = 0 := by
    have := sqrt5_sq
    nlinarith [hq, this]
  rcases mul_eq_zero.mp hfac with h | h
  · linarith
  · have : 0 < x + (Real.sqrt 5 + 1) / 2 := by linarith [one_lt_sqrt5]
    linarith

/-- And φ⁻¹ is that value: it satisfies x = (1 − x)/x. -/
theorem invPhi_self_similar : (Real.sqrt 5 - 1) / 2 = (1 - (Real.sqrt 5 - 1) / 2) / ((Real.sqrt 5 - 1) / 2) := by
  rw [self_similar_iff _ invPhi_in_unit.1]
  nlinarith [sqrt5_sq]

/-- φ⁻¹ is the inverse of the golden ratio. -/
theorem invPhi_eq : (Real.sqrt 5 - 1) / 2 = goldenRatio⁻¹ := by
  rw [inv_gold, goldenConj]
  ring

end UEF.Golden
