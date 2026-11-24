/-
  THE UNIFIED EXISTENCE FRAMEWORK — Chapters 33 and 34, in Lean 4 with Mathlib
  Ten Falsifiable Predictions; Structural Soundness Tests

  Jake McDonough, Institute for Higher Thinking, Louisville, Kentucky, USA

  Source: UEF Release, 01_Manuscript.pdf, Chapter 33 (F1–F10 and the table of 33.12) and
  Chapter 34 (34.2 Landauer, 34.3 Turing). Every number is checked in exact arithmetic; the
  Jarlskog invariant of F10 is bounded with exact rational bounds on sin and √.
  No floating point anywhere.
-/
import Mathlib

namespace UEF.Predictions

/-! ## Chapter 33 — the ten predictions -/

/-- F1 — the measured exponent −4000/1000 is exactly −4, the d − 2 = 4 of six dimensions. -/
theorem F1 : (-4000 : ℚ) / 1000 = -4 ∧ (6 : ℤ) - 2 = 4 := by norm_num

/-- F2 — m_H = 12520/100 GeV fixes μ = m_H/√2 = (313/5)√2 GeV: ((313/5)√2)·√2 = 12520/100. -/
theorem F2 : (313 / 5 : ℝ) * Real.sqrt 2 * Real.sqrt 2 = 12520 / 100 := by
  rw [mul_assoc, Real.mul_self_sqrt (by norm_num)]
  norm_num

/-- F3 — sin²θ_W = 23129/100000 gives tan²θ_W = 23129/76871. -/
theorem F3 : (23129 / 100000 : ℚ) / (1 - 23129 / 100000) = 23129 / 76871 := by norm_num

/-- F4 — Planck 2018's ratio 75/14 fixes η = 14/89. -/
theorem F4 : (1 - (14 : ℚ) / 89) / (14 / 89) = 75 / 14 := by norm_num

/-- F4 as stated in 34 and in the table of 33.12: 75/14 at collapse efficiency η = 14/89, the
    Planck 2018 ratio Ω_c h²/Ω_b h². -/
theorem F4_F5 : (1 - (14 : ℚ) / 89) / (14 / 89) = 75 / 14 ∧
    ((120 : ℚ) / 1000) / (224 / 10000) = 75 / 14 := by
  norm_num

/-- F5 — LEP's (29963 ± 74)/10000 lies half a standard deviation from 3. -/
theorem F5 : (3 - (29963 : ℚ) / 10000) / (74 / 10000) = 1 / 2 := by norm_num

/-- F9 — β₀ = 11 − (2/3)n_f: 23/3 at the Z mass (n_f = 5), 7 above the top threshold (n_f = 6). -/
theorem F9 : (11 : ℚ) - 2 / 3 * 5 = 23 / 3 ∧ (11 : ℚ) - 2 / 3 * 6 = 7 := by norm_num

/-- F10 — first-row unitarity (9984 ± 7)/10000 lies 16/7 σ below 1. -/
theorem F10_unitarity : (1 - (9984 : ℚ) / 10000) / (7 / 10000) = 16 / 7 := by norm_num

/-- Monotonicity of a four-factor product with non-negative factors, for the lower bound. -/
theorem prod_lower (A B K S C A0 B0 S0 C0 : ℝ) (hA0 : A0 ≤ A) (hB0 : B0 ≤ B) (hS0 : S0 ≤ S)
    (hC0 : C0 ≤ C) (pA0 : 0 ≤ A0) (pB0 : 0 ≤ B0) (pS0 : 0 ≤ S0) (pC0 : 0 ≤ C0) (pK : 0 ≤ K) :
    A0 * B0 * K * (2 * (S0 * C0)) ≤ A * B * K * (2 * (S * C)) := by
  have hA : 0 ≤ A := pA0.trans hA0
  have hB : 0 ≤ B := pB0.trans hB0
  have hS : 0 ≤ S := pS0.trans hS0
  have h1 : A0 * B0 ≤ A * B := mul_le_mul hA0 hB0 pB0 hA
  have h2 : S0 * C0 ≤ S * C := mul_le_mul hS0 hC0 pC0 hS
  have h3 : A0 * B0 * K ≤ A * B * K := mul_le_mul_of_nonneg_right h1 pK
  have h4 : 2 * (S0 * C0) ≤ 2 * (S * C) := by linarith
  have h5 : 0 ≤ 2 * (S0 * C0) := by have := mul_nonneg pS0 pC0; linarith
  exact mul_le_mul h3 h4 h5 (mul_nonneg (mul_nonneg hA hB) pK)

/-- The same product, for the upper bound. -/
theorem prod_upper (A B K S C S1 C1 : ℝ) (hA : A ≤ 1) (hB : B ≤ 1) (pA : 0 ≤ A) (pB : 0 ≤ B)
    (hS1 : S ≤ S1) (hC1 : C ≤ C1) (pS : 0 ≤ S) (pC : 0 ≤ C) (pK : 0 ≤ K) :
    A * B * K * (2 * (S * C)) ≤ 1 * 1 * K * (2 * (S1 * C1)) := by
  have h1 : A * B ≤ 1 * 1 := mul_le_mul hA hB pB zero_le_one
  have h2 : S * C ≤ S1 * C1 := mul_le_mul hS1 hC1 pC (pS.trans hS1)
  have h3 : A * B * K ≤ 1 * 1 * K := mul_le_mul_of_nonneg_right h1 pK
  have h4 : 2 * (S * C) ≤ 2 * (S1 * C1) := by linarith
  have h5 : 0 ≤ 2 * (S * C) := by have := mul_nonneg pS pC; linarith
  exact mul_le_mul h3 h4 h5 (by norm_num [pK])

/-- F10 — J = c₁₂c₂₃c₁₃²s₁₂s₂₃s₁₃ sin δ with s₁₂ = 22501/100000, s₂₃ = 4183/100000,
    s₁₃ = 3732/1000000 and δ = 1147/1000 lies inside the measured (312 + 13 − 12) × 10⁻⁷:
    300 × 10⁻⁷ ≤ J ≤ 325 × 10⁻⁷. -/
theorem F10_jarlskog :
    (300 : ℝ) / 10 ^ 7 ≤ Real.sqrt (1 - (22501 / 100000) ^ 2) * Real.sqrt (1 - (4183 / 100000) ^ 2)
        * ((1 - (3732 / 1000000) ^ 2) * (22501 / 100000) * (4183 / 100000) * (3732 / 1000000))
        * Real.sin (1147 / 1000) ∧
      Real.sqrt (1 - (22501 / 100000) ^ 2) * Real.sqrt (1 - (4183 / 100000) ^ 2)
        * ((1 - (3732 / 1000000) ^ 2) * (22501 / 100000) * (4183 / 100000) * (3732 / 1000000))
        * Real.sin (1147 / 1000) ≤ (325 : ℝ) / 10 ^ 7 := by
  have hy : |(1147 : ℝ) / 2000| ≤ 1 := by
    rw [abs_of_pos (by norm_num)]
    norm_num
  have sb := abs_le.mp (Real.sin_bound hy)
  have cb := abs_le.mp (Real.cos_bound hy)
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1147 / 2000)] at sb cb
  have h2 : Real.sin (1147 / 1000) = 2 * (Real.sin (1147 / 2000) * Real.cos (1147 / 2000)) := by
    rw [← mul_assoc, ← Real.sin_two_mul]
    norm_num
  have hS0 : (1147 / 2000 - (1147 / 2000) ^ 3 / 6 - (1147 / 2000) ^ 4 * (5 / 96) : ℝ)
      ≤ Real.sin (1147 / 2000) := by linarith [sb.1]
  have hS1 : Real.sin (1147 / 2000)
      ≤ (1147 / 2000 - (1147 / 2000) ^ 3 / 6 + (1147 / 2000) ^ 4 * (5 / 96) : ℝ) := by
    linarith [sb.2]
  have hC0 : (1 - (1147 / 2000) ^ 2 / 2 - (1147 / 2000) ^ 4 * (5 / 96) : ℝ)
      ≤ Real.cos (1147 / 2000) := by linarith [cb.1]
  have hC1 : Real.cos (1147 / 2000)
      ≤ (1 - (1147 / 2000) ^ 2 / 2 + (1147 / 2000) ^ 4 * (5 / 96) : ℝ) := by linarith [cb.2]
  have hA0 : (97435 / 100000 : ℝ) ≤ Real.sqrt (1 - (22501 / 100000) ^ 2) :=
    calc (97435 / 100000 : ℝ) = Real.sqrt ((97435 / 100000) ^ 2) :=
          (Real.sqrt_sq (by norm_num)).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by norm_num)
  have hB0 : (9991 / 10000 : ℝ) ≤ Real.sqrt (1 - (4183 / 100000) ^ 2) :=
    calc (9991 / 10000 : ℝ) = Real.sqrt ((9991 / 10000) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by norm_num)
  have hA1 : Real.sqrt (1 - (22501 / 100000 : ℝ) ^ 2) ≤ 1 :=
    (Real.sqrt_le_sqrt (by norm_num)).trans_eq Real.sqrt_one
  have hB1 : Real.sqrt (1 - (4183 / 100000 : ℝ) ^ 2) ≤ 1 :=
    (Real.sqrt_le_sqrt (by norm_num)).trans_eq Real.sqrt_one
  have pS0 : (0 : ℝ) ≤ 1147 / 2000 - (1147 / 2000) ^ 3 / 6 - (1147 / 2000) ^ 4 * (5 / 96) := by
    norm_num
  have pC0 : (0 : ℝ) ≤ 1 - (1147 / 2000) ^ 2 / 2 - (1147 / 2000) ^ 4 * (5 / 96) := by norm_num
  have pK : (0 : ℝ) ≤ (1 - (3732 / 1000000) ^ 2) * (22501 / 100000) * (4183 / 100000)
      * (3732 / 1000000) := by norm_num
  rw [h2]
  constructor
  · refine le_trans ?_ (prod_lower _ _ _ _ _ _ _ _ _ hA0 hB0 hS0 hC0 (by norm_num) (by norm_num)
      pS0 pC0 pK)
    norm_num
  · refine le_trans (prod_upper _ _ _ _ _ _ _ hA1 hB1 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      hS1 hC1 (pS0.trans hS0) (pC0.trans hC0) pK) ?_
    norm_num

/-! ## Chapter 34 — structural soundness -/

/-- 34.2 Landauer — erasing one bit costs at least k_B T ln 2, so N erased bits cost at least
    N k_B T ln 2. -/
theorem landauer (N : ℕ) (cost : Fin N → ℝ) (kT : ℝ) (h : ∀ i, kT * Real.log 2 ≤ cost i) :
    N * (kT * Real.log 2) ≤ ∑ i, cost i := by
  have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => h i
  simpa using this

/-- 34.2 — ΔS_total = ΔS_system + ΔS_observer ≥ 0 when the observer absorbs at least what the
    system sheds. -/
theorem entropy_balance (dSsys dSobs : ℝ) (h : -dSsys ≤ dSobs) : 0 ≤ dSsys + dSobs := by linarith

/-- 34.3 Turing — a computable sequence cannot be Martin-Löf random: K(X↾n) ≥ n − c₀ and
    K(X↾n) ≤ |P| + f(n) cannot both hold at an n with |P| + f(n) + c₀ < n. -/
theorem turing (K n c0 P f : ℝ) (random : n - c0 ≤ K) (computable : K ≤ P + f)
    (large : P + f + c0 < n) : False := by linarith

end UEF.Predictions
