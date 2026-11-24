/-
  THE UNIFIED EXISTENCE FRAMEWORK — Chapter 31, in Lean 4 with Mathlib
  ξ₇ — Integrability

  Jake McDonough, Institute for Higher Thinking, Louisville, Kentucky, USA

  Source: UEF Release, 01_Manuscript.pdf, Chapter 31, Parts I–II: the curvature inequality in
  three dimensions, the evolution of R, the volume bound, and the finite count of surgeries.
  ξ₇ is the integrability projection of the one condition Ξ = 0; its bridge is Theorem B.7.
  All arithmetic is exact. No floating point anywhere.
-/
import Mathlib

open Real

namespace UEF.Poincare

/-- Step 2 — in three dimensions (λ₁ + λ₂ + λ₃)² ≤ 3(λ₁² + λ₂² + λ₃²), so |Ric|² ≥ R²/3. -/
theorem ricci_bound (l1 l2 l3 : ℝ) : (l1 + l2 + l3) ^ 2 / 3 ≤ l1 ^ 2 + l2 ^ 2 + l3 ^ 2 := by
  nlinarith [sq_nonneg (l1 - l2), sq_nonneg (l2 - l3), sq_nonneg (l1 - l3)]

/-- Step 2 — ∂_t R = ΔR + 2|Ric|² with |Ric|² ≥ R²/3 gives ∂_t R ≥ ΔR + (2/3)R². -/
theorem scalar_evolution (dR lapR R Ric2 : ℝ) (h : dR = lapR + 2 * Ric2) (hRic : R ^ 2 / 3 ≤ Ric2) :
    lapR + 2 / 3 * R ^ 2 ≤ dR := by
  linarith

/-- Grönwall without a constant term — y′ ≤ ay with a ≥ 0 gives y(t) ≤ y(0)e^{at} for t ≥ 0. -/
theorem gronwall0 (y y' : ℝ → ℝ) (a : ℝ) (hy : ∀ t, HasDerivAt y (y' t) t)
    (hineq : ∀ t, y' t ≤ a * y t) (t : ℝ) (ht : 0 ≤ t) : y t ≤ y 0 * Real.exp (a * t) := by
  have hz : ∀ s, HasDerivAt (fun s => y s * Real.exp (-(a * s)))
      ((y' s - a * y s) * Real.exp (-(a * s))) s := by
    intro s
    have h1 : HasDerivAt (fun s => Real.exp (-(a * s))) (Real.exp (-(a * s)) * -(a * 1)) s :=
      ((hasDerivAt_id s).const_mul a).neg.exp
    exact ((hy s).mul h1).congr_deriv (by ring)
  have hanti := antitone_of_deriv_nonpos (fun s => (hz s).differentiableAt) (fun s => by
    rw [(hz s).deriv]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hineq s]) (Real.exp_pos _).le)
  have h := hanti ht
  dsimp only at h
  rw [mul_zero, neg_zero, Real.exp_zero, mul_one] at h
  have he : 0 < Real.exp (a * t) := Real.exp_pos _
  calc y t = y t * Real.exp (-(a * t)) * Real.exp (a * t) := by
        rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    _ ≤ y 0 * Real.exp (a * t) := mul_le_mul_of_nonneg_right h he.le

/-- Step 5 — dVol/dt = −∫R dV ≤ −R_min(0)Vol ≤ |R_min(0)|Vol keeps
    Vol(t) ≤ Vol(0)e^{|R_min(0)|t}. -/
theorem volume_bound (vol vol' : ℝ → ℝ) (Rmin : ℝ) (hv : ∀ t, HasDerivAt vol (vol' t) t)
    (hpos : ∀ t, 0 ≤ vol t) (hineq : ∀ t, vol' t ≤ -Rmin * vol t) (t : ℝ) (ht : 0 ≤ t) :
    vol t ≤ vol 0 * Real.exp (|Rmin| * t) := by
  refine gronwall0 vol vol' |Rmin| hv (fun s => ?_) t ht
  have h1 : -Rmin * vol s ≤ |Rmin| * vol s :=
    mul_le_mul_of_nonneg_right (neg_le_abs Rmin) (hpos s)
  linarith [hineq s]

/-- Step 5 — each surgery at scale at least h removes volume at least ch³, so a bounded volume
    allows at most Vol_max/(ch³) of them: finitely many. -/
theorem finitely_many_surgeries (N : ℕ) (c h Vmax : ℝ) (hc : 0 < c) (hh : 0 < h)
    (removed : N * (c * h ^ 3) ≤ Vmax) : (N : ℝ) ≤ Vmax / (c * h ^ 3) :=
  (le_div_iff₀ (by positivity)).mpr removed

end UEF.Poincare
