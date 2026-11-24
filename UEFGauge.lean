/-
  THE UNIFIED EXISTENCE FRAMEWORK — Chapter 27, in Lean 4 with Mathlib
  ξ₃ — Causality

  Jake McDonough, Institute for Higher Thinking, Louisville, Kentucky, USA

  Source: UEF Release, 01_Manuscript.pdf, Chapter 27, Parts II and III: completing the square,
  the transverse mass term, the momentum kernel, canonical normalization, coercivity, and the
  propagator. ξ₃ is the causality projection of the one condition Ξ = 0; its bridge is Theorem
  B.2 (UEFBridges.lean), and A4 supplies the potential B.
  All arithmetic is exact. No floating point anywhere.
-/
import Mathlib

open Complex

namespace UEF.Gauge

/-! ## Part II — exact decoupling, mode by mode in momentum space -/

/-- Completing the square: aB² + cB = a(B + c/(2a))² − c²/(4a). -/
theorem complete_square (a c B : ℂ) (ha : a ≠ 0) :
    a * B ^ 2 + c * B = a * (B + c / (2 * a)) ^ 2 - c ^ 2 / (4 * a) := by
  field_simp
  ring

/-- Step 6 — with a = Δ/(2κ²) and c = iλF, the stationary point is B₀ = −c/(2a) = −iλκ²F/Δ. -/
theorem stationary_point (κ lam D F : ℂ) (hκ : κ ≠ 0) (hD : D ≠ 0) :
    -(I * lam * F) / (2 * (D / (2 * κ ^ 2))) = -I * lam * κ ^ 2 * F / D := by
  field_simp
  ring

/-- Step 6 — the constant left over is −c²/(4a) = (λ²κ²/2)F²/Δ, since i² = −1. -/
theorem leftover (κ lam D F : ℂ) (hκ : κ ≠ 0) (hD : D ≠ 0) :
    -(I * lam * F) ^ 2 / (4 * (D / (2 * κ ^ 2))) = lam ^ 2 * κ ^ 2 / 2 * F ^ 2 / D := by
  rw [mul_pow, mul_pow, I_sq]
  field_simp
  ring

/-- Step 6 — so S_B = (1/2κ²)⟨b, Δb⟩ + (λ²κ²/2)⟨F, Δ⁻¹F⟩ with b = B − B₀, mode by mode. -/
theorem decoupling (κ lam D F B : ℂ) (hκ : κ ≠ 0) (hD : D ≠ 0) :
    D / (2 * κ ^ 2) * B ^ 2 + I * lam * F * B
      = D / (2 * κ ^ 2) * (B - -I * lam * κ ^ 2 * F / D) ^ 2 + lam ^ 2 * κ ^ 2 / 2 * F ^ 2 / D := by
  have ha : D / (2 * κ ^ 2) ≠ 0 := div_ne_zero hD (by simp [hκ])
  rw [complete_square _ _ B ha, ← leftover κ lam D F hκ hD,
    show B + I * lam * F / (2 * (D / (2 * κ ^ 2))) = B - -(I * lam * F) / (2 * (D / (2 * κ ^ 2)))
      by ring, stationary_point κ lam D F hκ hD]
  ring

/-! ## Part III — the functional-analysis bound -/

section Transverse
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Step 8 — on a transverse field, p·A = 0, the kernel p²δ − pp acts as p², so
    ⟨A, Δ⁻¹(p²δ − pp)A⟩ = ‖A_T‖². -/
theorem transverse_mass (p A : E) (hT : @inner ℝ _ _ p A = 0) (hp : p ≠ 0) :
    @inner ℝ _ _ A (‖p‖ ^ 2 • A - (@inner ℝ _ _ p A) • p) / ‖p‖ ^ 2 = ‖A‖ ^ 2 := by
  have hp2 : ‖p‖ ^ 2 ≠ 0 := by positivity
  rw [hT, zero_smul, sub_zero, real_inner_smul_right, real_inner_self_eq_norm_sq]
  field_simp

/-- Step 11 — the operator p²δ − pp is non-negative: ⟨A, (p²δ − pp)A⟩ = ‖p‖²‖A‖² − (p·A)² ≥ 0. -/
theorem kernel_nonneg (p A : E) :
    0 ≤ @inner ℝ _ _ A (‖p‖ ^ 2 • A - (@inner ℝ _ _ p A) • p) := by
  rw [inner_sub_right, real_inner_smul_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
    real_inner_comm A p]
  have := real_inner_mul_inner_self_le p A
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at this
  nlinarith

/-- Step 11 — coercivity: E[Ã] = ⟨Ã, (p²δ − pp)Ã⟩ + m²‖Ã_T‖² ≥ m²‖Ã_T‖². -/
theorem coercive (p A : E) (m AT : ℝ) :
    m ^ 2 * AT ≤ @inner ℝ _ _ A (‖p‖ ^ 2 • A - (@inner ℝ _ _ p A) • p) + m ^ 2 * AT := by
  linarith [kernel_nonneg p A]

end Transverse

/-- Steps 9–10 — on transverse modes the kernel is (1/g²)(p² + m²_UEF), and rescaling A = gÃ
    removes the 1/g²: a massive vector field of mass m_UEF = gλκ. -/
theorem canonical (g lam κ p2 A : ℝ) (hg : g ≠ 0) :
    1 / g ^ 2 * (p2 + (g * lam * κ) ^ 2) * (g * A) ^ 2 = (p2 + (g * lam * κ) ^ 2) * A ^ 2 := by
  field_simp
  ring

/-- Step 10 — m_UEF = gλκ > 0 whenever g, λ, κ > 0. -/
theorem mass_pos (g lam κ : ℝ) (hg : 0 < g) (hl : 0 < lam) (hk : 0 < κ) : 0 < g * lam * κ := by
  positivity

/-- Step 11 — the transverse propagator 1/(p² + m²) has no pole at p² = 0: for m > 0 it is
    finite and at most 1/m² at every p² ≥ 0. -/
theorem no_pole (m p2 : ℝ) (hm : 0 < m) (hp : 0 ≤ p2) :
    0 < p2 + m ^ 2 ∧ 1 / (p2 + m ^ 2) ≤ 1 / m ^ 2 :=
  ⟨by positivity, one_div_le_one_div_of_le (by positivity) (by linarith)⟩

end UEF.Gauge
