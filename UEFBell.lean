/-
  THE UNIFIED EXISTENCE FRAMEWORK — A3.10 and E26, Bell, in Lean 4 with Mathlib

  Jake McDonough, Institute for Higher Thinking, Louisville, Kentucky, USA

  Source: UEF Release, 01_Manuscript.pdf, A3.10: "Under no-signaling and
  measurement independence, Bell-violating outcomes are produced by no
  predetermined strategy (E26)." Here E26 is proved, not cited.
-/
import Mathlib

open MeasureTheory Matrix

namespace UEF.Bell

/-! ## Every predetermined strategy obeys |S| ≤ 2 (CHSH) -/

/-- Four outcomes, each ±1: a·b + a·b′ + a′·b − a′·b′ is ±2. -/
theorem chsh_pointwise (a a' b b' : ℝ) (ha : a = 1 ∨ a = -1) (ha' : a' = 1 ∨ a' = -1)
    (hb : b = 1 ∨ b = -1) (hb' : b' = 1 ∨ b' = -1) :
    |a * b + a * b' + a' * b - a' * b'| ≤ 2 := by
  rcases ha with rfl | rfl <;> rcases ha' with rfl | rfl <;>
    rcases hb with rfl | rfl <;> rcases hb' with rfl | rfl <;> norm_num

section Local
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- A predetermined strategy: a hidden state λ, drawn from one law μ whatever the
    settings (measurement independence); each side's ±1 outcome depends only on its
    own setting and λ (no-signaling): A(a, λ), A(a′, λ), B(b, λ), B(b′, λ). -/
structure Strategy (Ω : Type*) [MeasurableSpace Ω] where
  A : Ω → ℝ
  A' : Ω → ℝ
  B : Ω → ℝ
  B' : Ω → ℝ
  mA : Measurable A
  mA' : Measurable A'
  mB : Measurable B
  mB' : Measurable B'
  sA : ∀ ω, A ω = 1 ∨ A ω = -1
  sA' : ∀ ω, A' ω = 1 ∨ A' ω = -1
  sB : ∀ ω, B ω = 1 ∨ B ω = -1
  sB' : ∀ ω, B' ω = 1 ∨ B' ω = -1

theorem pm_one_abs {x : ℝ} (h : x = 1 ∨ x = -1) : |x| = 1 := by
  rcases h with rfl | rfl <;> norm_num

theorem integrable_product (f g : Ω → ℝ) (mf : Measurable f) (mg : Measurable g)
    (sf : ∀ ω, f ω = 1 ∨ f ω = -1) (sg : ∀ ω, g ω = 1 ∨ g ω = -1) :
    Integrable (fun ω => f ω * g ω) μ :=
  (integrable_const (1 : ℝ)).mono' (mf.mul mg).aestronglyMeasurable
    (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_mul, pm_one_abs (sf ω), pm_one_abs (sg ω)]; norm_num)

/-- The CHSH value of a strategy: E(a,b) + E(a,b′) + E(a′,b) − E(a′,b′). -/
noncomputable def S (s : Strategy Ω) : ℝ :=
  (∫ ω, s.A ω * s.B ω ∂μ) + (∫ ω, s.A ω * s.B' ω ∂μ) + (∫ ω, s.A' ω * s.B ω ∂μ)
    - (∫ ω, s.A' ω * s.B' ω ∂μ)

/-- Bell–CHSH: every predetermined strategy has |S| ≤ 2. -/
theorem chsh (s : Strategy Ω) : |S μ s| ≤ 2 := by
  have i1 := integrable_product μ _ _ s.mA s.mB s.sA s.sB
  have i2 := integrable_product μ _ _ s.mA s.mB' s.sA s.sB'
  have i3 := integrable_product μ _ _ s.mA' s.mB s.sA' s.sB
  have i4 := integrable_product μ _ _ s.mA' s.mB' s.sA' s.sB'
  have e : S μ s = ∫ ω, (s.A ω * s.B ω + s.A ω * s.B' ω + s.A' ω * s.B ω - s.A' ω * s.B' ω) ∂μ := by
    have e1 : ∫ ω, (s.A ω * s.B ω + s.A ω * s.B' ω + s.A' ω * s.B ω - s.A' ω * s.B' ω) ∂μ
        = ∫ ω, (s.A ω * s.B ω + s.A ω * s.B' ω + s.A' ω * s.B ω) ∂μ - ∫ ω, s.A' ω * s.B' ω ∂μ :=
      integral_sub ((i1.add i2).add i3) i4
    have e2 : ∫ ω, (s.A ω * s.B ω + s.A ω * s.B' ω + s.A' ω * s.B ω) ∂μ
        = ∫ ω, (s.A ω * s.B ω + s.A ω * s.B' ω) ∂μ + ∫ ω, s.A' ω * s.B ω ∂μ :=
      integral_add (i1.add i2) i3
    have e3 : ∫ ω, (s.A ω * s.B ω + s.A ω * s.B' ω) ∂μ
        = ∫ ω, s.A ω * s.B ω ∂μ + ∫ ω, s.A ω * s.B' ω ∂μ := integral_add i1 i2
    unfold S
    rw [e1, e2, e3]
  rw [e, ← Real.norm_eq_abs]
  have := norm_integral_le_of_norm_le_const (μ := μ) (C := 2)
    (f := fun ω => s.A ω * s.B ω + s.A ω * s.B' ω + s.A' ω * s.B ω - s.A' ω * s.B' ω)
    (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs]; exact chsh_pointwise _ _ _ _ (s.sA ω) (s.sA' ω) (s.sB ω) (s.sB' ω))
  simpa using this

end Local

/-! ## The quantum correlations reach 2√2 -/

/-- The Pauli observables Z and X, each with outcomes ±1. -/
def Z : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]
def X : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

/-- The entangled state (|00⟩ + |11⟩)/√2, written unnormalised; ⟨ψ|ψ⟩ = 2. -/
def ψ : Fin 2 × Fin 2 → ℝ := fun p => if p.1 = p.2 then 1 else 0

/-- The correlation ⟨ψ| A ⊗ B |ψ⟩ / ⟨ψ|ψ⟩. -/
noncomputable def corr (A B : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  (ψ ⬝ᵥ ((Matrix.kroneckerMap (· * ·) A B) *ᵥ ψ)) / 2

theorem corr_ZZ : corr Z Z = 1 := by
  simp [corr, ψ, Z, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
    Matrix.kroneckerMap_apply]
theorem corr_XX : corr X X = 1 := by
  simp [corr, ψ, X, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
    Matrix.kroneckerMap_apply]
theorem corr_ZX : corr Z X = 0 := by
  simp [corr, ψ, Z, X, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
    Matrix.kroneckerMap_apply]
theorem corr_XZ : corr X Z = 0 := by
  simp [corr, ψ, Z, X, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
    Matrix.kroneckerMap_apply]

/-- The settings: A on Z or X; B on (Z + X)/√2 or (Z − X)/√2. -/
noncomputable def Bb : Matrix (Fin 2) (Fin 2) ℝ := (1 / Real.sqrt 2) • (Z + X)
noncomputable def Bb' : Matrix (Fin 2) (Fin 2) ℝ := (1 / Real.sqrt 2) • (Z - X)

/-- ⟨A ⊗ (Z ± X)/√2⟩ = (⟨A ⊗ Z⟩ ± ⟨A ⊗ X⟩)/√2, worked out entry by entry. -/
theorem corr_ZB : corr Z Bb = 1 / Real.sqrt 2 := by
  simp [corr, ψ, Z, X, Bb, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
    Matrix.kroneckerMap_apply]
theorem corr_ZB' : corr Z Bb' = 1 / Real.sqrt 2 := by
  simp [corr, ψ, Z, X, Bb', Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
    Matrix.kroneckerMap_apply]
theorem corr_XB : corr X Bb = 1 / Real.sqrt 2 := by
  simp [corr, ψ, Z, X, Bb, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
    Matrix.kroneckerMap_apply]
theorem corr_XB' : corr X Bb' = -(1 / Real.sqrt 2) := by
  simp [corr, ψ, Z, X, Bb', Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
    Matrix.kroneckerMap_apply]

/-- The quantum CHSH value is 2√2. -/
theorem quantum_S : corr Z Bb + corr Z Bb' + corr X Bb - corr X Bb' = 2 * Real.sqrt 2 := by
  rw [corr_ZB, corr_ZB', corr_XB, corr_XB']
  have h : Real.sqrt 2 ≠ 0 := by positivity
  field_simp
  rw [mul_assoc, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

theorem two_lt_quantum : 2 < 2 * Real.sqrt 2 := by
  have : 1 < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

/-- E26, A3.10 — Bell-violating outcomes are produced by no predetermined strategy:
    no strategy reproduces the four quantum correlations. -/
theorem no_predetermined_strategy {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (s : Strategy Ω)
    (h1 : ∫ ω, s.A ω * s.B ω ∂μ = corr Z Bb) (h2 : ∫ ω, s.A ω * s.B' ω ∂μ = corr Z Bb')
    (h3 : ∫ ω, s.A' ω * s.B ω ∂μ = corr X Bb) (h4 : ∫ ω, s.A' ω * s.B' ω ∂μ = corr X Bb') :
    False := by
  have hS := chsh μ s
  unfold S at hS
  rw [h1, h2, h3, h4, quantum_S, abs_of_pos (by positivity)] at hS
  linarith [two_lt_quantum]

end UEF.Bell
