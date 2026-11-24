/-
  THE UNIFIED EXISTENCE FRAMEWORK — Chapter 19, in Lean 4 with Mathlib
  Ethical Consequences, Moral Geometry, and Toy Models

  Jake McDonough, Institute for Higher Thinking, Louisville, Kentucky, USA

  Source: UEF Release, 01_Manuscript.pdf, Chapter 19: 19.1 (moral geometry) and 19.4 (the dark
  matter ratio). All arithmetic is exact. No floating point anywhere.
-/
import Mathlib

open Real Matrix

namespace UEF.Moral

/-! ## 19.1 — moral geometry -/

/-- For normalized currents, c_ij = ⟨ŝ_i, ŝ_j⟩ lies in [−1, 1] by Cauchy–Schwarz. -/
theorem alignment_range {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (s t : E)
    (hs : ‖s‖ = 1) (ht : ‖t‖ = 1) : -1 ≤ @inner ℝ _ _ s t ∧ @inner ℝ _ _ s t ≤ 1 := by
  have := abs_real_inner_le_norm s t
  rw [hs, ht, mul_one] at this
  exact abs_le.mp this

/-- The misalignment energy of a coupled pair, E_ij = κ_ij(1 − cos θ_ij). -/
noncomputable def energy (κ θ : ℝ) : ℝ := κ * (1 - Real.cos θ)

/-- 0 ≤ E_ij ≤ 2κ_ij. -/
theorem energy_bounds (κ θ : ℝ) (hκ : 0 < κ) : 0 ≤ energy κ θ ∧ energy κ θ ≤ 2 * κ := by
  unfold energy
  have h1 := Real.cos_le_one θ
  have h2 := Real.neg_one_le_cos θ
  constructor <;> nlinarith

/-- E_ij = 0 exactly when θ_ij = 0, for θ ∈ [0, π]. -/
theorem energy_zero_iff (κ θ : ℝ) (hκ : 0 < κ) (h0 : 0 ≤ θ) (hπ : θ ≤ π) :
    energy κ θ = 0 ↔ θ = 0 := by
  unfold energy
  constructor
  · intro h
    have hc : Real.cos θ = 1 := by
      rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hκ.ne'
      · linarith
    by_contra hne
    have hpos : 0 < θ := lt_of_le_of_ne h0 (Ne.symm hne)
    have := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) hπ hpos
    rw [Real.cos_zero] at this
    linarith
  · rintro rfl
    simp

/-- dE_ij/dθ = κ_ij sin θ > 0 for 0 < θ < π: misalignment costs more the further it goes. -/
theorem energy_slope (κ θ : ℝ) (hκ : 0 < κ) (h0 : 0 < θ) (hπ : θ < π) :
    HasDerivAt (energy κ) (κ * Real.sin θ) θ ∧ 0 < κ * Real.sin θ :=
  ⟨(((Real.hasDerivAt_cos θ).const_sub 1).const_mul κ).congr_deriv (by ring),
    mul_pos hκ (Real.sin_pos_of_pos_of_lt_pi h0 hπ)⟩

/-- E_rel = Σ κ_ij(1 − c_ij) ≥ 0, and it is zero exactly when every coupled pair is aligned. -/
theorem network_least {ι : Type*} (s : Finset ι) (κ c : ι → ℝ) (hκ : ∀ p ∈ s, 0 < κ p)
    (hc : ∀ p ∈ s, c p ≤ 1) :
    0 ≤ ∑ p ∈ s, κ p * (1 - c p) ∧ (∑ p ∈ s, κ p * (1 - c p) = 0 ↔ ∀ p ∈ s, c p = 1) := by
  have hnn : ∀ p ∈ s, 0 ≤ κ p * (1 - c p) := fun p hp =>
    mul_nonneg (hκ p hp).le (by linarith [hc p hp])
  refine ⟨Finset.sum_nonneg hnn, ?_⟩
  rw [Finset.sum_eq_zero_iff_of_nonneg hnn]
  constructor
  · intro h p hp
    rcases mul_eq_zero.mp (h p hp) with h' | h'
    · exact absurd h' (hκ p hp).ne'
    · linarith
  · intro h p hp
    rw [h p hp]
    ring

/-- Gradient relaxation — δ(t) = δ(0)e^{−Mkt} solves dδ/dt = −Mkδ: the deviation dies away. -/
theorem deviation_decays (δ0 M k t : ℝ) :
    HasDerivAt (fun s => δ0 * Real.exp (-(M * k) * s)) (-(M * k) * (δ0 * Real.exp (-(M * k) * t))) t :=
  (((hasDerivAt_id t).const_mul (-(M * k))).exp.const_mul δ0).congr_deriv
    (by simp only [id_eq]; ring)

/-- ẋ = −M∇F with M ⪰ 0 gives dF/dt = ∇F · ẋ = −∇FᵀM∇F ≤ 0: F only falls. -/
theorem free_energy_falls {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosSemidef)
    (g : Fin n → ℝ) : g ⬝ᵥ (-(M *ᵥ g)) ≤ 0 := by
  have := hM.2 g
  simp only [star_trivial] at this
  rw [dotProduct_neg]
  linarith

/-- Holding a configuration still, −M(∇F − F_ext) = 0 with M invertible, takes F_ext = ∇F:
    maintaining a deviation from alignment always costs work. -/
theorem holding_costs_work {n : ℕ} (M Minv : Matrix (Fin n) (Fin n) ℝ) (hinv : Minv * M = 1)
    (g f : Fin n → ℝ) (still : -(M *ᵥ (g - f)) = 0) : f = g := by
  have h0 : M *ᵥ (g - f) = 0 := neg_eq_zero.mp still
  have : g - f = 0 := by
    calc g - f = (Minv * M) *ᵥ (g - f) := by rw [hinv, Matrix.one_mulVec]
      _ = Minv *ᵥ (M *ᵥ (g - f)) := (Matrix.mulVec_mulVec _ _ _).symm
      _ = 0 := by rw [h0, Matrix.mulVec_zero]
  exact (sub_eq_zero.mp this).symm

/-! ## 19.4 — the dark matter ratio -/

/-- With k/N → η = 14/89 the ratio is (1 − η)/η = 75/14. -/
theorem ratio_chapter19 : (1 - (14 : ℚ) / 89) / (14 / 89) = 75 / 14 := by norm_num

/-- 19.4 — the ratio matches Planck 2018: Ω_c h²/Ω_b h² = (120/1000)/(224/10000) = 75/14. -/
theorem planck_match : (1 - (14 : ℚ) / 89) / (14 / 89) = ((120 : ℚ) / 1000) / (224 / 10000) := by
  norm_num

end UEF.Moral
