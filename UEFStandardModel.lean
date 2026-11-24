/-
  THE UNIFIED EXISTENCE FRAMEWORK — Chapter 11, the Standard Model as a projection, in Lean 4 with Mathlib

  Jake McDonough, Institute for Higher Thinking, Louisville, Kentucky, USA

  Source: UEF Release, 01_Manuscript.pdf, evidence Chapter 11: Theorem 1 and
  Corollaries 1.1–1.3 (the Higgs potential, vacuum, masses), Theorem 7
  (asymptotic freedom), Theorem 8 (the mass ratio mW/mZ = cos θW), Theorem 10
  (the Weyl count 6/2 = 3). The mathematics of each step is proved; the physical
  identifications (V_H ≡ πU(VΨ), the projected fields) are the manuscript's.
-/
import Mathlib

open Real Filter Topology

namespace UEF.StandardModel

/-! ## Theorem 1 — The Higgs potential: why the quadratic term must be negative -/

/-- V_H(ρ) = aρ² + bρ⁴ is bounded below (b > 0) and the realized vacuum is nonzero,
    ρ₀ > 0, so V_H′(ρ₀) = 2aρ₀ + 4bρ₀³ = 0. Then a = −2bρ₀² < 0, and with μ² = −a,
    λ = b, ρ₀² = μ²/2λ. -/
theorem quadratic_negative (a b ρ₀ : ℝ) (hb : 0 < b) (hρ : 0 < ρ₀)
    (vacuum : 2 * a * ρ₀ + 4 * b * ρ₀ ^ 3 = 0) :
    a = -2 * b * ρ₀ ^ 2 ∧ a < 0 ∧ ρ₀ ^ 2 = -a / (2 * b) := by
  have key : (a + 2 * b * ρ₀ ^ 2) * (2 * ρ₀) = 0 := by linear_combination vacuum
  have h1 : a + 2 * b * ρ₀ ^ 2 = 0 := by
    rcases mul_eq_zero.mp key with h | h
    · exact h
    · linarith
  have hpos : 0 < b * ρ₀ ^ 2 := mul_pos hb (pow_pos hρ 2)
  refine ⟨by linarith, by linarith, ?_⟩
  rw [eq_div_iff (by positivity)]
  linear_combination h1

/-! ## Corollary 1.1 — The vacuum expectation value -/

/-- V_H = −μ²|φ|² + λ|φ|⁴, written in ρ = |φ|. -/
noncomputable def VH (μ2 lam ρ : ℝ) : ℝ := -μ2 * ρ ^ 2 + lam * ρ ^ 4

/-- V_H(ρ) = −μ⁴/4λ + λ(ρ² − μ²/2λ)². -/
theorem VH_complete_square (μ2 lam ρ : ℝ) (hl : 0 < lam) :
    VH μ2 lam ρ = -(μ2 ^ 2) / (4 * lam) + lam * (ρ ^ 2 - μ2 / (2 * lam)) ^ 2 := by
  unfold VH
  field_simp
  ring

/-- dV_H/d|φ| = 0 ⟹ |φ|² = μ²/2λ: that is where V_H is least. -/
theorem vacuum_is_minimum (μ2 lam ρ σ : ℝ) (hl : 0 < lam) (hσ : σ ^ 2 = μ2 / (2 * lam)) :
    VH μ2 lam σ ≤ VH μ2 lam ρ := by
  rw [VH_complete_square μ2 lam ρ hl, VH_complete_square μ2 lam σ hl, hσ, sub_self]
  have : 0 ≤ lam * (ρ ^ 2 - μ2 / (2 * lam)) ^ 2 := mul_nonneg hl.le (sq_nonneg _)
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero]
  linarith

/-- The vacuum is nonzero exactly when μ² > 0: then |φ|² = μ²/2λ > 0. -/
theorem vacuum_nonzero (μ2 lam : ℝ) (hl : 0 < lam) : 0 < μ2 / (2 * lam) ↔ 0 < μ2 := by
  constructor
  · intro h; by_contra h'; push_neg at h'
    have : μ2 / (2 * lam) ≤ 0 := div_nonpos_of_nonpos_of_nonneg h' (by positivity)
    linarith
  · intro h; positivity

/-- v = μ/√λ gives |φ|² = μ²/2λ = v²/2. -/
theorem v_squared (μ lam : ℝ) (hl : 0 < lam) : (μ / Real.sqrt lam) ^ 2 / 2 = μ ^ 2 / (2 * lam) := by
  rw [div_pow, Real.sq_sqrt hl.le]
  ring

/-! ## Corollary 1.2 — Mass generation -/

/-- m_F = g_F · v/√2 = g_F · μ/√(2λ). -/
theorem fermion_mass (gF μ lam : ℝ) :
    gF * ((μ / Real.sqrt lam) / Real.sqrt 2) = gF * (μ / Real.sqrt (2 * lam)) := by
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), div_div, mul_comm (Real.sqrt lam)]

/-! ## Corollary 1.3 — The Higgs boson mass -/

/-- V_H(h) = −(μ²/2)(v + h)² + (λ/4)(v + h)⁴, with φ = (v + h)/√2. -/
noncomputable def Vh (μ2 lam v h : ℝ) : ℝ := -(μ2 / 2) * (v + h) ^ 2 + (lam / 4) * (v + h) ^ 4

theorem Vh_deriv (μ2 lam v h : ℝ) :
    HasDerivAt (fun h => Vh μ2 lam v h) (-μ2 * (v + h) + lam * (v + h) ^ 3) h := by
  have h1 : HasDerivAt (fun h => v + h) 1 h := (hasDerivAt_id h).const_add v
  have := ((h1.pow 2).const_mul (-(μ2 / 2))).add ((h1.pow 4).const_mul (lam / 4))
  convert this using 1
  push_cast
  ring

theorem Vh_deriv2 (μ2 lam v h : ℝ) :
    HasDerivAt (fun h => -μ2 * (v + h) + lam * (v + h) ^ 3) (-μ2 + 3 * lam * (v + h) ^ 2) h := by
  have h1 : HasDerivAt (fun h => v + h) 1 h := (hasDerivAt_id h).const_add v
  have := (h1.const_mul (-μ2)).add ((h1.pow 3).const_mul lam)
  convert this using 1
  push_cast
  ring

/-- d²V_H/dh² at h = 0 is −μ² + 3λv² = −μ² + 3μ² = 2μ², so m_H = √2 μ. -/
theorem higgs_mass (μ lam v : ℝ) (hμ : 0 ≤ μ) (hv : lam * v ^ 2 = μ ^ 2) :
    -μ ^ 2 + 3 * lam * (v + 0) ^ 2 = 2 * μ ^ 2 ∧ Real.sqrt (2 * μ ^ 2) = Real.sqrt 2 * μ := by
  refine ⟨by rw [add_zero, mul_assoc, hv]; ring, ?_⟩
  rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hμ]

/-- m_H = 12520/100 GeV gives μ = m_H/√2 = (313/5)√2 GeV. -/
theorem mu_value : (12520 / 100 : ℝ) / Real.sqrt 2 = (313 / 5) * Real.sqrt 2 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [div_eq_iff (by positivity), mul_assoc, h2]
  norm_num

/-- With v = 24622/100 GeV, λ = m_H²/2v² = 19593800/151560721. -/
theorem lambda_value : (12520 / 100 : ℝ) ^ 2 / (2 * (24622 / 100) ^ 2) = 19593800 / 151560721 := by
  norm_num

/-! ## Theorem 7 — Asymptotic freedom -/

/-- β₀ = (11/3)C_A − (4/3)T_F n_f. -/
noncomputable def β₀ (CA TF nf : ℝ) : ℝ := 11 / 3 * CA - 4 / 3 * TF * nf

/-- For SU(3), C_A = 3 and T_F = 1/2: β₀ = 11 − (2/3)n_f; with six flavours β₀ = 7 > 0. -/
theorem β₀_SU3 (nf : ℝ) : β₀ 3 (1 / 2) nf = 11 - 2 / 3 * nf ∧ β₀ 3 (1 / 2) 6 = 7 := by
  unfold β₀; constructor <;> ring

/-- gs²(μ) = gs²(μ₀) / [1 + (gs²(μ₀)β₀/8π²) ln(μ/μ₀)]. -/
noncomputable def gs2 (g0 b μ0 μ : ℝ) : ℝ := g0 / (1 + g0 * b / (8 * π ^ 2) * Real.log (μ / μ0))

/-- gs(μ) → 0 as μ → ∞: asymptotic freedom (Step 11). -/
theorem asymptotic_freedom (g0 b μ0 : ℝ) (hg : 0 < g0) (hb : 0 < b) (hμ0 : 0 < μ0) :
    Tendsto (fun μ => gs2 g0 b μ0 μ) atTop (𝓝 0) := by
  have hlog : Tendsto (fun μ => Real.log (μ / μ0)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_id.atTop_div_const hμ0)
  have hc : 0 < g0 * b / (8 * π ^ 2) := by positivity
  have hden : Tendsto (fun μ => 1 + g0 * b / (8 * π ^ 2) * Real.log (μ / μ0)) atTop atTop :=
    tendsto_atTop_add_const_left _ 1 (hlog.const_mul_atTop hc)
  have := (hden.inv_tendsto_atTop).const_mul g0
  simpa [gs2, div_eq_mul_inv] using this

/-- The denominator reaches zero at Λ_QCD = μ₀ exp(−8π²/(β₀ gs²(μ₀))) (Step 12). -/
theorem lambda_QCD (g0 b μ0 : ℝ) (hg : 0 < g0) (hb : 0 < b) (hμ0 : 0 < μ0) :
    1 + g0 * b / (8 * π ^ 2) * Real.log (μ0 * Real.exp (-(8 * π ^ 2) / (b * g0)) / μ0) = 0 := by
  rw [mul_div_cancel_left₀ _ hμ0.ne', Real.log_exp]
  have : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-! ## Theorem 8 — Electroweak unification and the Weinberg angle -/

/-- m_W = (1/2) g v, m_Z = (1/2)√(g² + g′²) v, so m_W/m_Z = g/√(g² + g′²) = 1/√(1 + tan²θ_W)
    = cos θ_W, with tan θ_W = g′/g. -/
theorem mass_ratio (g g' v : ℝ) (hg : 0 < g) (hv : 0 < v) :
    (1 / 2 * g * v) / (1 / 2 * Real.sqrt (g ^ 2 + g' ^ 2) * v) = g / Real.sqrt (g ^ 2 + g' ^ 2) ∧
      g / Real.sqrt (g ^ 2 + g' ^ 2) = 1 / Real.sqrt (1 + (g' / g) ^ 2) := by
  have hs : 0 < Real.sqrt (g ^ 2 + g' ^ 2) := Real.sqrt_pos.mpr (by positivity)
  constructor
  · field_simp
    ring
  · have e : 1 + (g' / g) ^ 2 = (g ^ 2 + g' ^ 2) / g ^ 2 := by field_simp
    rw [e, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hg.le]
    field_simp

/-- tan²θ_W = sin²θ_W/(1 − sin²θ_W): with sin²θ_W = 23129/100000, the value Theorem 8 states,
    this is 23129/76871, the value in Step 8. -/
theorem tan_sq_value : (23129 / 100000 : ℝ) / (1 - 23129 / 100000) = 23129 / 76871 := by
  norm_num

/-! ## Theorem 10 — The Weyl count -/

/-- χ(SU(3)/U(2)) = |W(SU(3))| / |W(U(2))| = 6/2 = 3, with W(SU(3)) = S₃ and W(U(2)) = S₂. -/
theorem weyl_count :
    Fintype.card (Equiv.Perm (Fin 3)) = 6 ∧ Fintype.card (Equiv.Perm (Fin 2)) = 2 ∧
      Fintype.card (Equiv.Perm (Fin 3)) / Fintype.card (Equiv.Perm (Fin 2)) = 3 := by
  simp [Fintype.card_perm, Nat.factorial]

end UEF.StandardModel
