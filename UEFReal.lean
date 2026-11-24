/-
  THE UNIFIED EXISTENCE FRAMEWORK — the lines over the real numbers, in Lean 4 with Mathlib

  Jake McDonough, Institute for Higher Thinking, Louisville, Kentucky, USA

  Source: UEF Release, 01_Manuscript.pdf and S8_One_Equation_Compression.pdf,
  each line with its section, page and line. Together with UEF.lean this is the
  one equation.
-/
import Mathlib

open Real Finset MeasureTheory

namespace UEF.Reals

/-! ## §5.3 — The integrated transport form (p. 127, ll. 2742–2748) -/

section Transport
variable {ι : Type*} (ℰ : Finset ι) (w : ι → ℕ)

/-- δ_Δ := log w_Δ. -/
noncomputable def δ (Δ : ι) : ℝ := Real.log (w Δ)

/-- w_Δ := [Λ:Δ(Λ)] ≥ 1, δ_Δ := log w_Δ ≥ 0. -/
theorem δ_nonneg (hw : ∀ Δ, 1 ≤ w Δ) (Δ : ι) : 0 ≤ δ w Δ :=
  Real.log_nonneg (by exact_mod_cast hw Δ)

/-- w_{Δ₁∘Δ₂} = w_{Δ₁}w_{Δ₂} ⟹ δ_{Δ₁∘Δ₂} = δ_{Δ₁} + δ_{Δ₂}. -/
theorem δ_compose (a b c : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : c = a * b) :
    Real.log c = Real.log a + Real.log b := by
  subst hc
  push_cast
  exact Real.log_mul (by positivity) (by positivity)

/-- ∏_{Δ∈ℰ} w_Δ = exp(Σ_{Δ∈ℰ} δ_Δ). -/
theorem prod_eq_exp_sum (hw : ∀ Δ, 1 ≤ w Δ) :
    (∏ Δ ∈ ℰ, (w Δ : ℝ)) = Real.exp (∑ Δ ∈ ℰ, δ w Δ) := by
  rw [Real.exp_sum]
  refine Finset.prod_congr rfl fun Δ _ => ?_
  have : (0 : ℝ) < w Δ := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (hw Δ)
  exact (Real.exp_log this).symm

/-- ∏_{Δ∈ℰ}w_Δ=1 ⇔ Σδ_Δ=0 ⇔ ∀Δ:δ_Δ=0.   (§5.3, p. 127, l. 2748) -/
theorem transport (hw : ∀ Δ, 1 ≤ w Δ) :
    ((∏ Δ ∈ ℰ, (w Δ : ℝ)) = 1 ↔ ∑ Δ ∈ ℰ, δ w Δ = 0) ∧
    (∑ Δ ∈ ℰ, δ w Δ = 0 ↔ ∀ Δ ∈ ℰ, δ w Δ = 0) ∧
    ((∀ Δ ∈ ℰ, δ w Δ = 0) ↔ ∀ Δ ∈ ℰ, w Δ = 1) := by
  refine ⟨?_, Finset.sum_eq_zero_iff_of_nonneg fun Δ _ => δ_nonneg w hw Δ, ?_⟩
  · rw [prod_eq_exp_sum ℰ w hw, Real.exp_eq_one_iff]
  · refine forall₂_congr fun Δ _ => ?_
    constructor
    · intro h
      have h1 : (1 : ℝ) ≤ w Δ := by exact_mod_cast hw Δ
      rcases Real.log_eq_zero.mp h with h0 | h0 | h0
      · linarith
      · exact_mod_cast h0
      · linarith
    · intro h
      simp [δ, h]

end Transport

/-! ## Evidence §8.6 — Proposition 8.6: the approach to Ξ = 0 -/

section Approach

/-- VK(Ξ) = ΞᵀΞ = Σᵢ ξᵢ², every channel counted equally.   (evidence §8.6, p. 161, l. 3487) -/
def VK (Ξ : Fin 7 → ℝ) : ℝ := ∑ i, Ξ i ^ 2

theorem VK_zero_iff (Ξ : Fin 7 → ℝ) : VK Ξ = 0 ↔ Ξ = 0 := by
  unfold VK
  rw [Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (Ξ i)]
  constructor
  · intro h; funext i; exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (h i (mem_univ i))
  · intro h i _; simp [h]

/-- dVK/dt = 2ΞᵀG(Ξ): along the flow dξᵢ/dt = Gᵢ(Ξ).   (evidence §8.6, p. 161, l. 3489) -/
theorem dVK (Ξ : ℝ → Fin 7 → ℝ) (G : (Fin 7 → ℝ) → Fin 7 → ℝ) (t : ℝ)
    (flow : ∀ i, HasDerivAt (fun s => Ξ s i) (G (Ξ t) i) t) :
    HasDerivAt (fun s => VK (Ξ s)) (2 * ∑ i, Ξ t i * G (Ξ t) i) t := by
  unfold VK
  have h : ∀ i ∈ (univ : Finset (Fin 7)),
      HasDerivAt (fun s => Ξ s i ^ 2) (2 * Ξ t i * G (Ξ t) i) t := by
    intro i _
    have := (flow i).pow 2
    simpa [mul_comm, mul_assoc, mul_left_comm] using this
  have hs := HasDerivAt.sum h
  convert hs using 1
  · funext s; simp
  · rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; ring

/-- VK(t) ≤ VK(t₀) e^{−γ(t − t₀)}.   (evidence §8.6, p. 161, l. 3492)
    When the K7 flow satisfies ΞᵀG(Ξ) ≤ −(γ/2)ΞᵀΞ for some γ > 0, this gives
    dVK/dt ≤ −γVK, so d/dt[e^{γt}VK] ≤ 0. -/
theorem decay (V V' : ℝ → ℝ) (γ : ℝ) (hV : ∀ t, HasDerivAt V (V' t) t)
    (hdec : ∀ t, V' t ≤ -γ * V t) {t₀ t : ℝ} (ht : t₀ ≤ t) :
    V t ≤ V t₀ * Real.exp (-(γ * (t - t₀))) := by
  set f : ℝ → ℝ := fun s => Real.exp (γ * s) * V s with hf
  have hderiv : ∀ s, HasDerivAt f (Real.exp (γ * s) * (γ * V s + V' s)) s := by
    intro s
    have h1 : HasDerivAt (fun s => Real.exp (γ * s)) (Real.exp (γ * s) * γ) s := by
      simpa using ((hasDerivAt_id s).const_mul γ).exp
    convert h1.mul (hV s) using 1
    ring
  have hanti : Antitone f := by
    apply antitone_of_deriv_nonpos (fun s => (hderiv s).differentiableAt)
    intro s
    rw [(hderiv s).deriv]
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (by linarith [hdec s])
  have key : Real.exp (γ * t) * V t ≤ Real.exp (γ * t₀) * V t₀ := hanti ht
  have e : Real.exp (-(γ * (t - t₀))) = Real.exp (γ * t₀) * Real.exp (-(γ * t)) := by
    rw [← Real.exp_add]; ring_nf
  calc V t = Real.exp (-(γ * t)) * (Real.exp (γ * t) * V t) := by
          rw [← mul_assoc, ← Real.exp_add]; simp
    _ ≤ Real.exp (-(γ * t)) * (Real.exp (γ * t₀) * V t₀) :=
          mul_le_mul_of_nonneg_left key (Real.exp_pos _).le
    _ = V t₀ * Real.exp (-(γ * (t - t₀))) := by rw [e]; ring

/-- Proposition 8.6 together: along a flow with ΞᵀG(Ξ) ≤ −(γ/2)ΞᵀΞ, γ > 0,
    VK(t) ≤ VK(t₀)e^{−γ(t−t₀)}. -/
theorem proposition_8_6 (Ξ : ℝ → Fin 7 → ℝ) (G : (Fin 7 → ℝ) → Fin 7 → ℝ) (γ : ℝ)
    (flow : ∀ t i, HasDerivAt (fun s => Ξ s i) (G (Ξ t) i) t)
    (lyapunov : ∀ t, ∑ i, Ξ t i * G (Ξ t) i ≤ -(γ / 2) * VK (Ξ t)) {t₀ t : ℝ} (ht : t₀ ≤ t) :
    VK (Ξ t) ≤ VK (Ξ t₀) * Real.exp (-(γ * (t - t₀))) :=
  decay (fun s => VK (Ξ s)) (fun s => 2 * ∑ i, Ξ s i * G (Ξ s) i) γ
    (fun s => dVK Ξ G s (flow s)) (fun s => by linarith [lyapunov s]) ht

end Approach

/-! ## Evidence §14.3 — Ξ̄* = φ⁻¹ = (√5 − 1)/2   (p. 231, l. 5080) -/

theorem inv_phi : goldenRatio⁻¹ = (Real.sqrt 5 - 1) / 2 := by
  rw [inv_gold, goldenConj]; ring

/-! ## §6.3 — Projection, return and scale -/

section Projection
variable {X Y : Type*}

/-- s(φ)(x, y) = φ(x).   (§6.3.4, p. 130, l. 2811) -/
def lift (φ : X → ℝ) : X × Y → ℝ := fun p => φ p.1

/-- π_U: the zero mode, the average over the fibre T⁴ (a probability measure ν). -/
noncomputable def zeroMode [MeasurableSpace Y] (ν : Measure Y) (Φ : X × Y → ℝ) : X → ℝ :=
  fun x => ∫ y, Φ (x, y) ∂ν

/-- π_U ∘ s = id.   (§6.3.4, p. 130, l. 2813) Its average over T⁴ is φ. -/
theorem zeroMode_lift [MeasurableSpace Y] (ν : Measure Y) [IsProbabilityMeasure ν]
    (φ : X → ℝ) : zeroMode ν (lift φ) = φ := by
  funext x; simp [zeroMode, lift]

/-- KK-momentum: ∫_{T¹} e^{i n y / R} dy = 2πR δ_{n,0}, one circle of the torus.
    Products of zero modes carry total momentum zero.   (§6.3.1) -/
theorem kk_mode (n : ℤ) (R : ℝ) (hR : R ≠ 0) :
    ∫ y in (0 : ℝ)..2 * π * R, Complex.exp (n * Complex.I * y / R) =
      if n = 0 then (2 * π * R : ℂ) else 0 := by
  split_ifs with hn
  · subst hn; simp
  · have hc : (n * Complex.I / R : ℂ) ≠ 0 := by
      simp [hn, hR, Complex.I_ne_zero]
    have := integral_exp_mul_complex (a := 0) (b := 2 * π * R) hc
    have e : ∀ y : ℝ, (n * Complex.I * y / R : ℂ) = n * Complex.I / R * y := by
      intro y; ring
    simp_rw [e]
    rw [this]
    have h2 : (n * Complex.I / R : ℂ) * (2 * π * R : ℝ) = n * (2 * π * Complex.I) := by
      push_cast; field_simp; ring
    rw [h2, Complex.exp_int_mul_two_pi_mul_I]
    simp

/-- G₄ = G₈ / Vol(T⁴).   (§6.3.2, p. 130, l. 2800) Fibre integration of a term
    that does not depend on the fibre multiplies it by Vol(T⁴):
    S_EH⁽⁸⁾ = (1/16πG₈)∫_U∫_{T⁴} √(-g₈)R₈ = (Vol(T⁴)/16πG₈)∫_U √(-g₄)R₄ = S_EH⁽⁴⁾ exactly
    when 1/(16πG₄) = Vol(T⁴)/(16πG₈). -/
theorem newton_constant (G₈ G₄ vol : ℝ) (h₈ : 0 < G₈) (hv : 0 < vol) :
    1 / (16 * π * G₄) = vol / (16 * π * G₈) ↔ G₄ = G₈ / vol := by
  have hπ := Real.pi_pos
  constructor
  · intro h
    have hG₄ : G₄ ≠ 0 := by
      rintro rfl; simp at h; exact absurd h (by positivity)
    field_simp at h ⊢
    nlinarith [h]
  · intro h; subst h; field_simp; ring

/-- S⁽⁸⁾ ∘ s = S⁽⁴⁾: the fibre integral of a lifted field is Vol(T⁴) times its
    integral on the base.   (§6.3.4, p. 131, l. 2817) -/
theorem fibre_integral [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y)
    [SigmaFinite μ] [SigmaFinite ν] [IsFiniteMeasure ν] (φ : X → ℝ) :
    ∫ p, lift φ p ∂(μ.prod ν) = (ν Set.univ).toReal * ∫ x, φ x ∂μ := by
  simp only [lift]
  rw [integral_fun_fst]
  simp [smul_eq_mul]

end Projection

/-! ## §5.2 — The action -/

section Action
variable {M : Type*} [MeasurableSpace M]

/-- L = L_SM + L_grav + L_cross.   (§5.2, p. 126, l. 2716) -/
def lagrangian (L_SM L_grav L_cross : M → ℝ) : M → ℝ := fun x => L_SM x + L_grav x + L_cross x

/-- S_UEF = ∫_M L(φ,∇φ,g) dV.   (§5.2, p. 126, l. 2714) -/
noncomputable def action (dV : Measure M) (L : M → ℝ) : ℝ := ∫ x, L x ∂dV

/-- The action of the sum is the sum of the actions of the three sectors. -/
theorem action_sectors (dV : Measure M) (L_SM L_grav L_cross : M → ℝ)
    (h₁ : Integrable L_SM dV) (h₂ : Integrable L_grav dV) (h₃ : Integrable L_cross dV) :
    action dV (lagrangian L_SM L_grav L_cross) = action dV L_SM + action dV L_grav + action dV L_cross := by
  unfold action lagrangian
  rw [integral_add (h₁.add h₂) h₃, integral_add h₁ h₂]

end Action

end UEF.Reals
