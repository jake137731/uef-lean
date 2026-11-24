/-
  THE UNIFIED EXISTENCE FRAMEWORK — Chapter 26, in Lean 4 with Mathlib
  ξ₂ — Continuity

  Jake McDonough, Institute for Higher Thinking, Louisville, Kentucky, USA

  Source: UEF Release, 01_Manuscript.pdf, Chapter 26, Parts II–IV: the S energy estimates,
  Grönwall, the enstrophy bound, and Serrin's condition. ξ₂ is the continuity projection of the
  one condition Ξ = 0; its bridge is Theorem B.3.
  All arithmetic is exact. No floating point anywhere.
-/
import Mathlib

open Real

namespace UEF.Fluids

/-- Part II, Step 2 — d/dt‖S‖ ≤ 2C_topo C₀ gives ‖S(t)‖ ≤ ‖S₀‖ + 2C_topo C₀ t. -/
theorem linear_growth (f f' : ℝ → ℝ) (c : ℝ) (hf : ∀ t, HasDerivAt f (f' t) t)
    (hb : ∀ t, f' t ≤ c) (t : ℝ) (ht : 0 ≤ t) : f t ≤ f 0 + c * t := by
  have hg : ∀ s, HasDerivAt (fun s => f s - c * s) (f' s - c) s := fun s =>
    ((hf s).sub ((hasDerivAt_id s).const_mul c)).congr_deriv (by ring)
  have hanti := antitone_of_deriv_nonpos (fun s => (hg s).differentiableAt)
    (fun s => by rw [(hg s).deriv]; linarith [hb s])
  have h := hanti ht
  dsimp only at h
  linarith

/-- Grönwall — y′ ≤ ay + b with a > 0, b ≥ 0 gives y(t) ≤ (y(0) + b/a)e^{at} for t ≥ 0. -/
theorem gronwall (y y' : ℝ → ℝ) (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (hy : ∀ t, HasDerivAt y (y' t) t) (hineq : ∀ t, y' t ≤ a * y t + b) (t : ℝ) (ht : 0 ≤ t) :
    y t ≤ (y 0 + b / a) * Real.exp (a * t) := by
  have ha' : a ≠ 0 := ha.ne'
  have hz : ∀ s, HasDerivAt (fun s => (y s + b / a) * Real.exp (-(a * s)))
      ((y' s - a * y s - b) * Real.exp (-(a * s))) s := by
    intro s
    have h1 : HasDerivAt (fun s => Real.exp (-(a * s))) (Real.exp (-(a * s)) * -(a * 1)) s :=
      ((hasDerivAt_id s).const_mul a).neg.exp
    refine (((hy s).add_const (b / a)).mul h1).congr_deriv ?_
    field_simp
    ring
  have hanti := antitone_of_deriv_nonpos (fun s => (hz s).differentiableAt) (fun s => by
    rw [(hz s).deriv]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hineq s]) (Real.exp_pos _).le)
  have h := hanti ht
  dsimp only at h
  rw [mul_zero, neg_zero, Real.exp_zero, mul_one] at h
  have he : 0 < Real.exp (a * t) := Real.exp_pos _
  have hprod : y t + b / a = (y t + b / a) * Real.exp (-(a * t)) * Real.exp (a * t) := by
    rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
  have hba : 0 ≤ b / a := div_nonneg hb ha.le
  calc y t ≤ y t + b / a := by linarith
    _ = (y t + b / a) * Real.exp (-(a * t)) * Real.exp (a * t) := hprod
    _ ≤ (y 0 + b / a) * Real.exp (a * t) := mul_le_mul_of_nonneg_right h he.le

/-- Part II, Step 2 — d/dt‖∇S‖ ≤ 2C_u‖∇S‖ + 2C_topo C₀ gives
    ‖∇S(t)‖ ≤ (‖∇S₀‖ + C_topo C₀/C_u) e^{2C_u t}. -/
theorem gradS_bound (X X' : ℝ → ℝ) (Cu Ct C0 : ℝ) (hCu : 0 < Cu) (hb : 0 ≤ Ct * C0)
    (hX : ∀ t, HasDerivAt X (X' t) t) (hineq : ∀ t, X' t ≤ 2 * Cu * X t + 2 * Ct * C0)
    (t : ℝ) (ht : 0 ≤ t) : X t ≤ (X 0 + Ct * C0 / Cu) * Real.exp (2 * Cu * t) := by
  have := gronwall X X' (2 * Cu) (2 * Ct * C0) (by positivity) (by linarith) hX
    (fun s => by linarith [hineq s]) t ht
  rwa [show 2 * Ct * C0 / (2 * Cu) = Ct * C0 / Cu by field_simp; ring] at this

/-- Part III, Step 6 — √y ≤ (1 + y)/2. -/
theorem sqrt_le_half (y : ℝ) (hy : 0 ≤ y) : Real.sqrt y ≤ (1 + y) / 2 := by
  nlinarith [Real.sq_sqrt hy, Real.sqrt_nonneg y, sq_nonneg (Real.sqrt y - 1)]

/-- Part III, Steps 5–6 — dy/dt ≤ K₁y + K₂√y gives dy/dt ≤ (K₁ + K₂/2)y + K₂/2, and then
    y(t) ≤ (y(0) + K₂/(2K₁ + K₂)) e^{(K₁ + K₂/2)t}: the enstrophy stays bounded on every
    interval. -/
theorem enstrophy (y y' : ℝ → ℝ) (K1 K2 : ℝ) (hK1 : 0 < K1) (hK2 : 0 ≤ K2)
    (hpos : ∀ t, 0 ≤ y t) (hy : ∀ t, HasDerivAt y (y' t) t)
    (hineq : ∀ t, y' t ≤ K1 * y t + K2 * Real.sqrt (y t)) (t : ℝ) (ht : 0 ≤ t) :
    y t ≤ (y 0 + K2 / (2 * K1 + K2)) * Real.exp ((K1 + K2 / 2) * t) := by
  have hlin : ∀ s, y' s ≤ (K1 + K2 / 2) * y s + K2 / 2 := by
    intro s
    have h1 := sqrt_le_half (y s) (hpos s)
    have h2 : K2 * Real.sqrt (y s) ≤ K2 * ((1 + y s) / 2) := mul_le_mul_of_nonneg_left h1 hK2
    nlinarith [hineq s]
  have := gronwall y y' (K1 + K2 / 2) (K2 / 2) (by positivity) (by positivity) hy hlin t ht
  rwa [div_div, show 2 * (K1 + K2 / 2) = 2 * K1 + K2 by ring] at this

/-- Part IV — u bounded in L^q uniformly in time with q = 6 (p = ∞): 2/p + 3/q = 0 + 1/2 ≤ 1,
    Serrin's condition. -/
theorem serrin : (0 : ℚ) + 3 / 6 = 1 / 2 ∧ (1 : ℚ) / 2 ≤ 1 := by norm_num

/-- Part III, Step 4 — ‖curl(S·∇S)‖ ≤ C_geom C₁ + C_topo C₅ =: C_curl and
    |B_back| ≤ κ‖ω‖C_curl = C_UEF‖ω‖. -/
theorem back_reaction (κ ω Ccurl Cgeom C1 Ctopo C5 B : ℝ) (hκ : 0 ≤ κ) (hω : 0 ≤ ω)
    (hcurl : Ccurl ≤ Cgeom * C1 + Ctopo * C5) (hB : |B| ≤ κ * ω * Ccurl) :
    |B| ≤ κ * (Cgeom * C1 + Ctopo * C5) * ω := by
  have : κ * ω * Ccurl ≤ κ * ω * (Cgeom * C1 + Ctopo * C5) :=
    mul_le_mul_of_nonneg_left hcurl (mul_nonneg hκ hω)
  linarith

end UEF.Fluids
