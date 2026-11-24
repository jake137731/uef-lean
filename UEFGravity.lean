/-
  THE UNIFIED EXISTENCE FRAMEWORK — Chapter 13, in Lean 4 with Mathlib
  General Relativity and the Compatibility Theorem

  Jake McDonough, Institute for Higher Thinking, Louisville, Kentucky, USA

  Source: UEF Release, 01_Manuscript.pdf, Chapter 13, Theorems 12–18.
  All arithmetic is exact (ℚ and ℝ). There is no floating point anywhere.
-/
import Mathlib

open Real

namespace UEF.Gravity

/-! ## Theorem 12 — the Newtonian limit fixes the coefficient -/

/-- Step 12 — at first order G₀₀ = 2∇²Φ/c² and T₀₀ = ρc², so G₀₀ = (8πG/c⁴)T₀₀ is exactly
    Poisson's equation ∇²Φ = 4πGρ. -/
theorem newtonian_limit (G c ρ L : ℝ) (hc : c ≠ 0) :
    2 * L / c ^ 2 = 8 * π * G / c ^ 4 * (ρ * c ^ 2) ↔ L = 4 * π * G * ρ := by
  have e : 8 * π * G / c ^ 4 * (ρ * c ^ 2) = 2 * (4 * π * G * ρ) / c ^ 2 := by
    rw [div_mul_eq_mul_div, div_eq_div_iff (pow_ne_zero 4 hc) (pow_ne_zero 2 hc)]
    ring
  rw [e]
  constructor
  · intro h
    have := (div_left_inj' (pow_ne_zero 2 hc)).mp h
    linarith
  · intro h
    rw [h]

/-- The coefficient is fixed: a coupling κ that turns G₀₀ = κT₀₀ into Poisson's equation for
    every density is κ = 8πG/c⁴, which is the 1/16πG of the Einstein–Hilbert action. -/
theorem coefficient_fixed (G c κ : ℝ) (hc : c ≠ 0)
    (h : ∀ ρ L : ℝ, 2 * L / c ^ 2 = κ * (ρ * c ^ 2) ↔ L = 4 * π * G * ρ) :
    κ = 8 * π * G / c ^ 4 := by
  have := (h 1 (4 * π * G * 1)).mpr rfl
  rw [div_eq_iff (pow_ne_zero 2 hc)] at this
  rw [eq_div_iff (pow_ne_zero 4 hc)]
  linear_combination -this

/-! ## Theorem 13 — the geodesic equation from L_p = ½ g_{μν} ẋ^μ ẋ^ν -/

section Geodesic
variable {n : ℕ}

/-- Γ^α_{μν} = ½ g^{αρ}(∂_μ g_{ρν} + ∂_ν g_{ρμ} − ∂_ρ g_{μν}); dg σ ρ ν stands for ∂_σ g_{ρν}. -/
def christoffel (ginv : Matrix (Fin n) (Fin n) ℝ) (dg : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (α μ ν : Fin n) : ℝ :=
  1 / 2 * ∑ ρ, ginv α ρ * (dg μ ρ ν + dg ν ρ μ - dg ρ μ ν)

/-- Step 6 — the Euler–Lagrange expression of L_p:
    g_{ρν} ẍ^ν + ∂_σ g_{ρν} ẋ^σ ẋ^ν − ½ ∂_ρ g_{μν} ẋ^μ ẋ^ν. -/
def eulerLagrange (g : Matrix (Fin n) (Fin n) ℝ) (dg : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (v a : Fin n → ℝ) (ρ : Fin n) : ℝ :=
  ∑ ν, g ρ ν * a ν + ∑ σ, ∑ ν, dg σ ρ ν * v σ * v ν - 1 / 2 * ∑ μ, ∑ ν, dg ρ μ ν * v μ * v ν

/-- Step 6 — multiplying the Euler–Lagrange expression by g^{αρ} and symmetrizing the middle
    term gives ẍ^α + Γ^α_{μν} ẋ^μ ẋ^ν, the geodesic equation. -/
theorem geodesic_equation (g ginv : Matrix (Fin n) (Fin n) ℝ) (hinv : ginv * g = 1)
    (dg : Fin n → Matrix (Fin n) (Fin n) ℝ) (v a : Fin n → ℝ) (α : Fin n) :
    ∑ ρ, ginv α ρ * eulerLagrange g dg v a ρ
      = a α + ∑ μ, ∑ ν, christoffel ginv dg α μ ν * v μ * v ν := by
  have hA : ∑ ρ, ginv α ρ * ∑ ν, g ρ ν * a ν = a α := by
    calc ∑ ρ, ginv α ρ * ∑ ν, g ρ ν * a ν = ∑ ν, (∑ ρ, ginv α ρ * g ρ ν) * a ν := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
      _ = ∑ ν, (1 : Matrix (Fin n) (Fin n) ℝ) α ν * a ν := by
          refine Finset.sum_congr rfl fun ν _ => ?_
          rw [← hinv, Matrix.mul_apply]
      _ = a α := by simp [Matrix.one_apply]
  have swap : ∀ ρ, ∑ μ, ∑ ν, dg ν ρ μ * v μ * v ν = ∑ μ, ∑ ν, dg μ ρ ν * v μ * v ν := by
    intro ρ
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have key : ∀ ρ, ∑ μ, ∑ ν, (dg μ ρ ν + dg ν ρ μ - dg ρ μ ν) * v μ * v ν
      = 2 * ∑ μ, ∑ ν, dg μ ρ ν * v μ * v ν - ∑ μ, ∑ ν, dg ρ μ ν * v μ * v ν := by
    intro ρ
    have e : ∀ μ ν, (dg μ ρ ν + dg ν ρ μ - dg ρ μ ν) * v μ * v ν
        = dg μ ρ ν * v μ * v ν + dg ν ρ μ * v μ * v ν - dg ρ μ ν * v μ * v ν :=
      fun _ _ => by ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, swap ρ]
    ring
  have hR : ∑ μ, ∑ ν, christoffel ginv dg α μ ν * v μ * v ν
      = ∑ ρ, ginv α ρ * (1 / 2 * ∑ μ, ∑ ν, (dg μ ρ ν + dg ν ρ μ - dg ρ μ ν) * v μ * v ν) := by
    calc ∑ μ, ∑ ν, christoffel ginv dg α μ ν * v μ * v ν
        = ∑ μ, ∑ ν, ∑ ρ, ginv α ρ * (1 / 2 * ((dg μ ρ ν + dg ν ρ μ - dg ρ μ ν) * v μ * v ν)) := by
          unfold christoffel
          refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
          rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
          exact Finset.sum_congr rfl fun _ _ => by ring
      _ = ∑ μ, ∑ ρ, ∑ ν, ginv α ρ * (1 / 2 * ((dg μ ρ ν + dg ν ρ μ - dg ρ μ ν) * v μ * v ν)) :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ ρ, ∑ μ, ∑ ν, ginv α ρ * (1 / 2 * ((dg μ ρ ν + dg ν ρ μ - dg ρ μ ν) * v μ * v ν)) :=
          Finset.sum_comm
      _ = ∑ ρ, ginv α ρ * (1 / 2 * ∑ μ, ∑ ν, (dg μ ρ ν + dg ν ρ μ - dg ρ μ ν) * v μ * v ν) :=
          Finset.sum_congr rfl fun _ _ => by simp only [Finset.mul_sum]
  rw [hR, ← hA, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  unfold eulerLagrange
  rw [key ρ]
  ring

end Geodesic

/-! ## Theorem 14 — the Schwarzschild solution -/

/-- A function with zero derivative on (a, ∞) is constant there. -/
theorem const_of_deriv_zero {f : ℝ → ℝ} {a : ℝ} (h : ∀ r, a < r → HasDerivAt f 0 r)
    {r s : ℝ} (hr : a < r) (hs : a < s) : f r = f s := by
  have := (convex_Ioi a).norm_image_sub_le_of_norm_hasDerivWithin_le (f := f)
    (f' := fun _ => (0 : ℝ)) (C := 0) (fun x hx => (h x hx).hasDerivWithinAt)
    (fun _ _ => by simp) hs hr
  simpa [sub_eq_zero] using this

/-- Step 4, G_tt = 0 — d/dr(r(1 − e^{−2β})) = 0 for r > 0 gives e^{−2β} = 1 − C/r. -/
theorem gtt {B : ℝ → ℝ} (hB : ∀ r, 0 < r → HasDerivAt (fun r => r * (1 - B r)) 0 r) :
    ∃ C, ∀ r, 0 < r → B r = 1 - C / r := by
  refine ⟨1 * (1 - B 1), fun r hr => ?_⟩
  have h1 : r * (1 - B r) = 1 * (1 - B 1) := const_of_deriv_zero hB hr one_pos
  rw [eq_sub_iff_add_eq, ← h1, mul_div_cancel_left₀ _ hr.ne']
  ring

/-- Step 4, G_rr = 0 — α′ = C/[2r(r − C)] integrates to e^{2α} = K(1 − C/r) with K > 0. -/
theorem grr {α : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hα : ∀ r, C < r → HasDerivAt α (C / (2 * r * (r - C))) r) :
    ∃ K, 0 < K ∧ ∀ r, C < r → Real.exp (2 * α r) = K * (1 - C / r) := by
  have hd : ∀ r, C < r → HasDerivAt (fun r => 2 * α r - Real.log (1 - C / r)) 0 r := by
    intro r hr
    have hr0 : 0 < r := lt_of_le_of_lt hC hr
    have hrc : r - C ≠ 0 := (sub_pos.mpr hr).ne'
    have hq : HasDerivAt (fun r => 1 - C / r) (C / r ^ 2) r := by
      have := ((hasDerivAt_inv hr0.ne').const_mul C).const_sub 1
      convert this using 1 <;> first | (funext s; ring) | ring
    have hpos : 0 < 1 - C / r := by
      rw [sub_pos, div_lt_one hr0]
      exact hr
    have := ((hα r hr).const_mul 2).sub (hq.log hpos.ne')
    refine this.congr_deriv ?_
    field_simp
    ring
  refine ⟨Real.exp (2 * α (C + 1) - Real.log (1 - C / (C + 1))), Real.exp_pos _, fun r hr => ?_⟩
  have hr0 : 0 < r := lt_of_le_of_lt hC hr
  have hpos : 0 < 1 - C / r := by
    rw [sub_pos, div_lt_one hr0]
    exact hr
  have e : 2 * α r - Real.log (1 - C / r) = 2 * α (C + 1) - Real.log (1 - C / (C + 1)) :=
    const_of_deriv_zero hd hr (by linarith)
  rw [← e, Real.exp_sub, Real.exp_log hpos, div_mul_eq_mul_div, mul_div_assoc,
    div_self hpos.ne', mul_one]

/-- Step 5 — asymptotic flatness, e^{2α} → 1 as r → ∞, fixes K = 1. -/
theorem flat_fixes_K {α : ℝ → ℝ} {C K : ℝ}
    (hK : ∀ r, C < r → Real.exp (2 * α r) = K * (1 - C / r))
    (flat : Filter.Tendsto (fun r => Real.exp (2 * α r)) Filter.atTop (nhds 1)) : K = 1 := by
  have h1 : Filter.Tendsto (fun r => K * (1 - C / r)) Filter.atTop (nhds (K * (1 - 0))) :=
    (tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop Filter.tendsto_id)).const_mul K
  have h2 : Filter.Tendsto (fun r => Real.exp (2 * α r)) Filter.atTop (nhds (K * (1 - 0))) := by
    apply h1.congr'
    filter_upwards [Filter.eventually_gt_atTop C] with r hr
    exact (hK r hr).symm
  have := tendsto_nhds_unique flat h2
  rw [sub_zero, mul_one] at this
  exact this.symm

/-- Step 5 — with K = 1, e^{2α} = e^{−2β} = 1 − C/r gives α = −β. -/
theorem alpha_neg_beta {α β : ℝ → ℝ} {C r : ℝ}
    (hβ : Real.exp (-2 * β r) = 1 - C / r) (hα : Real.exp (2 * α r) = 1 * (1 - C / r)) :
    α r = -β r := by
  rw [one_mul, ← hβ] at hα
  have := Real.exp_injective hα
  linarith

/-- Step 7 — for one solar mass, GM☉ = 13271244 × 10¹³ m³ s⁻² (IAU 2015) and
    c = 299792458 m/s: r_s = 2GM☉/c² = 9479460000000000000/3209839924060063 m, exactly. -/
theorem sun_radius :
    (2 * (13271244 * 10 ^ 13) / 299792458 ^ 2 : ℚ) = 9479460000000000000 / 3209839924060063 := by
  norm_num

theorem sun_radius_bounds :
    (2953 : ℚ) < 9479460000000000000 / 3209839924060063 ∧
      (9479460000000000000 : ℚ) / 3209839924060063 < 2954 := by
  norm_num

/-- Step 7 — light climbing from r₁ to r₂ > r₁ arrives redshifted:
    ν₂/ν₁ = √(1 − r_s/r₁)/√(1 − r_s/r₂) < 1. -/
theorem redshift (rs r₁ r₂ : ℝ) (hrs : 0 < rs) (h1 : rs < r₁) (h12 : r₁ < r₂) :
    Real.sqrt (1 - rs / r₁) / Real.sqrt (1 - rs / r₂) < 1 := by
  have hr1 : 0 < r₁ := hrs.trans h1
  have hr2 : 0 < r₂ := hr1.trans h12
  have a : 0 < 1 - rs / r₁ := by
    rw [sub_pos, div_lt_one hr1]
    exact h1
  have b : 1 - rs / r₁ < 1 - rs / r₂ := by
    have : rs / r₂ < rs / r₁ := by
      rw [div_lt_div_iff hr2 hr1]
      exact mul_lt_mul_of_pos_left h12 hrs
    linarith
  rw [div_lt_one (Real.sqrt_pos.mpr (a.trans b))]
  exact Real.sqrt_lt_sqrt a.le b

/-! ## Theorem 15 — the horizon -/

/-- Step 1 — the horizon r = r_s = 2GM/c² has area A = 4πr_s² = 16πG²M²/c⁴. -/
theorem horizon_area (G M c : ℝ) :
    4 * π * (2 * G * M / c ^ 2) ^ 2 = 16 * π * G ^ 2 * M ^ 2 / c ^ 4 := by
  ring

/-- Step 2 — with l_P² = ħG/c³ the Bekenstein–Hawking term is A/4l_P² = 4πGM²/(ħc). -/
theorem horizon_entropy (G M c hbar : ℝ) (hG : 0 < G) (hc : 0 < c) (hh : 0 < hbar) :
    (4 * π * (2 * G * M / c ^ 2) ^ 2) / (4 * (hbar * G / c ^ 3)) =
      4 * π * G * M ^ 2 / (hbar * c) := by
  have h1 := hG.ne'
  have h2 := hc.ne'
  have h3 := hh.ne'
  field_simp
  ring

/-! ## Theorem 16 — the information paradox -/

/-- Steps 2–3 — the flux out of the region between the horizon and a distant sphere is zero, so
    the flux through the distant sphere balances the flux through the horizon. -/
theorem flux_balance (Φ_BH Φ_inf : ℝ) (h : Φ_BH + Φ_inf = 0) : Φ_inf = -Φ_BH := by
  linarith

/-- Step 5 — 0 = Φ_out − Φ_in + Φ_H gives Φ_out + Φ_H = Φ_in. -/
theorem flux_accounting (Φin Φout ΦH : ℝ) (h : 0 = Φout - Φin + ΦH) : Φout + ΦH = Φin := by
  linarith

/-- Step 6 — an injective encoding followed by an isometric evaporation: distinct infalling
    states give distinct radiation, and every inner product is kept. -/
theorem information_preserved {States H H' : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    (Enc : States → H) (hEnc : Function.Injective Enc) (U : H →ₗᵢ[ℂ] H') :
    Function.Injective (U ∘ Enc) ∧
      ∀ x y, @inner ℂ _ _ (U (Enc x)) (U (Enc y)) = @inner ℂ _ _ (Enc x) (Enc y) :=
  ⟨U.injective.comp hEnc, fun x y => U.inner_map_map (Enc x) (Enc y)⟩

/-! ## Theorem 17 — the dimension count -/

/-- Step 4 — in d dimensions [G_d] = 2 − d, so (1/G_d)R carries (d − 2) + 2 = d against the
    measure d^d x of dimension −d: the action is dimensionless in every dimension. -/
theorem action_dimensionless (d : ℤ) : (-(2 - d) + 2) + -d = 0 := by ring

/-- [G₈] = 2 − 8 = −6, and [1/G₈] + [R₈] = 6 + 2 = 8. -/
theorem G8_dimension : (2 : ℤ) - 8 = -6 ∧ -(2 - 8 : ℤ) + 2 = 8 := by norm_num

/-- G = G₈/V₄ with [V₄] = −4 has dimension −6 + 4 = −2 = 2 − 4, Newton's constant in 4D. -/
theorem G4_dimension : (2 - 8 : ℤ) - (-4) = 2 - 4 := by norm_num

/-- Step 6 — an operator of dimension 4 + 2k matches the k-th Kaluza–Klein mode. The match is
    one-to-one, and the operator lies beyond dimension 4 exactly when k ≥ 1. -/
theorem kk_correspondence :
    Function.Injective (fun k : ℕ => 4 + 2 * k) ∧ ∀ k : ℕ, 4 < 4 + 2 * k ↔ 1 ≤ k :=
  ⟨fun a b h => by
    have : 4 + 2 * a = 4 + 2 * b := h
    omega, fun k => by omega⟩

/-! ## Theorem 18 — the Friedmann equations -/

/-- Step 5 — G₀₀ = 8πGT₀₀ − Λg₀₀ with g₀₀ = −1: 3(ȧ² + k)/a² = 8πGρ + Λ gives
    (ȧ/a)² = (8πG/3)ρ − k/a² + Λ/3. -/
theorem friedmann_first (a x k ρ G Λ : ℝ) (ha : a ≠ 0)
    (G00 : 3 * (x ^ 2 + k) / a ^ 2 = 8 * π * G * ρ + Λ) :
    (x / a) ^ 2 = 8 * π * G / 3 * ρ - k / a ^ 2 + Λ / 3 := by
  rw [div_eq_iff (pow_ne_zero 2 ha)] at G00
  have hx : x ^ 2 = ((8 * π * G * ρ + Λ) * a ^ 2 - 3 * k) / 3 := by linarith
  rw [div_pow, hx]
  field_simp
  ring

/-- Step 6 — G_ii = 8πGT_ii − Λg_ii: −(2aä + ȧ² + k)/a² = 8πGp − Λ, combined with the first,
    gives ä/a = −(4πG/3)(ρ + 3p) + Λ/3. -/
theorem friedmann_second (a x y k ρ p G Λ : ℝ) (ha : a ≠ 0)
    (G00 : 3 * (x ^ 2 + k) / a ^ 2 = 8 * π * G * ρ + Λ)
    (Gii : -(2 * a * y + x ^ 2 + k) / a ^ 2 = 8 * π * G * p - Λ) :
    y / a = -(4 * π * G / 3) * (ρ + 3 * p) + Λ / 3 := by
  rw [div_eq_iff (pow_ne_zero 2 ha)] at G00 Gii
  rw [div_eq_iff ha]
  apply mul_left_cancel₀ (mul_ne_zero (by norm_num : (-2 : ℝ) ≠ 0) ha)
  linear_combination Gii + (1 / 3 : ℝ) * G00

/-- The same second equation in time: from the first Friedmann equation and the continuity of
    matter, ρ̇a = −3ȧ(ρ + p), at every moment the universe expands or contracts (ȧ ≠ 0). -/
theorem friedmann_acceleration (a a' a'' ρ ρ' p : ℝ → ℝ) (G Λ k : ℝ)
    (ha : ∀ t, HasDerivAt a (a' t) t) (ha' : ∀ t, HasDerivAt a' (a'' t) t)
    (hρ : ∀ t, HasDerivAt ρ (ρ' t) t)
    (friedmann1 : ∀ t, a' t ^ 2 = 8 * π * G / 3 * ρ t * a t ^ 2 - k + Λ / 3 * a t ^ 2)
    (conserv : ∀ t, ρ' t * a t = -3 * a' t * (ρ t + p t))
    (t : ℝ) (hpos : 0 < a t) (hmove : a' t ≠ 0) :
    a'' t / a t = -(4 * π * G / 3) * (ρ t + 3 * p t) + Λ / 3 := by
  have hL : HasDerivAt (fun s => a' s ^ 2) (2 * a' t * a'' t) t := by
    convert (ha' t).pow 2 using 1
    norm_num
  have hR : HasDerivAt (fun s => 8 * π * G / 3 * ρ s * a s ^ 2 - k + Λ / 3 * a s ^ 2)
      (8 * π * G / 3 * (ρ' t * a t ^ 2 + ρ t * (2 * a t * a' t)) + Λ / 3 * (2 * a t * a' t)) t := by
    have h := ((((hρ t).mul ((ha t).pow 2)).const_mul (8 * π * G / 3)).sub_const k).add
      (((ha t).pow 2).const_mul (Λ / 3))
    convert h using 1 <;> first | (funext s; ring) | norm_num
  have heq : (fun s => a' s ^ 2) =
      (fun s => 8 * π * G / 3 * ρ s * a s ^ 2 - k + Λ / 3 * a s ^ 2) :=
    funext friedmann1
  rw [heq] at hL
  have E := hL.unique hR
  rw [div_eq_iff hpos.ne']
  apply mul_left_cancel₀ (mul_ne_zero two_ne_zero hmove)
  linear_combination E + 8 * π * G / 3 * a t * conserv t

/-- The cosmic budget as stated: matter Ω_m = 315/1000 split by η = 156/1000, and dark energy
    Ω_Λ = 685/1000. Ordinary 2457/50000, dark 13293/50000, and the three sum to 1. -/
theorem budget :
    (156 : ℚ) / 1000 * (315 / 1000) = 2457 / 50000 ∧
      (844 : ℚ) / 1000 * (315 / 1000) = 13293 / 50000 ∧
      (2457 : ℚ) / 50000 + 13293 / 50000 + 685 / 1000 = 1 := by
  norm_num

/-- The budget closes for every realized fraction η: ηΩ_m + (1 − η)Ω_m + Ω_Λ = Ω_m + Ω_Λ. -/
theorem budget_any_eta (η Ωm ΩΛ : ℚ) : η * Ωm + (1 - η) * Ωm + ΩΛ = Ωm + ΩΛ := by ring

end UEF.Gravity
