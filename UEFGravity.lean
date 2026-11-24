/-
  THE UNIFIED EXISTENCE FRAMEWORK — Chapters 12 and 13, in Lean 4 with Mathlib

  Jake McDonough, Institute for Higher Thinking, Louisville, Kentucky, USA

  Source: UEF Release, 01_Manuscript.pdf, evidence Chapter 12 (the dark sector,
  Definitions 1.1–1.2) and Chapter 13 (Theorem 15, the horizon entropy; Theorem 18,
  the Friedmann equations). All arithmetic is exact: no floating point anywhere.
-/
import Mathlib

open Real

namespace UEF.Gravity

/-! ## Chapter 12 — The realized domain and the dark sector -/

section Dark
variable {Ω : Type*} (R : Set Ω)

/-- Definition 1.2 — Ω_dark = Ω − R: the uncollapsed complement of the realized domain. -/
def dark : Set Ω := Rᶜ

/-- Ω partitions into the realized domain and the dark sector, with nothing in both. -/
theorem partition : R ∪ dark R = Set.univ ∧ R ∩ dark R = ∅ :=
  ⟨Set.union_compl_self R, Set.inter_compl_self R⟩

/-- Ω_dark = ∅ exactly when Ω = R: every configuration realized. -/
theorem dark_empty_iff : dark R = ∅ ↔ R = Set.univ :=
  Set.compl_empty_iff

end Dark

/-! ## Theorem 15 — The horizon term of the black hole entropy -/

/-- The horizon r = r_s = 2GM/c² has area A = 4πr_s², and with l_P² = ħG/c³ the
    Bekenstein–Hawking term is A/4l_P² = 4πGM²/(ħc). -/
theorem horizon_entropy (G M c hbar : ℝ) (hG : 0 < G) (hc : 0 < c) (hh : 0 < hbar) :
    (4 * π * (2 * G * M / c ^ 2) ^ 2) / (4 * (hbar * G / c ^ 3)) = 4 * π * G * M ^ 2 / (hbar * c) := by
  have h1 := hG.ne'
  have h2 := hc.ne'
  have h3 := hh.ne'
  field_simp
  ring

/-! ## Theorem 18 — The Friedmann equations -/

/-- The second Friedmann equation follows from the first and the continuity of the
    matter, ρ̇ = −3(ȧ/a)(ρ + p):
    (ȧ/a)² = (8πG/3)ρ − k/a² + Λ/3  ⟹  ä/a = −(4πG/3)(ρ + 3p) + Λ/3,
    at every moment the universe is expanding or contracting (ȧ ≠ 0). -/
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
  have heq : (fun s => a' s ^ 2) = (fun s => 8 * π * G / 3 * ρ s * a s ^ 2 - k + Λ / 3 * a s ^ 2) :=
    funext friedmann1
  rw [heq] at hL
  have E := hL.unique hR
  rw [div_eq_iff hpos.ne']
  apply mul_left_cancel₀ (mul_ne_zero two_ne_zero hmove)
  linear_combination E + 8 * π * G / 3 * a t * conserv t

end UEF.Gravity
