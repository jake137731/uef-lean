/-
  THE UNIFIED EXISTENCE FRAMEWORK — Chapter 16, in Lean 4 with Mathlib
  Discrete Toroidal Geometry

  Jake McDonough, Institute for Higher Thinking, Louisville, Kentucky, USA

  Source: UEF Release, 01_Manuscript.pdf, Chapter 16: the operational conditions T1–T4 and the
  embedding of 16.2–16.3. All arithmetic is exact. No floating point anywhere.
-/
import Mathlib

namespace UEF.Torus

/-! ## 16.2 — the toroidal band and its lattice -/

/-- (T1) Containment — the discrete toroidal band has no edge to fall off: the step x ↦ x + 1
    is a bijection, so every point has exactly one successor and one predecessor. -/
theorem no_edge (n : ℕ) : Function.Bijective fun x : ZMod n => x + 1 :=
  (Equiv.addRight (1 : ZMod n)).bijective

/-- (T1) — n steps around the band return to the start. -/
theorem wraps (n : ℕ) (x : ZMod n) : x + (n : ZMod n) = x := by simp

/-- (T2) Accountability — the lattice has finitely many distinguishable states, n · m of them. -/
theorem finitely_many (n m : ℕ) [NeZero n] [NeZero m] :
    Fintype.card (ZMod n × ZMod m) = n * m := by
  simp [ZMod.card]

/-- Admissible transitions: CIO operations that preserve the boundary invariants S|∂R. -/
def Admissible {X Y : Type*} (S : X → Y) (f : X → X) : Prop := ∀ x, S (f x) = S x

theorem admissible_id {X Y : Type*} (S : X → Y) : Admissible S id := fun _ => rfl

theorem admissible_comp {X Y : Type*} {S : X → Y} {f g : X → X}
    (hf : Admissible S f) (hg : Admissible S g) : Admissible S (f ∘ g) :=
  fun x => (hf (g x)).trans (hg x)

/-! ## 16.3 — adversarial misreading as structured Ξ deviation [M] -/

/-- A targeted attack that activates any one channel ξᵢ leaves Ξ ≠ 0, and VK(Ξ) = Σξⱼ² > 0
    sees it: no component stays isolated from the certificate. -/
theorem attack_detected (Ξ : Fin 7 → ℝ) (i : Fin 7) (h : Ξ i ≠ 0) :
    Ξ ≠ 0 ∧ 0 < ∑ j, Ξ j ^ 2 := by
  refine ⟨fun h0 => h (congrFun h0 i), ?_⟩
  calc (0 : ℝ) < Ξ i ^ 2 := by positivity
    _ ≤ ∑ j, Ξ j ^ 2 := Finset.single_le_sum (fun j _ => sq_nonneg (Ξ j)) (Finset.mem_univ i)

end UEF.Torus
