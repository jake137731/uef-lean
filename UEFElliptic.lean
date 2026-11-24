/-
  THE UNIFIED EXISTENCE FRAMEWORK — Chapter 29, in Lean 4 with Mathlib
  ξ₅ — Non-Divergence

  Jake McDonough, Institute for Higher Thinking, Louisville, Kentucky, USA

  Source: UEF Release, 01_Manuscript.pdf, Chapter 29, Parts II–IV: fracture energy and the
  finiteness of Sha, the p-torsion of a finite group, the collapse of the Selmer sequence, and
  the rank read off the Selmer group. ξ₅ is the non-divergence projection of the one condition
  Ξ = 0; its bridge is Theorem B.4 (UEFBridges.lean), with A4 giving ∫‖div S‖² = 0.
  All arithmetic is exact. No floating point anywhere.
-/
import Mathlib

namespace UEF.Elliptic

/-- Steps 5–6 — each nontrivial element of Sha carries a fracture of energy at least e₀ > 0,
    distinct elements give disjoint fractures, and the energies add. With finite total fracture
    energy ℰ_frac, Sha is finite, and every set of nontrivial elements has at most ℰ_frac/e₀
    members: |Sha| ≤ 1 + ℰ_frac/e₀. -/
theorem sha_finite {G : Type*} [Zero G] (e0 Efrac : ℝ) (he0 : 0 < e0)
    (adds : ∀ F : Finset G, (∀ σ ∈ F, σ ≠ 0) → e0 * F.card ≤ Efrac) :
    Set.Finite {σ : G | σ ≠ 0} ∧
      ∀ F : Finset G, (∀ σ ∈ F, σ ≠ 0) → (F.card : ℝ) ≤ Efrac / e0 := by
  refine ⟨?_, fun F hF => (le_div_iff₀ he0).mpr (by linarith [adds F hF])⟩
  by_contra hinf
  obtain ⟨n, hn⟩ := exists_nat_gt (Efrac / e0)
  obtain ⟨F, hFsub, hFcard⟩ := Set.Infinite.exists_subset_card_eq hinf n
  have h := adds F (fun σ hσ => hFsub (Finset.mem_coe.mpr hσ))
  rw [hFcard] at h
  have : (n : ℝ) ≤ Efrac / e0 := (le_div_iff₀ he0).mpr (by linarith)
  linarith

/-- Step 9 — a finite group has trivial p-torsion for every prime p not dividing its order. -/
theorem no_p_torsion {G : Type*} [AddGroup G] [Fintype G] (p : ℕ) (hp : p.Prime)
    (hdvd : ¬p ∣ Fintype.card G) (x : G) (hx : p • x = 0) : x = 0 := by
  have h1 : addOrderOf x ∣ p := addOrderOf_dvd_of_nsmul_eq_zero hx
  have h2 : addOrderOf x ∣ Fintype.card G := addOrderOf_dvd_card
  rcases (Nat.dvd_prime hp).mp h1 with h | h
  · exact addOrderOf_eq_one_iff.mp h
  · rw [h] at h2
    exact absurd h2 hdvd

/-- Step 9 — only finitely many primes divide |Sha|. -/
theorem finitely_many_primes (n : ℕ) (hn : n ≠ 0) : Set.Finite {p : ℕ | p.Prime ∧ p ∣ n} :=
  (Finset.finite_toSet (Nat.divisors n)).subset fun p hp => Nat.mem_divisors.mpr ⟨hp.2, hn⟩

/-- Step 9 — 0 → E(ℚ)/pE(ℚ) → Sel⁽ᵖ⁾ → Sha[p] → 0 with Sha[p] = 0: the first map is an
    isomorphism. -/
theorem sequence_collapse {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (f : A →+ B) (g : B →+ C) (hf : Function.Injective f)
    (exact : ∀ b, g b = 0 ↔ ∃ a, f a = b) (hC : ∀ c : C, c = 0) : Function.Bijective f :=
  ⟨hf, fun b => (exact b).mp (hC _)⟩

/-- Steps 8–9 — dim E(ℚ)/pE(ℚ) = r_alg + dim E(ℚ)[p] and E(ℚ)/pE(ℚ) ≅ Sel⁽ᵖ⁾ give
    r_alg = dim Sel⁽ᵖ⁾ − dim E(ℚ)[p]: the rank is read off the Selmer group. -/
theorem rank_read (r tors sel : ℕ) (h : sel = r + tors) : r = sel - tors := by omega

/-- Step 10 — with the fracture term zero (Step 7) and A4 giving ∫‖div S‖² = 0, ξ₅ = 0 reads
    r_alg = r_an. -/
theorem rank_equality (ralg ran fracture divS : ℕ) (h7 : fracture = 0) (hA4 : divS = 0)
    (h : ralg = ran + fracture + divS) : ralg = ran := by omega

end UEF.Elliptic
