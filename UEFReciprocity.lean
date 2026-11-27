/-
  Reciprocity of the 467-step document, with its application, and the UEF.
  Built only on UEF.lean, unchanged: G1, G12, E29, E30, Theorem 3.15.1, the
  Ledger and R1–R5. No hypothesis, no axiom added, no `sorry`.

  L is the UEF's ledger over E. D is the document's ledger over the same E:
  its ground lines are members of E, and every other line is derived by a
  stated rule from the lines before it. Both are ledgers in the sense of
  Theorem 3.23.1; nothing else is supposed of either.
-/
import UEF

namespace UEF.Reciprocity
open UEF

universe u
variable {S : Type u} {R : Rule S → Prop} {E : Stmts S}

/-- G1 — the union of two sets of statements. -/
def union (X Y : Stmts S) : Stmts S := fun φ => X φ ∨ Y φ

/-- Two ledgers on one ground E have one theory: Th(U) = Th(E) = Th(D). (R3 twice.) -/
theorem one_theory (L D : Ledger R E) :
    Th R L.U = Th R E ∧ Th R E = Th R D.U ∧ Th R L.U = Th R D.U :=
  ⟨(R3 L).2.symm, (R3 D).2, (R3 L).2.symm.trans (R3 D).2⟩

/-- Reciprocity of the UEF and the document: U ⊢ D and D ⊢ U. -/
theorem uef_doc_reciprocal (L D : Ledger R E) : Reciprocal R L.U D.U := by
  have h := (one_theory L D).2.2
  refine ⟨?_, ?_⟩
  · intro φ hφ; rw [h]; exact E29 R D.U φ hφ
  · intro φ hφ; rw [← h]; exact E29 R L.U φ hφ

/-- Each is in the other: every line of the UEF is a theorem of the document,
    every line of the document is a theorem of the UEF, and for every φ,
    φ ∈ Th(U) ⟺ φ ∈ Th(D). -/
theorem each_in_the_other (L D : Ledger R E) :
    L.U ⊆ Th R D.U ∧ D.U ⊆ Th R L.U ∧ ∀ φ, Th R L.U φ ↔ Th R D.U φ :=
  ⟨(uef_doc_reciprocal L D).2, (uef_doc_reciprocal L D).1,
   fun φ => by rw [(one_theory L D).2.2]⟩

/-- Writing the UEF's lines into the document adds nothing, and writing the
    document's lines into the UEF adds nothing: Th(D ∪ U) = Th(D), Th(U ∪ D) = Th(U). -/
theorem nothing_added (L D : Ledger R E) :
    Th R (union D.U L.U) = Th R D.U ∧ Th R (union L.U D.U) = Th R L.U := by
  have ⟨hUD, hDU, _⟩ := each_in_the_other L D
  have into {X Y : Stmts S} (hY : Y ⊆ Th R X) : Th R (union X Y) = Th R X :=
    (reciprocity R
      (fun φ h => h.elim (E29 R X φ) (hY φ))
      (fun φ h => E29 R (union X Y) φ (Or.inl h))).symm
  exact ⟨into hUD, into hDU⟩

/-- The UEF is the one theory reciprocal with E, and so is the document. (R5.) -/
theorem one_reciprocal (L D : Ledger R E) :
    ExactlyOne (MutuallyDerivable (R := R) E) ∧ Th R L.U = Th R D.U :=
  ⟨(R5 L).1, (one_theory L D).2.2⟩

end UEF.Reciprocity
