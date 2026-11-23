module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0577
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0255
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0127

@[expose] public section

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm

theorem zOf_coeff_mem {G : Type} [Group G] [Fintype G] (K : IntermediateField ℚ ℂ) (χ : G → ℂ)
    (h : ∀ x, χ x ∈ K) (y : G) : (zOf χ).coeff y ∈ K := by
  unfold zOf
  refine Finset.sum_induction _ (fun a : MonoidAlgebra ℂ G => a.coeff y ∈ K) ?_ ?_ ?_
  · intro a b ha hb
    have := K.add_mem ha hb
    simpa using this
  · simp
  · intro x _
    have h1 : χ 1 / (Fintype.card G : ℂ) * χ x⁻¹ ∈ K :=
      K.mul_mem (K.div_mem (h 1) (natCast_mem K _)) (h _)
    rw [MonoidAlgebra.coeff_single, Finsupp.single_apply]
    split_ifs
    · exact h1
    · exact K.zero_mem

theorem isSer_eSerC (g : ℕ) [Fact g.Prime] (L : LabelDatum g) (hg : 5 ≤ g) (hG : Green) (r N : ℕ) (hN : 0 < N)
    (hd : Nat.card (GL (Fin r) (ZMod g)) ∣ N) : GlobalTheory.MemN.IsSer r g N (eSerC L r) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := _root_.GlobalTheory.GLq.eSerC_laws g L hg hG r
  refine ⟨h1, h2, h3, ?_, h5, ?_⟩
  · intro f
    refine ⟨fun h0 hf => _root_.GlobalTheory.GLm.eSerC_ne_zero g L hG r f hf.1 hf.2.1 hf.2.2 h0, h4 f⟩
  · intro f x
    unfold eSerC
    refine finsum_mem_induction (fun a : MonoidAlgebra ℂ (Gn g r) => a.coeff x ∈
      IntermediateField.adjoin ℚ {Complex.exp (2 * Real.pi * Complex.I / (N : ℕ))}) ?_ ?_ ?_
    · simp
    · intro a b ha hb
      have := add_mem ha hb
      simpa using this
    · intro χ hχ
      obtain ⟨⟨V, _, hV⟩, _⟩ := hχ
      exact zOf_coeff_mem _ χ (_root_.GlobalTheory.GLm.isChar_mem_adjoin_exp (Gn g r) χ N hN hd ⟨V, hV⟩) x

end GlobalTheory.GLm
