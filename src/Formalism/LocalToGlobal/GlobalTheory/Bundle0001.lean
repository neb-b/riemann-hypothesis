module

public import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeSelfDual
public import Formalism.SharpRestriction.GlobalSchurBounds.JointsL
public import Formalism.LocalRingCardinality.Bundle0004
public import Formalism.LocalToGlobal.HermitianColumns.Bundle0003
public import Formalism.LocalToGlobal.HermitianColumns.ColsHerm
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Formalism.LocalToGlobal.GlobalTheory.LinkTiesTh
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta

@[expose] public section

-- bundled from Formalism.LocalToGlobal.GlobalTheory.LevelZeroClassLatticeIntegral
section
noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.L2.GlobalTheoryTheory

open Formalism.UG Formalism.UG.CS Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Herm Formalism.L2.GlobalTheoryTheory.Comp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def K0 (D : D7) : Coord D.sp.cm (D.sp.X 0) (Fin D.R.k) := ⟨D.sp.crd0, D.sp.gram0, D.sp.hermitianForm_base_coordinates⟩

theorem dualSub_eq {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) (L : Submodule (𝓞 E) S.V) :
    flipTwoThree.dualSub S L = (Formalism.HermitianLatticesTheory.dual S.hT L).toAddSubgroup := by
  ext x
  show (∀ y ∈ L, S.hT y x ∈ (algebraMap (𝓞 E) E).range) ↔ x ∈ Formalism.HermitianLatticesTheory.dual S.hT L
  rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
  simp only [Submodule.mem_one, RingHom.mem_range]

theorem card_ringOfIntegers_quot_natCast_eq_pow (D : D7) (T : ℕ) :
    Nat.card (𝓞 D.host.E ⧸ Ideal.span {((T : ℕ) : 𝓞 D.host.E)}) = T ^ (2 * D.R.f) := by
  have h1 := Ideal.absNorm_span_singleton (((T : ℕ) : 𝓞 D.host.E))
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at h1
  rw [h1]
  have h2 : ((T : ℕ) : 𝓞 D.host.E) = algebraMap ℤ (𝓞 D.host.E) (T : ℤ) := by simp
  rw [h2, Algebra.norm_algebraMap, RingOfIntegers.rank, Formalism.MainNotions.StandardLattice.finrank_host D]
  simp [Int.natAbs_pow]

end Formalism.L2.GlobalTheoryTheory

end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.NormSqLatticeFunctionEq
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory

open Formalism.BasicNotions Formalism.MainNotions NumberField

theorem lattice_character_eq (d : ℕ) (Λ : AddSubgroup ℂ) (x : ℂ) : GL3Theta.al1 d Λ x = al1 d Λ x := rfl

theorem taylorLogMetric_U1_eq_U1 (Λ : AddSubgroup ℂ) (x : ℂ) (G : ℂ → ℂ) : TaylorLogMetric.U1 Λ x G = U1 Λ x G := by
  funext z
  simp only [TaylorLogMetric.U1, U1, H1]
  congr 2
  ring

theorem is_theta_zero_iff (d : ℕ) (Λ : AddSubgroup ℂ) (G : ℂ → ℂ) : GL3Theta.IsTheta0 d Λ G ↔ IsTheta0 d Λ G := by
  unfold GL3Theta.IsTheta0 IsTheta0
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, fun x hx z => ?_, h3⟩
    have hx' := h2 x hx z
    rwa [lattice_character_eq, congrFun (taylorLogMetric_U1_eq_U1 Λ x G) z] at hx'
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, fun x hx z => ?_, h3⟩
    rw [lattice_character_eq, congrFun (taylorLogMetric_U1_eq_U1 Λ x G) z]
    exact h2 x hx z

end Formalism.L2.GlobalTheoryTheory

end
end

