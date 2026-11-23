module

public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Formalism.HermitianLattices.Bundle0003
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.DoubleCosetDecomposition
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LevelSubgroupStabilizers

open NumberField Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open scoped TensorProduct

section Level

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem finMat_one : finMat σ J (1 : HA (AF F) σ J) = 1 := by
  show (((1 : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E))).map _ = 1
  rw [Units.val_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem finMat_mul (g h : HA (AF F) σ J) : finMat σ J (g * h) = finMat σ J g * finMat σ J h := by
  show (((HA.mat (AF F) σ J g * HA.mat (AF F) σ J h : GL (Fin M) (AF F ⊗[F] E)) :
    Matrix (Fin M) (Fin M) (AF F ⊗[F] E))).map _ = _
  rw [Units.val_mul]
  exact Matrix.map_mul (f := (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom)

def levelK (L : Set (Fin M → E)) : Subgroup (HA (AF F) σ J) where
  carrier := {h | ∀ y, y ∈ latHat F E L ↔ (finMat σ J h).mulVec y ∈ latHat F E L}
  one_mem' := by
    intro y
    rw [finMat_one, Matrix.one_mulVec]
  mul_mem' := by
    intro a b ha hb y
    rw [finMat_mul, ← Matrix.mulVec_mulVec]
    exact (hb y).trans (ha _)
  inv_mem' := by
    intro a ha y
    have := ha ((finMat σ J a⁻¹).mulVec y)
    rw [Matrix.mulVec_mulVec, ← finMat_mul, mul_inv_cancel, finMat_one, Matrix.one_mulVec] at this
    exact this.symm

end Level

section Space

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

def latCoord (W : HSpace E) : Set (Fin W.rank → E) := {x | ∑ i, x i • W.frame i ∈ W.L0}

def levelW (hc : CMData F E) (W : HSpace E) : Subgroup (HA (AF F) hc.sig W.gram) :=
  levelK hc.sig W.gram (latCoord W)


end Space

end GlobalTheory.IndefiniteRowSideFullHecke.LevelSubgroupStabilizers
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.VolumePerpendicular
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.VolumePerpendicular

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

section Spaces

variable {E : Type} [Field E] [NumberField E] [StarRing E]

end Spaces

def IsVol (D : D7) : letI := D.host.cmStar; HSpace D.host.E → ℕ → ℕ → ℝ → Prop :=
  letI := D.host.cmStar
  fun W P Q V =>
    0 < V ∧
    AllSome (IsVolMeas D W P Q) fun μ =>
    AllSome (fun 𝓕 => IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W.gram) 𝓕 μ) fun 𝓕 =>
      μ 𝓕 = ENNReal.ofReal V

end GlobalTheory.IndefiniteRowSideFullHecke.VolumePerpendicular
end
end

