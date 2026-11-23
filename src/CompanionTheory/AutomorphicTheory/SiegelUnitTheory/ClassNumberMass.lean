module

public import Mathlib
public import Formalism.LocalToGlobal.GlobalTheory.GL5.PacketStatementOfIndependence
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0154

@[expose] public section

namespace CompanionTheory.HU

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.StandardLattice Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def SiegelOneAll : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E),
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND σ J → SW1b2 F E σ M J

theorem hU_of (h : SiegelOneAll) (D : D7) : RT.MassRatioUnderVolume D := GlobalTheory.VolRatioFromSecondClause.volumeRatio h D

end CompanionTheory.HU
