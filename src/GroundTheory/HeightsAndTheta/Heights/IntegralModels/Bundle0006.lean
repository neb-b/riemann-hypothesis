module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PSumCp

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.Assembly
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

theorem BlowUpChart.full : BlowUpChart.Statement := BlowUpChart.proof

theorem FiniteIntegralClosure.full : FiniteIntegralClosure.Statement := FiniteIntegralClosure.proof

theorem MertensUpper.full : MertensUpper.Statement := MertensUpper.proof

theorem TorsionFreeQuotientLength.full : TorsionFreeQuotientLength.Statement := TorsionFreeQuotientLength.proof

theorem KrullAkizukiQuotientLength.full : KrullAkizukiQuotientLength.Statement :=
  KrullAkizukiQuotientLength.proof TorsionFreeQuotientLength.full

theorem KrullAkizuki.full : KrullAkizuki.Statement :=
  KrullAkizuki.proof KrullAkizukiQuotientLength.full

theorem DominatingDVR.full : DominatingDVR.Statement :=
  DominatingDVR.proof KrullAkizuki.full BlowUpChart.full

theorem SumCp.full : SumCp.Statement :=
  SumCp.proof MertensUpper.full

theorem FiniteNormalization.full : FiniteNormalization.Statement :=
  GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model.FiniteIntegralClosure.normalization_of_scheme
    (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model.FiniteIntegralClosure.scheme_of_alg
      (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model.FiniteIntegralClosure.alg_iff.mp FiniteIntegralClosure.full))

end GroundTheory.Heights₂.Heights.Model

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model

theorem BlowUpChart.full : BlowUpChart.Statement :=
  BlowUpChart.equiv.mp GroundTheory.Heights₂.Heights.Model.BlowUpChart.full

theorem KrullAkizuki.full : KrullAkizuki.Statement :=
  KrullAkizuki.equiv.mp GroundTheory.Heights₂.Heights.Model.KrullAkizuki.full

theorem MertensUpper.full : MertensUpper.Statement :=
  MertensUpper.equiv.mp GroundTheory.Heights₂.Heights.Model.MertensUpper.full

theorem SumCp.full : SumCp.Statement :=
  SumCp.equiv.mp GroundTheory.Heights₂.Heights.Model.SumCp.full

theorem FiniteIntegralClosure.full : FiniteIntegralClosure.Statement :=
  FiniteIntegralClosure.equiv.mp ⟨GroundTheory.Heights₂.Heights.Model.FiniteIntegralClosure.full,
    GroundTheory.Heights₂.Heights.Model.FiniteNormalization.full⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.PDominatingDVRScheme
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open AlgebraicGeometry

theorem DominatingDVR.closed : DominatingDVR.Statement :=
  DominatingDVR.proof
    (KrullAkizuki.proof (KrullAkizukiQuotientLength.proof TorsionFreeQuotientLength.proof))
    BlowUpChart.proof

theorem not_isField_stalk_of_ne_genericPoint (Z : Scheme.{0}) [IsIntegral Z] (z : Z)
    (hz : z ≠ genericPoint Z) : ¬ IsField (Z.presheaf.stalk z) := by
  intro hF
  have hgen : genericPoint Z ⤳ z := (genericPoint_spec Z).specializes trivial
  have hmem : genericPoint Z ∈ Set.range (Z.fromSpecStalk z) := by
    rw [Scheme.range_fromSpecStalk]; exact hgen
  obtain ⟨y, hy⟩ := hmem
  have hmax : IsLocalRing.maximalIdeal (Z.presheaf.stalk z) = ⊥ :=
    (IsLocalRing.isField_iff_maximalIdeal_eq.mp hF)
  have hyc : y = IsLocalRing.closedPoint (Z.presheaf.stalk z) := by
    apply PrimeSpectrum.ext
    apply le_antisymm
    · exact IsLocalRing.le_maximalIdeal y.isPrime.ne_top
    · exact hmax.le.trans bot_le
  apply hz
  rw [← hy, hyc, Scheme.fromSpecStalk_closedPoint]

theorem DominatingDVRScheme.proof : DominatingDVRScheme.Statement := by
  intro Z _ _ z hz
  exact DominatingDVR.closed (Z.presheaf.stalk z) (not_isField_stalk_of_ne_genericPoint Z z hz)
    Z.functionField

end GroundTheory.Heights₂.Heights.Model
end

