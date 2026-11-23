module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PGenSecDomain
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PNormFormIrreducible
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSecBTorsionFree
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PIncidenceZeroLocus
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSpecChartBack

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Assembly
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

theorem SecAlgFinite.full : SecAlgFinite.Statement := SecAlgFinite.proof IncidenceNull.full
theorem ChartDomain.full : ChartDomain.Statement := ChartDomain.proof
theorem GenSecDomain.full : GenSecDomain.Statement :=
  GenSecDomain.proof ChartDomain.full GroundTheory.Heights₂.Heights.IncidenceGeneric.full
    (GroundTheory.Heights₂.Heights.IncIdealBelow.proof GroundTheory.Heights₂.Heights.ChowFormMultiHomog.full)
theorem SecAlgField.full : SecAlgField.Statement := SecAlgField.proof SecAlgFinite.full GenSecDomain.full
theorem ChowSecDvd.full : ChowSecDvd.Statement := ChowSecDvd.proof IncidenceNull.full
theorem NormFormIrreducible.full : NormFormIrreducible.Statement := NormFormIrreducible.proof
theorem NormFormDvd.full : NormFormDvd.Statement := NormFormDvd.proof
theorem SecAlgFieldChange.full : SecAlgFieldChange.Statement := SecAlgFieldChange.proof
theorem GenChowIrreducible.full : GenChowIrreducible.Statement :=
  GenChowIrreducible.proof GroundTheory.Heights₂.Heights.IncIdealPrime.full
    GroundTheory.Heights₂.Heights.ChowFormMultiHomog.full

theorem SpecFirstNeField.full : SpecFirstNeField.Statement :=
  have hDim : GroundTheory.Heights₂.Heights.IncIdealDim.Statement :=
    GroundTheory.Heights₂.Heights.IncIdealDim.proof GroundTheory.Heights₂.Heights.IncidenceGeneric.full
      GroundTheory.Heights₂.Heights.GenericLinearTrdeg.full GroundTheory.Heights₂.Heights.AffineChartTrdeg.proof
  SpecFirstNeField.proof
    (GroundTheory.Heights₂.Heights.ConeDimOfChowForm.proof hDim GroundTheory.Heights₂.Heights.IncIdealPrime.full)
    GroundTheory.Heights₂.Heights.ConeDimComponent.full
    (GroundTheory.Heights₂.Heights.ChowFormExists.proof hDim GroundTheory.Heights₂.Heights.IncIdealPrime.full)
    GroundTheory.Heights₂.Heights.IncidenceZeroLocus.proof

theorem SecBTorsionFree.full : SecBTorsionFree.Statement := SecBTorsionFree.proof ParDVRIsDVR.full
theorem GaussDVR.full : GaussDVR.Statement := GaussDVR.proof ParDVRIsDVR.full
theorem VertSpec.full : VertSpec.Statement := VertSpec.proof
theorem ResidueAlgIndep.full : ResidueAlgIndep.Statement := ResidueAlgIndep.proof

theorem CodimOnePrimeAvoid.full : CodimOnePrimeAvoid.Statement := CodimOnePrimeAvoid.proof
theorem FibreCut.full : FibreCut.Statement := FibreCut.proof CodimOnePrimeAvoid.full
theorem GenericFibreDrop.full : GenericFibreDrop.Statement := GenericFibreDrop.proof

theorem ChowFormSectionVertical.of_remaining
    (hGenSep : GenSecSeparable.Statement) (hFibre : FibreClosedComponent.Statement)
    (hKer : GenSecKer.Statement) (hChart : SpecChart.Statement) (hOrd : FiniteOrd.Statement) :
    ChowFormSectionVertical.Statement := by
  have hDim : GroundTheory.Heights₂.Heights.IncIdealDim.Statement :=
    GroundTheory.Heights₂.Heights.IncIdealDim.proof GroundTheory.Heights₂.Heights.IncidenceGeneric.full
      GroundTheory.Heights₂.Heights.GenericLinearTrdeg.full GroundTheory.Heights₂.Heights.AffineChartTrdeg.proof
  have hCone : GroundTheory.Heights₂.Heights.ConeDimOfChowForm.Statement :=
    GroundTheory.Heights₂.Heights.ConeDimOfChowForm.proof hDim GroundTheory.Heights₂.Heights.IncIdealPrime.full
  have hExist : GroundTheory.Heights₂.Heights.ChowFormExists.Statement :=
    GroundTheory.Heights₂.Heights.ChowFormExists.proof hDim GroundTheory.Heights₂.Heights.IncIdealPrime.full
  have cnf : ChowNormForm.Statement :=
    ChowNormForm.proof
      (ChowNormFormGeneric.proof SecAlgFinite.full GenSecDomain.full hGenSep ChowSecDvd.full
        NormFormIrreducible.full GenChowIrreducible.full NormFormDvd.full)
      SecAlgFieldChange.full
  have csd : ChowSecDegree.Statement := ChowSecDegree.proof cnf ChowFormHomog.full NormFormEval.full
  have nzd : SecLinNZD.Statement := SecLinNZD.proof cnf NormFormEval.full SpecFirstNeField.full
  have lininj : SecBLinInj.Statement :=
    SecBLinInj.proof SecBGeneric.full SecBTorsionFree.full nzd ParAlgIndep.full
  have fcd : FibreCompDim.Statement := FibreCompDim.proof hFibre FibreCut.full GenericFibreDrop.full
  have scd : SpecCompDim.Statement := SpecCompDim.proof hCone fcd
  have sip : SecIdealOfPrime.Statement :=
    SecIdealOfPrime.proof scd hExist ResidueAlgIndep.full SecAlgField.full hKer
  have smax : SpecMax.Statement := SpecMax.proof SecBFinite.full sip
  have sres : SpecResidue.Statement := SpecResidue.proof csd cnf scd hExist ResidueAlgIndep.full
  have slen : SpecLength.Statement :=
    SpecLength.proof hChart hOrd ParDVRIsDVR.full SecBFinite.full lininj
  have nid : NormIdentity.Statement :=
    NormIdentity.proof cnf SecBFinite.full SecBTorsionFree.full SecBGeneric.full NormFormLocalization.full
      NormFormEval.full ParAlgIndep.full ParFracIsFractionRing.full ParDVRIsDVR.full
  have oeq : OrdEq.Statement :=
    OrdEq.proof nid NormLength.full LengthDecomp.full smax slen sres VertSpec.full lininj
      SecBFinite.full SecBTorsionFree.full ParDVRIsDVR.full
  have geq : GaussEq.Statement := GaussEq.proof oeq GaussDVR.full ParDVRIsDVR.full
  exact Main.proof geq PrimitiveScale.full VertTermEq.full

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSpecChart
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

theorem SpecChart.proof : SpecChart.Statement := by
  intro K _ _ n e I v _ 𝔫 W _ hW h𝔫
  have := 𝔫.isMaximal
  have hPW : integralModel I ≤ W := le_trans le_sup_left hW.1.1.2
  have h𝔫' : W.map (toSecB e I v) = 𝔫.asIdeal := by rw [← secIdealOf_eq_map]; exact h𝔫
  obtain ⟨hcontr, hflat⟩ := SpecChart.contraction_and_flat 𝔫.asIdeal hPW h𝔫'
  have hunit : ∀ s : W.primeCompl, IsUnit (((algebraMap (SecB e I v)
      (Localization.AtPrime 𝔫.asIdeal)).comp (toSecB e I v)) s) := fun s =>
    IsLocalization.map_units (Localization.AtPrime 𝔫.asIdeal)
      (⟨toSecB e I v s, fun h => s.2 (hcontr _ h)⟩ : 𝔫.asIdeal.primeCompl)
  let ψ0 : Localization.AtPrime W →+* Localization.AtPrime 𝔫.asIdeal :=
    IsLocalization.lift (M := W.primeCompl) hunit
  have hψ0 : ∀ g, ψ0 (algebraMap _ (Localization.AtPrime W) g) =
      algebraMap (SecB e I v) (Localization.AtPrime 𝔫.asIdeal) (toSecB e I v g) :=
    fun g => IsLocalization.lift_eq hunit g
  have hker : (integralModel I).map (algebraMap _ (Localization.AtPrime W)) ≤ RingHom.ker ψ0 := by
    rw [Ideal.map_le_iff_le_comap]
    intro g hg
    rw [Ideal.mem_comap, RingHom.mem_ker, hψ0, RingHom.mem_ker.mp (SpecChart.toSecB_le e hg), map_zero]
  have hker' : ∀ a ∈ (integralModel I).map (algebraMap _ (Localization.AtPrime W)), ψ0 a = 0 :=
    fun a ha => RingHom.mem_ker.mp (hker ha)
  let ψ := Ideal.Quotient.lift _ ψ0 hker'
  have hψ : ∀ g, ψ (Ideal.Quotient.mk _ (algebraMap _ (Localization.AtPrime W) g)) =
      algebraMap (SecB e I v) (Localization.AtPrime 𝔫.asIdeal) (toSecB e I v g) := fun g => by
    show Ideal.Quotient.lift _ ψ0 hker' (Ideal.Quotient.mk _ _) = _
    rw [Ideal.Quotient.lift_mk, hψ0]
  have hmax : (IsLocalRing.maximalIdeal (Localization.AtPrime W)).map (ψ.comp (Ideal.Quotient.mk _)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime 𝔫.asIdeal) := by
    have hcomp : (ψ.comp (Ideal.Quotient.mk _)).comp (algebraMap _ (Localization.AtPrime W)) =
        (algebraMap (SecB e I v) (Localization.AtPrime 𝔫.asIdeal)).comp (toSecB e I v) :=
      RingHom.ext fun g => hψ g
    rw [← Localization.AtPrime.map_eq_maximalIdeal (I := W), Ideal.map_map, hcomp, ← Ideal.map_map, h𝔫',
      Localization.AtPrime.map_eq_maximalIdeal]
  refine ⟨ψ, fun g => ?_, ?_, ?_, hmax⟩
  · rw [hψ]
    rfl
  · exact ((IsLocalRing.local_hom_tfae (ψ.comp (Ideal.Quotient.mk _))).out 3 1).mp hmax.le
  · have := SpecChart.isLocalization_quot W (integralModel I)
    refine SpecChart.flat_of_isLocalization_comp (R := MvPolynomial (Fin n) (𝓞 K) ⧸ integralModel I)
      (S := Localization.AtPrime W ⧸ (integralModel I).map (algebraMap _ (Localization.AtPrime W)))
      (T := Localization.AtPrime 𝔫.asIdeal) (W.primeCompl.map (Ideal.Quotient.mk (integralModel I))) ψ ?_
    have h : ψ.comp (algebraMap (MvPolynomial (Fin n) (𝓞 K) ⧸ integralModel I)
        (Localization.AtPrime W ⧸ (integralModel I).map (algebraMap _ (Localization.AtPrime W)))) =
        SpecChart.quotToBn e 𝔫.asIdeal := by
      apply Ideal.Quotient.ringHom_ext
      refine RingHom.ext fun g => ?_
      simp only [RingHom.comp_apply]
      rw [Ideal.Quotient.algebraMap_quotient_map_quotient, hψ, SpecChart.quotToBn_mk]
    rw [h]
    exact hflat

end

end GroundTheory.Heights₂.Heights.Vertical
end

