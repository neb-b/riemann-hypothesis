module

public import Formalism.SharpRestriction.SmoothDesignExistence.DesignExistsDes
public import Formalism.SharpRestriction.SmoothDesignExistence.LinkGLOBALPk
public import Formalism.SharpRestriction.GlobalSchurBounds.LinkMin
public import Formalism.SharpRestriction.GlobalSchurBounds.MainSup
public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.LemmaTwoThreeOfSiegelBound
public import Formalism.PeriodIntegrals.ExplicitFormulaCounts.ExplicitFormula
public import Formalism.SharpRestriction.GlobalSchurBounds.Bundle0001
public import Formalism.LocalToGlobal.GlobalTheory.GL2.Statement
public import Formalism.GL3MeanSquares.SecondEstimateOfIntervalHypothesis
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0012
public import Formalism.GL3MeanSquares.HookFormulaTorsion.Bundle0005
public import Formalism.GL3MeanSquares.HookFormulaTorsion.Bundle0006
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0011
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0006
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0003
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0001
public import Formalism.LandauZeroFreeBounds.Bundle0001
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Imports
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.FamilyPartFiveOfExplicitConstants
public import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0006
public import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.Bundle0005
public import Formalism.SharpRestriction.GlobalSchurBounds.FirstClaimLemmaTwoFourOfLemmaTwoThree
public import Formalism.SharpRestriction.GlobalSchurBounds.JointsL
public import Formalism.LocalToGlobal.GlobalTheory.LossRequirementsOfSmallShares
public import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0010
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0012
public import Formalism.GradedWeylDivisibility.FinalC
public import Formalism.LocalToGlobal.Divisibility.Bundle0005

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.Wire

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.GlobalTheoryTheory Formalism.MainNotions.Lnk Formalism.L2.GlobalTheoryTheory

structure FamGLmin (𝒞 : FamClass) (C5 : ℝ) : Prop where
  h2b : Closed 𝒞 fun Fm _ => flipTwoThree.fam0 Fm StandardLattice.MassRatio₂
  h2v : Closed 𝒞 fun Fm _ => flipTwoThree.fam0 Fm StandardLattice.BaseVolumeEqualsMass
  h3 : Closed 𝒞 fun Fm _ => flipTwoThree.fam0 Fm StandardLattice.SigmaDegreeTwoSidedBoundOfGap
  hZa : Closed 𝒞 fun Fm _ => flipTwoThree.FamilySlopeLowerOpenPart Fm
  hZb : Closed 𝒞 fun Fm _ => flipTwoThree.FamilySlopeMaxOpenPart Fm C5
  tCV : Closed 𝒞 fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) u, Nonempty (flipTwoThree.ColVal (Fm.D x i) u)
  hW : Closed 𝒞 fun Fm _ => FamU Fm fun D u => Nonempty (product_first_zeroth_parts.FreeT D u)
  hμ : Closed 𝒞 fun Fm _ => FamU Fm product_first_zeroth_parts.SlopeLine
  hI : Closed 𝒞 fun Fm _ => FamU Fm LocalLatticeBases.HeckeIntegralLevelZero
  hR : Closed 𝒞 fun Fm _ => FamU Fm LocalLatticeBases.HeckeRamifiedLevelZero
  hB : Closed 𝒞 fun Fm _ => FamU Fm LocalLatticeBases.SecondBranchInclusionLength

theorem linkGLOBAL_of_7w {eps : ℝ} (Fm : FamP eps) (Cabs CH C0 eD eL : ℝ) (h : LinkGLOBAL7 Fm Cabs CH C0 eD eL)
    (hW : ChosenWall Fm) : LinkGLOBAL Fm Cabs CH C0 eD eL :=
  fun hCh hIn => h (Formalism.L2.GlobalTheoryTheory.Loss7.loss_requirements_of_small_shares Fm C0 CH hCh hW) hIn

theorem FamGLmin.link7 {𝒞 : FamClass} {C5 : ℝ} (h : FamGLmin 𝒞 C5) (Cabs C0 : ℝ) (hCabs : 0 ≤ Cabs) (hC0 : 3 ≤ C0) :
    Closed 𝒞 fun Fm CH => TuSize Fm → LinkGLOBAL7 Fm Cabs CH C0 Cabs 0 :=
  by
    apply ((closed_CH 𝒞).and (h.h2b.and (h.h2v.and (h.h3.and (h.hZa.and (h.hZb.and (h.tCV.and (h.hW.and (h.hμ.and
      (h.hI.and (h.hR.and h.hB))))))))))).imp
    intro eps Fm CH _ hs
    obtain ⟨hCH, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := hs
    exact linkGLOBAL7_min Fm Cabs CH C0 C5 hCabs hCH hC0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11

theorem FamGLmin.link8 {𝒞 : FamClass} {C5 : ℝ} (h : FamGLmin 𝒞 C5) (Cabs C0 : ℝ) (hCabs : 0 ≤ Cabs) (hC0 : 3 ≤ C0)
    (hW : ∀ {eps : ℝ} (Fm : FamP eps), 𝒞 Fm → ChosenWall Fm) :
    Closed 𝒞 fun Fm CH => TuSize Fm → DGamSize Fm → LinkGLOBAL Fm Cabs CH C0 Cabs 0 :=
  ((h.link7 Cabs C0 hCabs hC0).and (Closed.of_class (P := fun Fm _ => ChosenWall Fm) fun Fm _ hc => hW Fm hc)).imp
    fun Fm CH _ ⟨l, hWa⟩ hT _ => linkGLOBAL_of_7w Fm Cabs CH C0 Cabs 0 (l hT) hWa

theorem family_theorems_two_and_five {eps : ℝ} (Fm : FamP eps) (hW : FamU Fm fun D u => Nonempty (product_first_zeroth_parts.FreeT D u))
    (hμ : FamU Fm product_first_zeroth_parts.SlopeLine) (hI : FamU Fm LocalLatticeBases.HeckeIntegralLevelZero) (hR : FamU Fm LocalLatticeBases.HeckeRamifiedLevelZero) (hB : FamU Fm LocalLatticeBases.SecondBranchInclusionLength) :
    FamU Fm product_first_zeroth_parts.family_property_and ∧ FamU Fm LocalLatticeBases.CongruenceLatticeLengthBound :=
  ⟨(hW.and hμ).mono fun _ _ hS h => by obtain ⟨⟨W⟩, hm⟩ := h; exact product_first_zeroth_parts.division_side_conditions_at_sizeData hS W hm,
   (hB.and (hI.and hR)).mono fun _ _ hS h => LocalLatticeBases.congruence_no_kernel_minimal hS h.1 h.2.1 h.2.2⟩

theorem FamGLmin.muRank {𝒞 : FamClass} {C5 : ℝ} (h : FamGLmin 𝒞 C5) (C0 : ℝ) (hC0 : 0 < C0) :
    Closed 𝒞 fun Fm CH => TuSize Fm → ChosenE Fm C0 CH → NuFullF Fm ∧ J.MuRank Fm :=
  (h.hW.and (h.hμ.and (h.hI.and (h.hR.and h.hB)))).imp fun Fm _ _ ⟨hW, hμ, hI, hR, hB⟩ hTu hCh => by
    have tSet : SettingEventually Fm := Formalism.L2.GlobalTheoryTheory.Places.settingF_of Fm hTu
    obtain ⟨hT2, hT5⟩ := family_theorems_two_and_five Fm hW hμ hI hR hB
    have hE : J.LvlF Fm := lvlF_of Fm tSet hT2 hT5
    have hNF : NuFullF Fm := nuFullF_of Fm (nuCommensF_min Fm hE)
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, cPr, _⟩ := hCh
    exact ⟨hNF, muRank_min Fm hC0 cPr hNF hE tSet⟩

end Formalism.MainNotions.Wire

namespace Formalism.MainNotions.Wire

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory


end Formalism.MainNotions.Wire

end
