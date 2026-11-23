module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0522
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0595
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0414
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0621
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0723
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0539
public import Development.AutomorphicArithmetic.ResidueCharacters.Bundle0005
public import Development.AutomorphicArithmetic.ResidueCharacters.TbKOf
public import Development.AutomorphicArithmetic.ResidueCharacters.TwistK

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations

theorem UpperTheory.N.locAll_of (hbk : GlobalTheory.Published.BlochKatoLocal) (htd : Formalism.GaloisCohomology.LocalTateDualityK)
    (hec : Formalism.GaloisCohomology.LocalEulerCharK) (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (h54 : LiftingTheory.LiftTheoremAllCases D HW F 23 32 32)
    (hW : ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
      EmbeddingTypeJumps.WachHypothesisLocal (LocalSituation.sit D.loc HW l (D.locA l) K s LL h) ((F l).E K s LL h).tie) :
    UpperTheory.N.LiftK (D.loc l) ∧ UpperTheory.N.InvariantsKilledOverCyclotomic (D.loc l) ∧ UpperTheory.N.TBK (D.loc l) := by
  have hres : ElementDenominator.CrystallineRestrictionToExtension D.loc := _root_.GlobalTheory.Per.ResFinite.adm12_elementDenominator D
  have hF := GlobalTheory.FontaineAll.fontaineAt_all D l
  obtain ⟨_J, hA⟩ := GlobalTheory.LocInputs.ties_and_inputs_of_duality_euler htd hec D HW F
  exact ⟨UpperTheory.N.liftK_of D HW F l h54 hres hF,
    UpperTheory.N.invariants_killed_over_cyclotomic_subfield_of_admissible D HW F l hW (fun K s LL h => GlobalTheory.T.torsion_exponent_kills_invariants_of_good hbk htd hec D HW F Cm l K s LL h) hres hF,
    UpperTheory.N.tbK_of D HW F l (_root_.GlobalTheory.TheoremTBRecords.aux_of_blochKato_tateDuality_eulerChar hbk htd hec D HW F Cm) (_root_.GlobalTheory.crysOnCond_all D HW F) hW
      (UpperTheory.N.TwistK.tbe_all D HW F hA (_root_.GlobalTheory.BlochKatoLocalAllOfTateDualityEulerChar₂.aux_of_blochKato_tateDuality_eulerChar₂ hbk htd hec D) l) hres hF⟩
