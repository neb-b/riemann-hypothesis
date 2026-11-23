module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.UnipotentInLevelSubgroup
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.FinLevi
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0055
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabMajPtPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0047
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FixedDecomposition
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0027
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0022
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.HostUnram
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0013
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0009
public import Formalism.PeriodIntegrals.Bundle0014
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormExpSatHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdCellOffCHoldsOfVol

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.Pf Formalism.L2.SG.TermOp.Vanish

namespace Formalism.L2.SG.Closed

theorem FinLeviC_holds : Formalism.L2.SG.Pf.FinLeviC := Formalism.L2.SG.Pf.FinLeviPf.finLeviC_holds

theorem FoldOKC_outright : FoldOKC := FoldOKC_holds FinLeviC_holds

theorem OOLintSumC_holds : Formalism.L2.SG.Pf.OOLintSumC :=
  Formalism.L2.SG.Pf.ooLintSumC_holds_slab Formalism.L2.SG.Pf.SlabMajPt.pointwise_majorant_by_columns Formalism.L2.SG.Pf.SlabCount.countC_holds

theorem OOIntAllC_outright : OOIntAllC := OOIntAllC_holds OOLintSumC_holds

theorem AbsConvC_outright : AbsConvC := AbsConvC_holds OOLintSumC_holds

theorem KppOffC_holds : Formalism.L2.SG.RowsConc.KppOffC :=
  Formalism.L2.SG.FixedDecomposition.kppOffC_of_steps0 FoldOKC_outright FundExistsC_holds OOIntAllC_outright LemmaVC_holds
    (Formalism.L2.SG.FixedDecomposition.covariantRepZero_of_lemmaV AvgCore_holds Formalism.L2.SG.Pf.ginfUnimod_holds Formalism.L2.SG.Pf.nLamNinf_holds
      ChiTrivialC_holds Formalism.L2.SG.Pf.psiInfChar_holds Formalism.L2.SG.Pf.rClosedC_holds Formalism.L2.SG.Pf.roDiscreteC_holds
      Formalism.L2.SG.TermOp.Vanish.rational_cocompact_holds)
    schurNFC

theorem LocHaarC_holds : Formalism.L2.SG.Pf.LocCP.LocHaarC := by
  intro D _ p
  obtain ⟨μ, h1, h2, h3⟩ := local_haar_real_real _ _ _ _ (D.s.atP p) (Formalism.L2.SG.Pf.LocCP.reduced p)
  refine ⟨μ, h1, h2, ?_⟩
  have hR : Formalism.L2.SG.Pf.LocCP.RR p = PI.LocHaarRR.RR (D.s.atP p) := by
    unfold Formalism.L2.SG.Pf.LocCP.RR PI.LocHaarRR.RR
    cases (D.s.atP p).split <;> rfl
  rw [hR]
  exact h3

theorem PinHostC_holds : Formalism.L2.SG.Pf.LocCP.PinHostC :=
  fun D hT p i hi => prime_quotient_unit _ _ _ _ (D.s.atP p) D.host.g D.host.g_prime D.host.g_ne i hi
    (Formalism.L2.SG.Pf.HostUnramP.hostUnramG D hT p i hi)

theorem LocDualGenC_holds : Formalism.L2.SG.Pf.LocCP.LocDualGenC := fun D _ p => local_dual_generation _ _ _ _ (D.s.atP p)

theorem LocCTied_holds : Formalism.L2.SG.Pf.FullLocalDualAgreement.LocalDualAgreement :=
  Formalism.L2.SG.Pf.FullLocalDualAgreement.locCTied_of' (Formalism.L2.SG.Pf.FullLocalDualAgreement.locDualC_of' LocDualGenC_holds PinHostC_holds)
    LocHaarC_holds

end Formalism.L2.SG.Closed
