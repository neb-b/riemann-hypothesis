module

public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0026
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0028
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0031
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0029
public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.AmpRootCut
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSB

@[expose] public section

namespace Formalism.MainNotions.S.Pv.LemmaJ

theorem relAtPt_holds : RelAtPt := (show PI.AmpRoot.RelAtPt ↔ RelAtPt from Iff.rfl).mp _root_.amplifier_relation_at_point

theorem rootJac_holds : RootJac := (show PI.AmpRoot.RootJac ↔ RootJac from Iff.rfl).mp _root_.amplifier_root_jacobian

theorem rootHaar_holds : RootHaar := (show PI.AmpRootH.RootHaar ↔ RootHaar from Iff.rfl).mp _root_.amplifier_root_haar

theorem exists_orbQuot₂ : OrbQuotEx := (show PI.AmpOrbQ.OrbQuotEx ↔ OrbQuotEx from Iff.rfl).mp (_root_.orbQuotEx_of_haarLieN (show PI.AmpOrbQ.HaarLieN from Formalism.MainNotions.BridgeCSB.haarLieN))

end Formalism.MainNotions.S.Pv.LemmaJ
