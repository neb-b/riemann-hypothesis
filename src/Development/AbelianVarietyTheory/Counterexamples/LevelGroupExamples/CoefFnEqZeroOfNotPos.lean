module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0039
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MaxCuspMemCuspFormsOfKilledCoefZero
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0037
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HyperbolicFlagDataBasePoint
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0025
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.MaxCuspsTie
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0036
public import Formalism.LocalToGlobal.ProjectiveLattices.XcLat
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Formalism.LocalToGlobal.ProjectiveLattices.UnifDom
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0003

@[expose] public section

noncomputable section

namespace GlobalTheory.ReadingTieCheck

open NumberField ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj.FJ Formalism.L2.Pj.QAt MeasureTheory GlobalTheory.TorusFourier GlobalTheory.MaxCuspKilled

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}

end Free

section Record

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ)

theorem reading_mem_SS (u : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j u) (k : (T.U j T.σ₀).Comp) :
    rdR h j F k ∈ ((T.U j T.σ₀).X k).SS (laU (T.U j T.σ₀) (wtA u) u.n k) :=
  readings_holomorphic_cuspForms siegelSpaceAlgebra_holds T.good_σ₀ (wtA u) u.n ⟨F.1, cutR_le T.C j u F.2⟩ k

theorem tieRead_iff : TieReadSt h j ↔ ∀ u : WeightFamilies.Wt D j, JInjRd T j (wtA u) u.n :=
  ⟨fun H => H.2, fun H => ⟨reading_mem_SS h j, H⟩⟩

theorem tieRead_holds (hj : InR D j) : TieReadSt h j :=
  (tieRead_iff h j).2 fun u =>
    GlobalTheory.ReadingIndependence.jInjRd_of_laws T h.toLawsCore.toLawsM hj (wtA u) u.n

end Record

end GlobalTheory.ReadingTieCheck
