module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.RunsAlong
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0570
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0032
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0564
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPrimeDataCurveLiftingHeightBounds
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0005
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0040
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0043
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0039
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0037
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0034
public import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0031

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.CoreFrameCompatibleConstructedPoint
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj Formalism.L2.Theta GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Plug
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Plug

theorem tied_cfOf : GlobalTheory.NT.RayField → ∀ (𝒮 : Slots), CoreSlot 𝒮 → ∀ (K : Ctx) (p : WPt 𝒮 K), Tied p.O.ex.errX (cfOf p).J (cfOf p).C := by
  intro hR 𝒮 hcs K p
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact p.x.what₂.r.z.geo.fw.laws
  · exact hcs K p.B p.f p.T p.w p.Z p.x.Wt p.O.p0 p.x.what₂ p.x.rx
  · exact _root_.GlobalTheory.AtMember.fieldTies_of_ksExact hR (p.w.st p.Z) p.f p.w.δ p.w.exact
  · show HalfAt (ofObj p.O).errX (Fr.at (p.w.st p.Z) p.f)
    rw [p.x.errX]
    exact _root_.GlobalTheory.AtMember.conj_gen_mem_frame p.B p.f p.T p.w p.Z p.x.col.toColT

end GlobalTheory.Plug
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPrimeDataCurveLiftingHeightBoundsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primeData_curve_lifting_heightBounds : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (S : Scal (recB h.toLawsCore)) (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ) (CL : ℝ), FnAlgClosed (Xo := (T.Q.Xo j)) (c := T.Q.c) → PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → HypC large₂ (recPJ h j hj) H C2 A2 7 0 CT S ka wL wF Tn nP nW h0 nus → 0 < CL → (∀ w : WeightFamilies.Wt D j, LAMwAt large₂ (recB h.toLawsCore) j w CL 2) → ∀ G : GlobalFamilyData (recPJ h j hj) ka wL wF, GenOK h j hj large₂ G S (cc D large₂ C2 A2 7 wL) → (j < D.R.m → EtaOK h j hj large₂ wL G.iet G.et) → G.TiedTh S (gcR large₂ (recB h.toLawsCore)) → (∀ la, InBasis G la) → Real.log G.del ≤ 1041 * Zb D large₂ ^ 3 → CombBound G S (cc D large₂ C2 A2 7 wL) nus → ∃ Qf : ∀ la, LocalPointData (gd2Xplus G (extAll h j hj) (intAtExt_extAll h j hj)) la, (∀ la, (Qf la).InCurve) ∧ (∀ la, (Qf la).InTie S) ∧ (∀ la, (Qf la).InLiftC S (gcR large₂ (recB h.toLawsCore)) (prwR large₂) Tn) ∧ Heights Qf (gcR large₂ (recB h.toLawsCore)) (phR large₂ (recB h.toLawsCore) CL wL) (prwR large₂) (WeightFamilies.PPv D large₂ 200000 2) := by
  first | exact @GlobalTheory.RunPrimeData.exists_primeData_heights | exact GlobalTheory.RunPrimeData.exists_primeData_heights | (intros; apply GlobalTheory.RunPrimeData.exists_primeData_heights <;> assumption)
end

