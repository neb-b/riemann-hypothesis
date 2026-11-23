module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.HeightInequalitiesIndefiniteLiftIndex
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0035
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0043
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0037
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0039
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0028
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.HeightInequalityDefiniteLiftIndex
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.OntoAlong
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.CoreTiesOfTied

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.HeightInequalitiesIndefiniteLiftIndexStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heightInequalities_indefinite_liftIndex : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) [Fintype (Comp (T.Q.Xo j) T.Q.c)] (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (S : Scal (recB h.toLawsCore)) (g0 : (recB h.toLawsCore).Cusp j wF), CurveHyp h j hj hG ka wL wF G S g0 → GenValInjSt h j hG → CompSplitSt h j hG → BIRSt h j hj hG G → ∀ (y : ∀ la, PtsG G la → (extAll h j hj).Pt' la) (hw : ∀ la ζ, FromW (E := extAll h j hj) (hM := intAtExt_extAll h j hj) ζ (y la ζ)), (∀ la, (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0).InCurve) → (∀ la, (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0).InTie S) → j < D.R.m → FnAlgClosed (Xo := (T.Q.Xo j)) (c := T.Q.c) → 3 ≤ WeightFamilies.dimY D j → 0 < wL.n → (∀ la, InBasis G la) → ∀ (large₂ : SizeData₂ D) (Gc PH Prw Pet PN' PP0' PI4' tableLineDegreeFive tableLineDegreeTwo POb CL AL : ℝ) (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ) (w2 : WeightFamilies.Wt D j) (t2 : (recB h.toLawsCore).Cusp j w2), G.TiedW S Gc Prw → G.TiedTh S Gc → (∀ i, G.th' i ∈ (recB h.toLawsCore).Mlat j wF) → IsG2 wL wF w2 → t2 ∈ (recB h.toLawsCore).Mlat j w2 → (recPlus h j hj).NonZeroComp w2 t2 → (∀ σ, Real.log ((recB h.toLawsCore).supN j w2 σ t2) ≤ PI4' * (WeightFamilies.dimY D j : ℝ) * wL.size) → WeightedPrimeSumBoundAlt large₂ (recPJ h j hj) wL nus → WeightAlgebra.PN D large₂ ≤ PN' → LAMwAt large₂ (recB h.toLawsCore) j (wsmul (8 * ((WeightFamilies.dimY D j + 2) * G.N) ^ 2 * (WeightFamilies.dimY D j + 1) * G.del * (1 + ⌈POb⌉₊)) wL) CL AL → LamConst j large₂ CL AL (wsmul (8 * ((WeightFamilies.dimY D j + 2) * G.N) ^ 2 * (WeightFamilies.dimY D j + 1) * G.del * (1 + ⌈POb⌉₊)) wL) PP0' (8 * ((WeightFamilies.dimY D j + 2) * G.N) ^ 2 * (WeightFamilies.dimY D j + 1) * G.del * (1 + ⌈POb⌉₊)) wL.size → 1 ≤ wL.size → (WeightAlgebra.DF wL : ℝ) ≤ wL.size → Real.log G.N + 1 / 2 ≤ Prw * (wL.size - 1) → Real.log (Module.finrank ℚ T.Q.c.F) ≤ POb → Real.log (|(NumberField.discr T.Q.c.F : ℝ)| ^ (1 / (Module.finrank ℚ T.Q.c.F : ℝ))) ≤ POb → 1 ≤ PN' → 1 ≤ PP0' → 1 ≤ Gc → 1 ≤ PI4' → 1 ≤ Pet → 1 ≤ tableLineDegreeFive → 1 ≤ tableLineDegreeTwo → 1 ≤ Prw → 1 ≤ POb → PH = 2 * (PP0' + PN' + tableLineDegreeFive + tableLineDegreeTwo + PI4' + Prw) + Gc → ∀ (c th : ℝ) (w1 : WeightFamilies.Wt D j) (t1 : (recB h.toLawsCore).Cusp j w1), IsDoubledWeightWithShift wL w1 wL.n → t1 ∈ (recB h.toLawsCore).Mlat j w1 → (recPlus h j hj).NonZeroComp w1 t1 → (∀ σ, Real.log ((recB h.toLawsCore).supN j w1 σ t1) ≤ 2 * PI4' * (WeightFamilies.dimY D j : ℝ) * wL.size) → 0 < G.iet → G.et ∈ (recB h.toLawsCore).Mlat j _ → (recPlus h j hj).NonZeroComp _ G.et → (∀ σ, Real.log ((recB h.toLawsCore).supN j _ σ G.et) / G.iet ≤ Pet) → 0 ≤ c → c * (WeightAlgebra.g0 D : ℝ) ≤ 1 / 2 → CombAlg (T.Q.Xo j) T.Q.c (fun k => (G.w k).1) G.et.1 nus (c / (2 * (G.iet : ℝ))) → (∀ σ, GoodEmb T.Q.c σ → ∀ (k : (T.U j σ).Comp) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame ((T.U j σ).X k).Ψ D.R.r), x ∈ ((T.U j σ).X k).dom → -Real.log (Real.sqrt (∑ k', recNrm (T.U j σ) (xiR D) (wtA wL) wL.n (G.w k').1 k x ^ 2)) ≤ tableLineDegreeFive * (WeightAlgebra.DF wL : ℝ) + c * ReciprocityTheory.ChartRestriction.G.I2.phiFD ((T.U j σ).X k) th x) → EtArch h th tableLineDegreeTwo j G.iet G.et → Heights (fun la => (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0)) Gc PH Prw Pet := by
  first | exact @GlobalTheory.HeightTop.heights_indefinite | exact GlobalTheory.HeightTop.heights_indefinite | (intros; apply GlobalTheory.HeightTop.heights_indefinite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.HeightInequalityDefiniteLiftIndexStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heightInequality_definite_liftIndex : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) [Fintype (Comp (T.Q.Xo j) T.Q.c)] (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (S : Scal (recB h.toLawsCore)) (g0 : (recB h.toLawsCore).Cusp j wF), CurveHyp h j hj hG ka wL wF G S g0 → GenValInjSt h j hG → CompSplitSt h j hG → BIRSt h j hj hG G → ∀ (y : ∀ la, PtsG G la → (extAll h j hj).Pt' la) (hw : ∀ la ζ, FromW (E := extAll h j hj) (hM := intAtExt_extAll h j hj) ζ (y la ζ)), (∀ la, (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0).InCurve) → (∀ la, (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0).InTie S) → j = D.R.m → FnAlgClosed (Xo := (T.Q.Xo j)) (c := T.Q.c) → 3 ≤ WeightFamilies.dimY D j → 0 < wL.n → (∀ la, InBasis G la) → ∀ (large₂ : SizeData₂ D) (Gc PH Prw Pet PN' PP0' PI4' tableLineDegreeFive tableLineDegreeTwo POb CL AL : ℝ) (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ) (w2 : WeightFamilies.Wt D j) (t2 : (recB h.toLawsCore).Cusp j w2), G.TiedW S Gc Prw → G.TiedTh S Gc → (∀ i, G.th' i ∈ (recB h.toLawsCore).Mlat j wF) → IsG2 wL wF w2 → t2 ∈ (recB h.toLawsCore).Mlat j w2 → (recPlus h j hj).NonZeroComp w2 t2 → (∀ σ, Real.log ((recB h.toLawsCore).supN j w2 σ t2) ≤ PI4' * (WeightFamilies.dimY D j : ℝ) * wL.size) → WeightedPrimeSumBoundAlt large₂ (recPJ h j hj) wL nus → WeightAlgebra.PN D large₂ ≤ PN' → LAMwAt large₂ (recB h.toLawsCore) j (wsmul (8 * ((WeightFamilies.dimY D j + 2) * G.N) ^ 2 * (WeightFamilies.dimY D j + 1) * G.del * (1 + ⌈POb⌉₊)) wL) CL AL → LamConst j large₂ CL AL (wsmul (8 * ((WeightFamilies.dimY D j + 2) * G.N) ^ 2 * (WeightFamilies.dimY D j + 1) * G.del * (1 + ⌈POb⌉₊)) wL) PP0' (8 * ((WeightFamilies.dimY D j + 2) * G.N) ^ 2 * (WeightFamilies.dimY D j + 1) * G.del * (1 + ⌈POb⌉₊)) wL.size → 1 ≤ wL.size → (WeightAlgebra.DF wL : ℝ) ≤ wL.size → Real.log G.N + 1 / 2 ≤ Prw * (wL.size - 1) → Real.log (Module.finrank ℚ T.Q.c.F) ≤ POb → Real.log (|(NumberField.discr T.Q.c.F : ℝ)| ^ (1 / (Module.finrank ℚ T.Q.c.F : ℝ))) ≤ POb → 1 ≤ PN' → 1 ≤ PP0' → 1 ≤ Gc → 1 ≤ PI4' → 1 ≤ Pet → 1 ≤ tableLineDegreeFive → 1 ≤ tableLineDegreeTwo → 1 ≤ Prw → 1 ≤ POb → PH = 2 * (PP0' + PN' + tableLineDegreeFive + tableLineDegreeTwo + PI4' + Prw) + Gc → (∀ la, ∀ v ∈ valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c) la, (⨅ k, v (G.w k).1) ≤ (nus la : EReal)) → (∀ σ, GoodEmb T.Q.c σ → ∀ (k : (T.U j σ).Comp) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame ((T.U j σ).X k).Ψ D.R.r), x ∈ ((T.U j σ).X k).dom → -Real.log (Real.sqrt (∑ k', recNrm (T.U j σ) (xiR D) (wtA wL) wL.n (G.w k').1 k x ^ 2)) ≤ tableLineDegreeFive * (WeightAlgebra.DF wL : ℝ)) → Heights (fun la => (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0)) Gc PH Prw Pet := by
  first | exact @GlobalTheory.HeightDefinite.heights_definite | exact GlobalTheory.HeightDefinite.heights_definite | (intros; apply GlobalTheory.HeightDefinite.heights_definite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.MoreOfTiesB
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlugPt

theorem more_of_tiesB : ∀ (D : D7) (O : GlobalTheory.EX.OB.Obj D) (c : ℝ) (b : BdPt D O c),
    TiesB D O c b → FieldSmall D O.L → SingleIndexPlacesAreTwisted b → More b := by
  intro D O c b hT hS hW
  obtain ⟨hs, hr⟩ := hT
  refine ⟨hW, ?_, ?_⟩
  · exact GlobalTheory.Plug.coreTies_of_tied D _ _ _ _ O.L O.ex.errX b.T (R2 b) b.P.A3.A.μ0 hs.tied b.charW.base.lev hS
  · exact ⟨hs.series, hs.level, hs.data, hs.psi, hs.psiVal, hs.small, hs.types, hr⟩

end GlobalTheory.PlugPt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.PathCoreConditionsOfSizeFreeConditions
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlugPt

theorem ties_core_of_tiesB : ∀ (D : D7) (O : GlobalTheory.EX.OB.Obj D) (c : ℝ) (b : BdPt D O c), TiesB D O c b → FieldSmall D O.L →
    CoreTies O.L O.ex.errX b.T b.R.toRealDat ∧ b.T.pb = b.R.C.P.pb ∧ GlobalTheory.GLq.ESerTie D ∧ b.LevelTie ∧ b.DataTie := by
  intro D O c b h hF
  obtain ⟨hT, -⟩ := h
  refine ⟨GlobalTheory.Plug.coreTies_of_tied D _ _ _ _ O.L O.ex.errX b.T b.R.toRealDat _ hT.tied b.charW.base.lev hF,
    hT.tied.core.pb, hT.types.eSerTie, hT.level, hT.data⟩

end GlobalTheory.PlugPt
end

