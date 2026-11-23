module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.GlnSuff
public import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.Bundle0005
public import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.TCosocleUnit
public import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.GlnTCentred
public import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.GlnTOrderfree
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Development
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0364
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0619
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0616
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.GKLocal
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0353
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SquareIntegrableSegments.SegmentSubquotients.ExistsSegmentRepresentation
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL

namespace UpperTheory.Lit.Cas

theorem temperedProduct (hG : GlobalTheory.Published.GeometricLemma) (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness)
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hF : GlobalTheory.Published.StandardFunctorsFiniteLength)
    (hE : GlobalTheory.Published.LanglandsExhaustionGL) (hC : GlobalTheory.Published.StandardCosocleGL) (hM : GlobalTheory.Published.LanglandsMultisegments)
    (hS : GlobalTheory.Published.EssSquareIntegrableSegments) : GlobalTheory.Published.TemperedProductOfSquareIntegrable := by
  intro k _ _ _ _ _ N hN V _ _ π hs hi
  constructor
  · intro ht
    have hO : Zc.LOrderFree k := orderfree hC hM k
    have hSo : Zc.LSocleGL k := _root_.GlobalTheory.CompanionTheory.LSocle.lSocleGL hA (_root_.GlobalTheory.CompanionTheory.GKLocalProof.gkLocal hA) hO
    have hL : Zc.LSegExists k := fun Δ => _root_.GlobalTheory.CompanionTheory.LkSegExists.exists_isLSeg hA Δ
    obtain ⟨𝔪, h𝔪⟩ := hE k (IrrGL.of π hs hi)
    have h𝔪' : IsL 𝔪 π := h𝔪.of_equiv (IrrGL.equivOf π hs hi).symm
    obtain ⟨h, x, hd, hx, hu⟩ := GlobalTheory.T.tempered_langlands_factors_square_integrable k hSo (Zl.JC.casselmanNecTemp_holds k) hL 𝔪 N π hN hs hi ht h𝔪'
    obtain ⟨Δ, hΔo, hΔ⟩ := hx
    have hsq : ∀ a, IsSqIntCoeff (x a).rep := fun a => centred hS hA k (Δ a) (x a) (hΔ a) (hu a)
    have e := cosocleUnit hBZ k h N x hd V π (fun a => GlobalTheory.T.square_integrable_unitarizable k (x a) (hsq a)) (hO 𝔪 h N x hd ⟨Δ, hΔo, hΔ⟩ π h𝔪')
    refine ⟨h, x, hd, fun a => ⟨?_, hsq a⟩, e⟩
    have h1 := (hΔ a).deg_eq
    have h2 := Nat.mul_pos (Δ a).len_pos (Δ a).d_pos
    simp only [Segment.deg] at h1
    omega
  · rintro ⟨h, δ, hd, hδ, e⟩
    obtain ⟨hu, hw⟩ := prodExp hG hBZ hA k (Zl.JC.casselmanNecSq_holds k) h N δ hd hδ V π hi e
    have H := casselmanSuffTemp hA hF k N π hN hs hi hu hw
    intro ε hε
    exact H ε hε

end UpperTheory.Lit.Cas

end
