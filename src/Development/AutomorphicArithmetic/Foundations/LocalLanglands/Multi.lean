module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.Outright
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalLanglandsExistence.LanglandsDataDualGLOfCosocle
public import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.EssSquareIntegrableSegmentsHolds
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.PublishedTheoremStatements.Bundle0001
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.PublishedTheoremStatements.BridgesMore
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0616

@[expose] public section

namespace UpperTheory.Zero.LLC.Pr

theorem exh : GlobalTheory.Published.LanglandsExhaustionGL := PositivityTheory.Exh.langlandsExhaustionGL_holds
theorem multi : GlobalTheory.Published.LanglandsMultisegments := PositivityTheory.Exh.langlandsMultisegments_holds
theorem cos : GlobalTheory.Published.StandardCosocleGL := PositivityTheory.Exh.standardCosocleGL_holds
theorem bz : GlobalTheory.Published.BernsteinZelevinskyFiniteness := PositivityTheory.Prw.bernsteinZelevinskyFiniteness_holds
theorem zel : GlobalTheory.Published.ZelevinskyPolynomialRing :=
  PositivityTheory.Prw.zelevinskyPolynomialRing_of bz PositivityTheory.RgGu.segmentRepresentation PositivityTheory.Groth.grothendieckRingPolynomial_holds
theorem dual : GlobalTheory.Published.LanglandsDataDualGL := PositivityTheory.Pf1.LocalLanglands.LDual.langlandsDataDualGL_of_cosocle cos
theorem adm : GlobalTheory.Published.IrreducibleAdmissibleGL := PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
theorem dzs : GlobalTheory.Published.DepthZeroSupport := GlobalTheory.SmGL.depthZeroSupport

end UpperTheory.Zero.LLC.Pr
