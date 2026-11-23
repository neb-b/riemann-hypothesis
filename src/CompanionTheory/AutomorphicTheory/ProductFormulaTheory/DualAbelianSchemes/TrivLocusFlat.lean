module

public import Mathlib
public import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CechFlatComplex
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SpecMapAppFromSpec
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0064
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsPointOfIsAffine
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0737
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.RigDescent
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsIdPowEqOneOfIsFiniteOfFlat
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0062
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1280
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0396
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0177
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0068
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0066
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.AppTopCompApply
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.DualAbelianSchemes.Bundle0001
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.DualAbelianSchemes.TrivLocus
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.DualAbelianSchemes.PointSurj
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.DualAbelianSchemes.FewEqBridge
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.AbelianDeRham.FreeAbelianDeRham.H1StructureDimLe

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus

attribute [local instance] Over.cartesianMonoidalCategory

namespace CompanionTheory.PfDual

theorem h1Le : H1StructureDimLe := MainStatements.Hodge.Free.h1Le

theorem trivLocus : TrivLocus := trivLocus_pf

theorem fewEquations : FewEquations := fewEquations_pf h1Le

theorem ciFlat : CIFlat := _root_.GlobalTheory.CompanionTheory.CIFlatPf.ciFlat

theorem trivLocusFlat : TrivLocusFlat := @GlobalTheory.CompanionTheory.TrivFlat.trivLocusFlat fewEquations ciFlat

theorem pointSurj : PointSurj := pointSurj_pf addAcyclic_pf

theorem finDual : FinDual := @GlobalTheory.CompanionTheory.DualAb.finDual_of_univNoeth (@GlobalTheory.CompanionTheory.DualUniv.univNoeth trivLocus trivLocusFlat pointSurj)

theorem kTrivModel : KTrivModel := @GlobalTheory.CompanionTheory.KTrivSpread.kTrivModel_of_trivLocus trivLocus

theorem kTrivDual : KTrivDual := @GlobalTheory.CompanionTheory.DualScheme.ktrivDual kTrivModel finDual

end CompanionTheory.PfDual
