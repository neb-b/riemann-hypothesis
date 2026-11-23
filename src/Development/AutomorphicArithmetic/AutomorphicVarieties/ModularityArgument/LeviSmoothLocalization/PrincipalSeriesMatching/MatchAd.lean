module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.AdjointEta.EtaOK
public import Mathlib
public import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdFormOf
public import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.WhittakerModelGL2
public import GroundTheory.AutomorphicForms.MeasuresGL
public import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.EulerProducts.GenStable
public import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.GammaZeroLevelMembership
public import GroundTheory.GlobalFields.CompletionAtPlace
public import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdelicGaussians.UpperRightUnipotentInvariance
public import GroundTheory.GlobalFields.AnalyticClassNumber.DirichletHeckeCorrespondence
public import GroundTheory.GlobalFields.Artin.OneDim
public import GroundTheory.GlobalFields.Artin.Series
public import GroundTheory.GlobalFields.ExistenceTheorem.ExistsIsAbelianGaloisRangeIdeleClassNormEqOfFini
public import GroundTheory.GlobalFields.NormResidueSymbol.RestrictNormalInfiniteLocalSymbol
public import GroundTheory.GlobalFields.Artin.Places
public import GroundTheory.GlobalFields.Artin.InflationTower
public import GroundTheory.GlobalFields.AnalyticClassNumber.HeckeContinued
public import GroundTheory.LocalFields.Bundle0001
public import GroundTheory.GlobalFields.TateThesis.Bundle0006
public import GroundTheory.GlobalFields.TateThesis.DedekindZetaContinuation
public import GroundTheory.LocalFields.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0699
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecTransportFieldIso
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0731
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0205
public import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0141
public import GroundTheory.GlobalFields.TateThesis.DedekindContinuation
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0580
public import GroundTheory.GlobalFields.ClassFieldConsequences.TrivialModulus
public import GroundTheory.GlobalFields.GlobalReciprocity.General
public import GroundTheory.GlobalFields.ClassFieldConsequences.RayClassFieldLocal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EulerProductInductionSupported
public import GroundTheory.GlobalFields.AnalyticClassNumber.DirichletHeckeLocal
public import GroundTheory.GlobalFields.TateThesis.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.GlobTw
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.SuppFacts

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.SmGL
open UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter GlobalTheory.HenQ UpperTheory.V.Z.Inf UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.Ad
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.LocalField
open GroundTheory.Automorphic.GodementSection (localChar)
open Ad3P.DihedralUnramifiedPlaces (toH)
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.Ad

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem unr_mul {a b : kˣ →* ℂˣ} (ha : IsUnram a) (hb : IsUnram b) : IsUnram (a * b) := fun x hx => by
  rw [MonoidHom.mul_apply, ha x hx, hb x hx, one_mul]

private theorem unr_inv {a : kˣ →* ℂˣ} (ha : IsUnram a) : IsUnram a⁻¹ := fun x hx => by
  rw [MonoidHom.inv_apply, ha x hx, inv_one]

end Loc

end UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.Ad

