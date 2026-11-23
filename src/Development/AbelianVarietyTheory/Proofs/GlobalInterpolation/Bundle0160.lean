module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Formalism.SharpRestriction.GlobalSchurBounds.LinkTied
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0127
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0140
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0471
public import Formalism.LocalToGlobal.HermitianForms.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0005
public import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0144
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdmissiblePeriodZeroOfClassPeriodDecompositionAl
public import Formalism.SharpRestriction.Divisibility.StatementFT.PeriodPointConditions

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsSymmetricColumnFormsStepZeroFiniteCharacte
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC

theorem colsTiedSym_chiFin0 : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∃ C : ColsTiedSym (I.rec7 l Z), ∀ u, Formalism.MainNotions.RT.ChiFin0 (C.forms u) := by
  intro B X I hI hP l Z
  obtain ⟨C, -, -⟩ := _root_.GlobalTheory.Mem.Col2.TC.colsTiedSym_std I hI hP l Z
  refine ⟨C, fun u => ?_⟩
  exact GlobalTheory.formsTiedSym_chi_zero_finite (I.rec7 l Z) u _ _ (C.forms u)
    (fun i => _root_.GlobalTheory.trueCols_exists_primitiveRoots I hI l Z i)

end GlobalTheory.Mem.Col2.TC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PeriodAdmissibleOfIntegralPeriodRows
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.PerAdm0.periodAdmissible_of_integralPeriodRows : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), GlobalTheory.PerQ.RowInt I l Z → Formalism.MainNotions.WeightDegreeSizes.PeriodClassSumWeyl (I.rec7 l Z) := by
  intro B X I hI hP l Z hR
  obtain ⟨C, hC, _⟩ := _root_.GlobalTheory.Mem.Col2.TC.colsTiedSym_std I hI hP l Z
  exact _root_.GlobalTheory.PerRed.periodClassSumWeyl_of_forall_perDec0 _ (Formalism.MainNotions.RT.PeriodPointConditions.perDec0_of_cols C
    (fun u => GlobalTheory.PerDecAtRef.perDec0At_std I hI l Z hR u _ _ (C.forms u) (hC u)))
end

