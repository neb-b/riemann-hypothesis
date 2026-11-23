module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.DataParams
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.WeaklyAdmissibleFiltrations.Statement
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065

@[expose] public section

noncomputable section

namespace GlobalTheory.SmallJumpExample

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.FrobeniusOrbits GlobalTheory.HTW GlobalTheory.IndefiniteRowSideFullHecke
open scoped Formalism.Per

theorem isField_bdR (D : D7) (l : ℕ) [Fact l.Prime] : IsField (D.loc l).R.BdR :=
  MulEquiv.isField (GlobalTheory.MemLoc.BdRField.bdR_isField l).2.2.1 (D.locT l).eD.toMulEquiv

section Count

variable {R : Ranks} (P : HCParam R) (j : Fin R.m) (s : Bool) (n : ℕ)

end Count

variable {D : D7} (L : SizeData₂ D)

end GlobalTheory.SmallJumpExample
