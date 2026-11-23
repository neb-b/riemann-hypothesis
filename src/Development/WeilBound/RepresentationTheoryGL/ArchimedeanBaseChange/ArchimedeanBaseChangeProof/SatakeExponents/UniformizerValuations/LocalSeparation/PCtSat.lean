module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalSeparation.PCtSatB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1090
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1124
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1107
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1145
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1159
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1147
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1155
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1091
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1082
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1100
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1178
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1719

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.RS

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem ordL_unif {w : Pl E} {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) : ordL ϖ = 1 := by
  have h1 : Valued.v ϖ ≠ 0 := by rw [hϖ]; exact WithZero.coe_ne_zero
  unfold ordL
  rw [dite_eq_right h1]
  have e : WithZero.unzero h1 = Multiplicative.ofAdd (-1 : ℤ) := by
    rw [← WithZero.coe_inj, WithZero.coe_unzero, hϖ]
  rw [e, toAdd_ofAdd, neg_neg]

theorem ord_neg_one' {w : Pl E} : GlobalTheory.SmGL.ord (w.adicCompletion E) (-1) = 0 := by
  rw [GlobalTheory.BCT.InertChar.ord_eq_ordL]
  have : Valued.v ((((-1 : (w.adicCompletion E)ˣ)) : w.adicCompletion E)) = 1 := by simp
  have h1 : Valued.v ((((-1 : (w.adicCompletion E)ˣ)) : w.adicCompletion E)) ≠ 0 := by rw [this]; exact one_ne_zero
  unfold ordL
  rw [dite_eq_right h1]
  have e : WithZero.unzero h1 = 1 := by
    rw [← WithZero.coe_inj, WithZero.coe_unzero, this]; rfl
  rw [e, toAdd_one, neg_zero]

end PositivityTheory.Rg.BcB.F.RS
