module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0002
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1277
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.InertFrames.OrdLEqOne
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Inert

namespace UniformizerValuation

theorem ordL_eq_one {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {x : L}
    (hx : Valued.v x = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) :
    ordL x = 1 := by
  unfold ordL
  have h0 : Valued.v x ≠ 0 := by rw [hx]; exact WithZero.coe_ne_zero
  rw [dite_eq_right h0]
  have hu : WithZero.unzero h0 = Multiplicative.ofAdd (-1 : ℤ) :=
    WithZero.coe_injective ((WithZero.coe_unzero h0).trans hx)
  rw [hu]
  simp

end UniformizerValuation

theorem unifEx : UnifEx := by
  intro E _ _ _ hU w hw
  obtain ⟨-, -, -, h4, -⟩ := _root_.GlobalTheory.ConjAtPlace.main E hU w
  obtain ⟨ϖ, q, hI, -⟩ := (h4 hw).2.1
  have hv : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) :=
    hI.2.2.2.1
  have h0 : ϖ ≠ 0 := by
    intro h
    rw [h, map_zero] at hv
    exact WithZero.coe_ne_zero hv.symm
  refine ⟨Units.mk0 ϖ h0, q, ⟨?_, ?_⟩, ?_⟩
  · exact UniformizerValuation.ordL_eq_one hv
  · exact hI.2.2.1
  · exact hI

end PositivityTheory.Rg.BcB.F.Inert

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.InertFrames.UnifOfP
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Inert

namespace UniformizerOfValuationOne

theorem v_of_ordL_eq_one {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {x : L}
    (hx0 : x ≠ 0) (hx : ordL x = 1) :
    Valued.v x = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  have h0 : Valued.v x ≠ 0 := by
    intro h
    exact hx0 ((Valuation.zero_iff _).mp h)
  unfold ordL at hx
  rw [dite_eq_right h0] at hx
  have hu : WithZero.unzero h0 = Multiplicative.ofAdd (-1 : ℤ) := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_ofAdd]
    omega
  rw [← WithZero.coe_unzero h0, hu]

end UniformizerOfValuationOne

theorem unifOf : UnifOf := by
  intro E _ _ _ hU w hw ϖ hϖ
  obtain ⟨-, -, -, h4, -⟩ := _root_.GlobalTheory.ConjAtPlace.main E hU w
  obtain ⟨ϖ₀, q, hI, -⟩ := (h4 hw).2.1
  refine ⟨q, hI.1, hI.2.1, hϖ.2, ?_, hI.2.2.2.2⟩
  exact UniformizerOfValuationOne.v_of_ordL_eq_one (Units.ne_zero ϖ) hϖ.1

end PositivityTheory.Rg.BcB.F.Inert

end
end

