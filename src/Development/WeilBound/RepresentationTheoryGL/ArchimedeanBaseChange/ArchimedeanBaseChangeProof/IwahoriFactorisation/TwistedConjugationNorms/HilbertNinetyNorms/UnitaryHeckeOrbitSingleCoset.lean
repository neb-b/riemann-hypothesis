module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.OneCoset
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0577
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0552
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0551

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Polynomial Matrix
open GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.Bc.ArchbcB.B.M4

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem unitary_hecke_orbit_single_coset (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (n : ℕ) (b : GLw n w) (hb : IsWitt n w b)
    (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifAt ϖ) (l : Fin (n / 2) → ℤ) (hl : Cone l) (γ : UL n w)
    (hP : ∃ p : UL n w, fU n w b ϖ l (p⁻¹ * γ * p) ≠ 0) :
    (∃ p₀, OneCoset (MonoidHom.id (UL n w)) (iwU n w b) γ {g | fU n w b ϖ l g ≠ 0} p₀) ∧
      CentOK (MonoidHom.id (UL n w)) (KL n w) (iwU n w b) γ ∧ HasVals γ.1.val.charpoly (wexp n l) := by
  obtain ⟨p₀, u, h1, -, h3, h4, h5⟩ := s2raw hU w hw n b hb ϖ hϖ l hl γ hP
  obtain ⟨-, hKc, hI, -, -⟩ := _root_.GlobalTheory.CompanionTheory.IwLevels.levels_unitary E hU w hw n b hb ϖ l hϖ hl
  have hIc : IsCompact (iwU n w b : Set (UL n w)) := (_root_.GlobalTheory.CompanionTheory.UnitaryWitt.unitary_hyperbolic_basis E hU w hw n b hb).2.2.1
  have hC : IsCompact (((iwU n w b).map (MulAut.conj p₀).toMonoidHom : Subgroup (UL n w)) : Set (UL n w)) := by
    rw [Subgroup.coe_map]
    exact hIc.image ((continuous_const.mul continuous_id).mul continuous_const)
  refine ⟨⟨p₀, h3, h4.le.trans inf_le_right⟩,
    _root_.GlobalTheory.CompanionTheory.CentOk.centraliser_hyps (UL n w) (MonoidHom.id _) continuous_id _ _ _ γ hKc hI.1 hC h4,
    fun i => (u i : w.adicCompletion E), h5, fun i => ⟨(u i).ne_zero, h1 i⟩⟩

end PositivityTheory.Rg.Bc.ArchbcB.B.M4
