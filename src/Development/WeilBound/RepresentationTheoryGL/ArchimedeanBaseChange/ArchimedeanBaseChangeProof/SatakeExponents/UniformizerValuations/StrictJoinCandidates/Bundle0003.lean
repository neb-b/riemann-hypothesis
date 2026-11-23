module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.Bundle0002
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0275
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0559
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfNonNil
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.CompFixSAlt
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FX

open PositivityTheory.Rg.BcB.F

def ExTb : Prop := ∀ (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n →
  ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ (S : Finset (Pl E)) (F₀ : Frame0 hR π S) (T : Finset (Pl E)),
  ∃ (T' : Finset (Pl E)) (b : ∀ w : Pl E, GLw n w), T'.Nonempty ∧
    (∀ w ∈ T', w ∈ F₀.Sec ∧ ¬ IsSplitAt w ∧ IsUnramU π w ∧ IsWitt n w (b w) ∧ w ∉ F₀.d₀.S₀ ∧ w ∉ F₀.d₀.Bad) ∧
    (∀ w, w ∉ T' → b w = F₀.d₀.b w) ∧ ∀ w ∈ T, IsUnramU π w → ¬ IsSplitAt w → w ∈ T'

def ExTbOf : Prop := Inert.InertPlaceEx → Inert.WittEx → InertInSec → ExTb

end PositivityTheory.Rg.BcB.F.FX

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.FixFin
section
noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BCT
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FX

open PositivityTheory.Rg.BcB.F

theorem fixFin : FixFin := by
  intro E _ _ _ n D w K hKo hKc
  have hs : IsSmooth (Tail.prodAt D w) := GlobalTheory.SmGL.isSmooth_parInd _ _
  have hfl : HasFiniteLength (Tail.prodAt D w) :=
    _root_.GlobalTheory.CompanionTheory.ProdLen.prodFinLen (w.adicCompletion E) (Fin n) (Fin D.c) (fun i => Fin (D.N i)) (GlobalTheory.SmGL.stdBlocks D.N D.h)
      (fun i => (D.σ i w).V) (fun i => (D.σ i w).ρ) (fun i => (D.σ i w).smooth) (fun i => (D.σ i w).irred)
  have hadm : IsAdmissible (Tail.prodAt D w) :=
    _root_.GlobalTheory.CompanionTheory.AdmFL.isAdmissible_of_hasFiniteLength (Tail.prodAt D w) hs hfl fun W _ _ σ hsub hirr =>
      PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top (w.adicCompletion E) n W σ (hsub.isSmooth hs) hirr
  exact hadm.2 K hKo hKc

end PositivityTheory.Rg.BcB.F.FX

end
end

