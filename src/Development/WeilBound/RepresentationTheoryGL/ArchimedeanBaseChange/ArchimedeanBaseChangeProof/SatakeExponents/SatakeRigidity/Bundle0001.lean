module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.ThetaOfCsdR
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1033
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0716
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0007
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0012
public import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.ResidualRigidity.AllPlaceRigidityResidual
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0339
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0538
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0513
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0495
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0556
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1068
public import Formalism.LocalToGlobal.PlaceMapInjectivity.MapPlInjective
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.FieldNOf

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.LRCuspCsdb
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Rig.B

open PositivityTheory.Rg.BcB.F

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem infChar_conj {a : ℕ} (P : CuspSub E a) (hn : IsNormalised P) (τ : E →+* ℂ) (m m' : Multiset ℂ)
    (hm : P.HasInfChar τ m) (hm' : P.HasInfChar (ComplexEmbedding.conjugate τ) m') :
    m' = m.map fun z => -(starRingEnd ℂ) z := by
  obtain ⟨μ, h1, h2⟩ := GlobalTheory.CompanionTheory.AdelicHaar.exists_haar_rightInvariant E a
  have := h1
  have := h2
  obtain ⟨B, hB⟩ := GlobalTheory.CompanionTheory.ClozelHerm.exists_isHerm GlobalTheory.CompanionTheory.CuspFinGL.cuspFormsBoundedGL E a μ P hn
  exact GlobalTheory.CompanionTheory.Clozel.hasInfChar_conj_eq E a P B hB τ m m' hm hm'

end PositivityTheory.Rg.BcB.F.Rig.B

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.StFull
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.One

namespace PositivityTheory.Rg.BcB.F.Rig

def UnrAE : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ)),
  IsAutRepU π → ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, IsUnramU π w

def InertSatEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ)
  (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π → ∀ w : HeightOneSpectrum (𝓞 E), ¬ IsSplitAt w → IsUnramU π w →
  ∃ (s : w.adicCompletion E →+* w.adicCompletion E) (ϖ : w.adicCompletion E) (q : ℕ) (α : Fin (n / 2) → ℂˣ),
    (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) ∧ IsUnramInv ϖ s q ∧ HasSatAt π w s ϖ q α

def SplitConj : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ)),
  IsAutRepU π → ∀ (D : Pre E n) (w u : HeightOneSpectrum (𝓞 E)), IsSplitAt w → ConjPl w u → IsUnramU π w →
    D.SplitAt π w → D.SplitAt π u → ∀ B B', D.Sat w B → D.Sat u B' → B' = B.map (·⁻¹)

def RFullSat : Prop := UnrAE → InertSatEx → Rig.SplitSatPre → FullSat

def RFullTheta : Prop := UnrAE → InertSatEx → SplitConj → FullTheta

end PositivityTheory.Rg.BcB.F.Rig

end
end

