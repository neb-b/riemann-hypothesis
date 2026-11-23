module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.TwistedSlicesSquareIntegrable
public import Development.WeilBound.CoreStatements.AutomorphicKernels.ResidualSpectrumHilbertSum.ResidualSpectrumTensors.Development
public import Development.WeilBound.CoreStatements.AutomorphicKernels.ResidualSpectrumHilbertSum.ResidualSpectrumTensors.Bundle0002
public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0716
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidual
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0647
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0853
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0664
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0697
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0317
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0644
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0158
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0002
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0007
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0710

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.Rs

namespace Re.Asc

theorem hasSpehComp (h3 : Clause3Asc) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL)
    {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N a d : ℕ} (hN : 1 ≤ N)
    {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) {π : CuspSub E a} (hn : IsNormalised π) (e : AscEmb V π d) :
    HasSpehComp V π d := by
  refine ⟨fun w => ?_, h3 E N a d V π hN hV (GlobalTheory.SpehPair.isUnitary_of_isNormalised hn) hn e, fun τ => ?_⟩
  · obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp hF E a π w
    obtain ⟨σ', hσ'⟩ := GlobalTheory.DiscLocEx.exists_isLocCompGL hF E N V hV w
    exact ⟨σ, σ', hσ, hσ'⟩
  · obtain ⟨m', hm'⟩ := PInfInd2A.exists_hasInfCharGL hV τ
    obtain ⟨m₀, hm₀, rfl⟩ := infAsc_holds E N a d V π hV e τ m' hm'
    refine ⟨m₀, hm₀, ?_⟩
    have e' : (∑ i : Fin d, m₀.map (· + (spehExp d i : ℂ))) = GlobalTheory.SphGal.spehInf d m₀ := by
      simp only [GlobalTheory.SphGal.spehInf, spehExp]
      push_cast
      rfl
    rw [← e']
    exact hm'

section Pair

end Pair

section Local

open GlobalTheory.DefiniteBC GlobalTheory.BcSpeh GlobalTheory.BcSpehProof

end Local

end Re.Asc

end PositivityTheory.Rg.Rs

end
