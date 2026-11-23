module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.WinUpDown
public import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.CyclicCharacterEigen.PropEG
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.WeakOfAtt

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Published UpperTheory.V.Sd UpperTheory.V

namespace UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

def PotOfFlag : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (n : ℕ)
    (r : G F Ω →* GL (Fin n) (Qbar l)) (m : Fin n → ℤ), (∀ i j, m i ≠ m j + 1) → ∀ v : HeightOneSpectrum (𝓞 F),
    ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → (∀ A : ValuationSubring Ω, IsPlaceOver A v →
      ∃ (κ : Fin n → ↥(Dec (F := F) A) →* (Qbar l)ˣ) (a : ℕ), 0 < a ∧ IsFlagOn r (Dec (F := F) A) κ ∧
        ∀ i (s : ↥(Dec (F := F) A)), (s : G F Ω) ∈ Ine (F := F) A → κ i s ^ a = (cycBar F Ω l s ^ m i) ^ a) → Win.PotUnl r v

end UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
