module

public import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.GlobalEulerFormulaInf
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseChangeDefs

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.LemmaX
section
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN

def GlobalEulerCharCoprime : Prop :=
  ∀ (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1))), S.Finite → ∀ (ℓ : ℕ) [Fact ℓ.Prime],
    (∀ v ∉ S, ((ℓ : ℕ) : 𝓞 K.1) ∉ v.asIdeal) → ∀ (L : FiniteSubfield) [Fact (K ≤ L)]
    (hL : ∀ x : L.1, algebraMap L.1 (AlgebraicClosure ℚ) x ∈ maxUnramifiedOutside K.1 (AlgebraicClosure ℚ) S),
    (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 (AlgebraicClosure ℚ) S)).Normal →
    Nat.Coprime (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 (AlgebraicClosure ℚ) S)).index ℓ →
    (∃ ζ : L.1, IsPrimitiveRoot ζ ℓ) → (ℓ ≠ 2 ∨ IsTotallyComplex L.1) →
    ∀ (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal},
        AlgebraicClosure ℚ →ₐ[K.1] AlgebraicClosure v.1.Completion)
      (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 (AlgebraicClosure ℚ) S)) [IsDiscreteRep M] [Finite M],
      (∀ m : M, ℓ • m = 0) →
      (∀ g ∈ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 (AlgebraicClosure ℚ) S)), M.ρ g = 1) →
      gsEulerRatio S M ιr = 1

end PositivityTheory.Lit1.GEN
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.RatioOneKilled
section
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN

def RatioOne (ℓ : ℕ) (P : FiniteSubfield → Prop) : Prop :=
  ∀ (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1))), S.Finite →
    (∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S) → P K →
    ∀ (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal},
        AlgebraicClosure ℚ →ₐ[K.1] AlgebraicClosure v.1.Completion)
      (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 (AlgebraicClosure ℚ) S))
      [IsDiscreteRep M] [Finite M], (∃ r : ℕ, ∀ m : M, (ℓ ^ r) • m = 0) → gsEulerRatio S M ιr = 1

def RatioOneKilled (ℓ : ℕ) (P : FiniteSubfield → Prop) : Prop :=
  ∀ (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1))), S.Finite →
    (∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S) → P K →
    ∀ (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal},
        AlgebraicClosure ℚ →ₐ[K.1] AlgebraicClosure v.1.Completion)
      (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 (AlgebraicClosure ℚ) S))
      [IsDiscreteRep M] [Finite M], (∀ m : M, ℓ • m = 0) → gsEulerRatio S M ιr = 1

end PositivityTheory.Lit1.GEN
end

