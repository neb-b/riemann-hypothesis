module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnrSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.SymmetricCubeUnits.Sym3AutKOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.EveryPointSatisfiesFrameCondition
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.EqOneOfMemLev

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Sd

namespace UpperTheory.V.Z.Sym.Pl

def LemTWM : Prop :=
  ∀ (F L Ω : Type) [Field F] [NumberField F] [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra F L] [Algebra F Ω]
    [Algebra L Ω] [IsScalarTower F L Ω] [IsAlgClosure F Ω] [IsAlgClosure L Ω], IsTotallyReal F → Module.finrank F L = 2 →
    ∀ (l : ℕ) [Fact l.Prime] (M : ℕ), 3 ≤ M → ∀ Φ : Set (HeightOneSpectrum (𝓞 L)), Af.Tw.IsType F M Φ →
    ∀ ν : G F Ω →* (Qbar l)ˣ, Continuous ν → (∀ c, IsConjEl c → ν c = 1) →
      (∀ (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A v → ((M : ℕ) : 𝓞 F) ∉ v.asIdeal →
        ∀ s ∈ Ine (F := F) A, ν s = 1) →
      ∃ κ : G L Ω →* (Qbar l)ˣ, Continuous κ ∧ VerEq κ ν ∧ ∃ k : ℕ, 0 < k ∧
        ∀ (w : HeightOneSpectrum (𝓞 L)) (A : ValuationSubring Ω), IsPlaceOver A w → ∀ s ∈ Ine (F := L) A,
          (((M : ℕ) : 𝓞 L) ∉ w.asIdeal → κ s = 1) ∧ (w ∉ Φ → κ s ^ k = 1)

def LinkUnr : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O]
    (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* Oˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ)
    (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] (Φ : Fr.Frame l (ResidueField O)),
    Pr.GalLink η Ψ σ g₁ B M L Φ → UnrSplit L M

def ChiUnr : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (N : ℕ) [NeZero N] (e : ℕ)
    (ψ : DirichletCharacter c.O N) (χ' : G ℚ Ω →* (Qbar l)ˣ) (j : ℕ), ¬ l ∣ orderOf χ' →
    (∀ s, ‖((cycBar ℚ Ω l ^ j * χ') s).val - (Chr.Psi l e (Chr.dirG ℚ Ω ψ) s).val.1‖ < 1) →
    ∀ M : ℕ, l * N ∣ M → ∀ (L : Type) [Field L] [NumberField L] [Algebra L Ω] (A : ValuationSubring Ω), ¬ A.valuation (M : Ω) < 1 →
      ∀ s ∈ Ine (F := L) A, χ' (galEmb ℚ L Ω s) = 1

end UpperTheory.V.Z.Sym.Pl

end
