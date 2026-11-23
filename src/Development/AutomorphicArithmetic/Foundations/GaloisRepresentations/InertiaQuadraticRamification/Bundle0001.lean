module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.NumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InertSplitAlt
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published GlobalTheory.RealGal GlobalTheory.UnitaryBC

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

def RealStep (E Ω : Type) {Y : Type} [Field E] [Field Y] [Field Ω] [Algebra E Y] [Algebra Y Ω] (δ : Y) : Prop :=
  (∃ q : ℕ, 0 < q ∧ δ ^ 2 = (q : Y)) ∧ (∀ y : Y, ∃ a b : E, y = algebraMap E Y a + algebraMap E Y b * δ) ∧
    ∃ s : Ω ≃+* Ω, (∀ (j : E →+* Ω) (x : E), s (j x) = j x) ∧ s (algebraMap Y Ω δ) = -algebraMap Y Ω δ

def RamOff {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (T : Set (HeightOneSpectrum (𝓞 F))) (Q : QCM F Ω) :
    Prop :=
  ∃ u ∉ T, ∃ A : ValuationSubring Ω, IsPlaceOver A u ∧ ∃ τ ∈ Ine (F := F) A, ¬ Fixes ↥Q.K τ

def Step0 {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] (T : Set (HeightOneSpectrum (𝓞 E)))
    (Q : QCM E Ω) : Prop :=
  (∃ δ : ↥Q.K, RealStep E Ω δ ∧ ∀ t ∈ T, ∀ A : ValuationSubring Ω, IsPlaceOver A t →
      ∀ g ∈ Dec (F := maximalRealSubfield E) A, g (δ : Ω) = δ) ∧
    (∀ t ∈ T, ∀ A : ValuationSubring Ω, IsPlaceOver A t → ∀ g ∈ Dec (F := E) A, Fixes ↥Q.K g) ∧ RamOff T Q

def Step1 {Y Ω : Type} [Field Y] [NumberField Y] [Field Ω] [Algebra Y Ω] (T : Set (HeightOneSpectrum (𝓞 Y)))
    (Q : QCM Y Ω) : Prop :=
  (∃ x : ↥Q.K, ∃ d : ℕ, 0 < d ∧ x ^ 2 = -(d : ↥Q.K)) ∧ Even (Module.finrank ℚ (maximalRealSubfield ↥Q.K)) ∧
    (∀ t ∈ T, ∀ A : ValuationSubring Ω, IsPlaceOver A t → ∀ g ∈ Dec (F := Y) A, Fixes ↥Q.K g) ∧
    (∀ w : HeightOneSpectrum (𝓞 ↥Q.K), ¬ IsSplitAt w → w.under (𝓞 Y) ∉ T ∧
      Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield ↥Q.K)) w.asIdeal ∧
      ∀ A : ValuationSubring Ω, IsPlaceOver A w → ∀ g ∈ Dec (F := Y) A, Fixes ↥Q.K g) ∧ RamOff T Q

def Quad0 : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (T : Set (HeightOneSpectrum (𝓞 E))), T.Finite → {Q : QCM E Ω | Step0 T Q}.Infinite

def SplitIff : Prop :=
  ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 L)), IsPlaceOver A w → (IsSplitAt w ↔ ∀ g ∈ Dec (F := maximalRealSubfield L) A, Fixes L g)

def Quad0Ex : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (T : Set (HeightOneSpectrum (𝓞 E))), T.Finite → ∃ Q : QCM E Ω, Step0 T Q

def InfOf : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (P : QCM F Ω → Prop),
    (∀ S : Set (HeightOneSpectrum (𝓞 F)), S.Finite → ∃ Q, P Q ∧ RamOff S Q) → {Q | P Q}.Infinite

def SqrtFix : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (A : ValuationSubring Ω) (x : Ω) (a : ℤ), x ^ 2 = (a : Ω) →
    (∀ t : ℕ, t.Prime → A.valuation (t : Ω) < 1 → ((8 * t : ℕ) : ℤ) ∣ a - 1 → ∀ g ∈ Dec (F := F) A, g x = x) ∧
    (A.valuation ((2 * a : ℤ) : Ω) = 1 → ∀ τ ∈ Ine (F := F) A, τ x = x)

def DecGen : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω)
    (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ∀ φ : G F Ω, IsFrob A (normV v) φ → ∀ X : Set Ω, X.Finite →
    (∀ τ ∈ Ine (F := F) A, ∀ x ∈ X, τ x = x) → ∀ g ∈ Dec (F := F) A, ∃ k : ℤ, ∀ x ∈ X, g x = (φ ^ k) x

def UnrLarge : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], ∃ B : ℕ, ∀ p : ℕ, p.Prime → B < p →
    ∀ w : HeightOneSpectrum (𝓞 K), ((p : ℕ) : 𝓞 K) ∉ w.asIdeal ^ 2

def MkQ : Prop :=
  ∀ (Y Ω : Type) [Field Y] [NumberField Y] [IsCMField Y] [Field Ω] [Algebra Y Ω] [IsAlgClosure Y Ω] (x : Ω) (a : ℤ),
    x ^ 2 = (a : Ω) → (∃ g : G Y Ω, g x ≠ x) →
    ∃ (Q : QCM Y Ω) (hx : x ∈ Q.K), (∀ y : ↥Q.K, ∃ b c : Y, y = algebraMap Y ↥Q.K b + algebraMap Y ↥Q.K c * ⟨x, hx⟩) ∧
      ∀ (F : Type) [Field F] [Algebra F Ω] (g : G F Ω), Fixes Y g → g x = x → Fixes ↥Q.K g

def PrimeWith : Prop :=
  ∀ (Y Ω : Type) [Field Y] [NumberField Y] [Field Ω] [Algebra Y Ω] [IsAlgClosure Y Ω] (δ : Ω) (q : ℕ), 0 < q →
    δ ^ 2 = (q : Ω) → ∀ g : Ω ≃+* Ω, g δ = -δ → (∀ (j : Y →+* Ω) (y : Y), g (g (j y)) = j y) →
    ∀ (M : ℕ) (ζ : Ω), 0 < M → IsPrimitiveRoot ζ M → ∀ B : ℕ,
    ∃ p : ℕ, p.Prime ∧ B < p ∧ g ζ = ζ ^ p ∧ ∀ A : ValuationSubring Ω, A.valuation (p : Ω) < 1 →
      ∀ h : Ω ≃+* Ω, (∀ z, h z ∈ A ↔ z ∈ A) → h δ = δ → ∀ y : Y, h (algebraMap Y Ω y) = algebraMap Y Ω y

def TwoPrimes : Prop :=
  ∀ (E Y Ω : Type) [Field E] [NumberField E] [Field Y] [NumberField Y] [Field Ω] [Algebra E Y] [Algebra Y Ω]
    [IsAlgClosure Y Ω] (δ : Y), RealStep E Ω δ → ∀ M B : ℕ, 0 < M →
    ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧ B < p₁ ∧ p₁ < p₂ ∧ M ∣ p₁ * p₂ + 1 ∧
      ∀ A : ValuationSubring Ω, A.valuation ((p₁ * p₂ : ℕ) : Ω) < 1 → ∀ h : Ω ≃+* Ω, (∀ z, h z ∈ A ↔ z ∈ A) →
        h (algebraMap Y Ω δ) = algebraMap Y Ω δ → ∀ y : Y, h (algebraMap Y Ω y) = algebraMap Y Ω y

def InertSplit : Prop :=
  ∀ (Y Ω : Type) [Field Y] [NumberField Y] [IsCMField Y] [Field Ω] [Algebra Y Ω] [IsAlgClosure Y Ω] (A : ValuationSubring Ω)
    (u : HeightOneSpectrum (𝓞 Y)), IsPlaceOver A u → ∀ (x : Ω) (a : ℤ), x ^ 2 = (a : Ω) →
    (∀ τ ∈ Ine (F := maximalRealSubfield Y) A, Fixes Y τ ∧ τ x = x) →
    (∃ g ∈ Dec (F := maximalRealSubfield Y) A, ¬ Fixes Y g) → ∀ h ∈ Dec (F := Y) A, h x = x

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InertiaGenAlt
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

def GroupStep : Prop :=
  ∀ (Γ : Type) [Group Γ] (Gd P : Subgroup Γ → Prop) (D : Set Γ) (Pl : Type) (Dc I : Pl → Set Γ), (∀ u, I u ⊆ Dc u) →
    (∀ H H', Gd H → Gd H' → Gd (H ⊓ H')) → (∀ H H', H ≤ H' → Gd H → Gd H') →
    (∀ U, Gd U → ∀ n : ℕ, 0 < n → ∃ ψ : Γ →* ℂˣ, Gd ψ.ker ∧ ψ ^ n = 1 ∧ (∀ g ∈ D, ψ g = 1) ∧
      ∃ u, Dc u ⊆ U ∧ ∃ τ ∈ I u, orderOf (ψ τ) = n) →
    (∀ H H' u, Gd H → Gd H' → P H → H' ≤ H → (H'.relIndex H).Prime → Dc u ⊆ H → (∃ τ ∈ I u, τ ∉ H') → P H') →
    ∀ (H₀ : Subgroup Γ) (r : Γ →* ℂˣ), Gd H₀ → P H₀ → Gd r.ker → ∀ n : ℕ, 0 < n → r ^ n = 1 →
      ∃ r' : Γ →* ℂˣ, Gd r'.ker ∧ (∀ g ∈ D, r' g = r g) ∧ P (H₀ ⊓ r'.ker)

def PowChar : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ), 0 < n → 2 * n ∣ p - 1 →
    ∃ lam : (ZMod p)ˣ →* ℂˣ, lam ^ n = 1 ∧ lam (-1) = 1 ∧ ∀ a, orderOf a = p - 1 → orderOf (lam a) = n

def InertiaGen : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (u : HeightOneSpectrum (𝓞 F)), IsPlaceOver A u →
    ∀ (p : ℕ) [Fact p.Prime], ((p : ℕ) : 𝓞 F) ∈ u.asIdeal → ((p : ℕ) : 𝓞 F) ∉ u.asIdeal ^ 2 →
    ∀ ζ : Ω, IsPrimitiveRoot ζ p →
    ∃ τ ∈ Ine (F := F) A, ∃ a : (ZMod p)ˣ, orderOf a = p - 1 ∧ τ ζ = ζ ^ (a : ZMod p).val

def DecPow : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (t : HeightOneSpectrum (𝓞 F)), IsPlaceOver A t →
    ∀ p : ℕ, p.Prime → ((p : ℕ) : 𝓞 F) ∉ t.asIdeal → ∀ ζ : Ω, IsPrimitiveRoot ζ p →
    (∀ g ∈ Dec (F := F) A, ∃ k : ℕ, g ζ = ζ ^ (normV t ^ k)) ∧ ∀ τ ∈ Ine (F := F) A, τ ζ = ζ

def SplitPlace : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (U : Subgroup (G F Ω)), IsOpen (U : Set (G F Ω)) →
    ∀ T : Set (HeightOneSpectrum (𝓞 F)), T.Finite →
    ∃ u ∉ T, (normV u).Prime ∧ ((normV u : ℕ) : 𝓞 F) ∈ u.asIdeal ∧ ((normV u : ℕ) : 𝓞 F) ∉ u.asIdeal ^ 2 ∧
      ∀ A : ValuationSubring Ω, IsPlaceOver A u → Dec (F := F) A ≤ U

def RootMod : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (u : HeightOneSpectrum (𝓞 F)), IsPlaceOver A u →
    ∀ p : ℕ, p.Prime → normV u = p → ∀ (y : Ω) (n : ℕ), 0 < n → (∀ g ∈ Dec (F := F) A, g y = y) →
    (∀ m : ℕ, y ^ n = (m : Ω) → ∃ b : ZMod p, b ^ n = (m : ZMod p)) ∧ (IsPrimitiveRoot y n → ¬ p ∣ n → n ∣ p - 1)

def FreshPrime : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (U : Subgroup (G F Ω)), IsOpen (U : Set (G F Ω)) →
    ∀ T : Set (HeightOneSpectrum (𝓞 F)), T.Finite → ∀ n : ℕ, 0 < n →
    ∃ u ∉ T, (normV u).Prime ∧ ((normV u : ℕ) : 𝓞 F) ∈ u.asIdeal ∧ ((normV u : ℕ) : 𝓞 F) ∉ u.asIdeal ^ 2 ∧
      (∀ A : ValuationSubring Ω, IsPlaceOver A u → Dec (F := F) A ≤ U) ∧ 2 * n ∣ normV u - 1 ∧
      ∀ t ∈ T, ((normV u : ℕ) : 𝓞 F) ∉ t.asIdeal ∧ ∃ b : ZMod (normV u), b ^ n = (normV t : ZMod (normV u))

def ExFld : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (H : Subgroup (G (maximalRealSubfield E) Ω)), Good H → ∃ X : Fld E Ω, Cuts X H

def InclOf : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (X Y : Fld E Ω), fixGrp E Ω Y.K ≤ fixGrp E Ω X.K →
    ∃ (_ : Algebra X.K Y.K) (_ : IsScalarTower E X.K Y.K) (_ : IsScalarTower X.K Y.K Ω), IsGalois X.K Y.K ∧
      Module.finrank X.K Y.K = (fixGrp E Ω Y.K).relIndex (fixGrp E Ω X.K)

def IndexComap : Prop :=
  ∀ (Γ Γ' : Type) [Group Γ] [Group Γ'] (f : Γ' →* Γ) (H H' : Subgroup Γ), commutator Γ ≤ H' → H' ≤ H → (H'.relIndex H).Prime →
    (∃ τ, f τ ∈ H ∧ f τ ∉ H') → (H'.comap f).relIndex (H.comap f) = H'.relIndex H

def LayerOf : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (S : Set (HeightOneSpectrum (𝓞 E))) (H H' : Subgroup (G (maximalRealSubfield E) Ω)), Good H' → H' ≤ H →
    (H'.relIndex H).Prime → ∀ X Y : Fld E Ω, Cuts X H → Cuts Y H' →
    ∀ u : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), (∀ s ∈ S, s.under (𝓞 (maximalRealSubfield E)) ≠ u) →
    (∀ A : ValuationSubring Ω, IsPlaceOver A u → ∀ g ∈ Dec (F := maximalRealSubfield E) A, Fixes E g ∧ g ∈ H) →
    (∃ A : ValuationSubring Ω, IsPlaceOver A u ∧ ∃ τ ∈ Ine (F := maximalRealSubfield E) A, τ ∉ H') →
    Layer S X Y ∧ ∀ (_ : Algebra X.K Y.K) (_ : IsScalarTower X.K Y.K Ω), Module.finrank X.K Y.K = H'.relIndex H

def DegOf : Prop :=
  ∀ (K M Ω : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Field Ω] [Algebra K M] [Algebra K Ω] [Algebra M Ω]
    [IsScalarTower K M Ω] [IsAlgClosure K Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 M)), IsPlaceOver A v → IsPlaceOver A w → (∀ τ ∈ Ine (F := K) A, Fixes M τ) →
    ∀ (φ : G K Ω) (d : ℕ), 0 < d → IsFrob A (normV v) φ → (∀ k : ℕ, Fixes M (φ ^ k) ↔ d ∣ k) → normV w = normV v ^ d

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
end
end

