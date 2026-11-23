module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Statements.GeometryStatements.FlagModelStatement
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory NumberField

def FlagModelStatement : Prop :=
  ∀ (o : Type) [CommRing o] [Algebra.EssFiniteType ℤ o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (A : Type) [Finite A] (κa : A → Type) [∀ a, Finite (κa a)] (w : ∀ a, κa a → Ω) (S : Type) [Finite S] (E : Type) [AddCommGroup E] [Module Ω E] (L : S → Lat M.ξ E) (g r : S → ℕ) (W : S → Submodule Ω E) (b₀ : ∀ σ, Fin (r σ) → E), (∀ a, ∃ l, w a l ≠ 0) → (∀ σ, (L σ).IsVB (g σ) (W σ)) → (∀ σ, LinearIndependent Ω (b₀ σ)) → (∀ σ k, b₀ σ k ∈ W σ) → ∃ (κ' : Type) (_ : Finite κ') (y : κ' → Ω) (M' : PModel o y) (f : M'.X ⟶ M.X), Dominates M'.ξ M.ξ f (RingHom.id Ω) ∧ Flat.NormalCpt M'.ξ ∧ (∀ a (p' : Cpt M'.ξ), ∃ l, InChart M'.ξ (w a) l p') ∧ (∀ σ, (((L σ).pull M'.ξ f (AddMonoidHom.id E)).inter (Submodule.span Ω (Set.range (b₀ σ)))).IsFlagVBOn Set.univ (b₀ σ)) ∧ (∀ σ (n : ℕ) (p' : Cpt M'.ξ), ∃ Q : Submodule (regAt M'.ξ p') E, Disjoint Q (((L σ).pull M'.ξ f (AddMonoidHom.id E)).inter (flagStep Ω (b₀ σ) n) p') ∧ Q ⊔ ((L σ).pull M'.ξ f (AddMonoidHom.id E)).inter (flagStep Ω (b₀ σ) n) p' = (L σ).pull M'.ξ f (AddMonoidHom.id E) p') ∧ ∀ p : Cpt M.ξ, (∀ a, ∃ l, InChart M.ξ (w a) l p) → (∀ σ (n : ℕ), ∃ (s : ℕ) (h : Fin s → E ⧸ flagStep Ω (b₀ σ) n), ((L σ).map (flagStep Ω (b₀ σ) n).mkQ).IsFrameAt h p) → NormAt M'.ξ f (RingHom.id Ω) p

end GlobalTheory.CompanionTheory.Ar
end
end

-- bundled from Development.AutomorphicSpectrum.Statements.GeometryStatements.HTChartExists
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BT

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField

def IsHTChartOf {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] {E : Type} [Field E] [NumberField E]
    {c : E ≃+* E} {p n N : ℕ} {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module R Ω] [IsScalarTower R K Ω]
    (D : HT.HTChart R K c p n N Ω) {T : Type} [CommGroup T] (Γ : QFGroup R T) {S : Scheme.{0}} {G : Over S} [GrpObj G]
    {x : Spec (CommRingCat.of R) ⟶ S} (i : Γ.G.left ⟶ G.left) {L : Type} [AddCommGroup L] [Module R L]
    (M : LieModel G x L) (ρ : 𝓞 E →+* Module.End R L) (j : Module.Dual R L →ₗ[R] Ω)
    (π : Multiplicative (Fin N → 𝓞 E) →* T) (ζ : Rˣ) : Prop :=
  D.om = LinearMap.range j ∧
  (∀ a w, D.ρΩ a (j w) = j (w ∘ₗ ρ (RingOfIntegers.mapRingEquiv c a))) ∧
  ∀ y, ∃ (χ : T →* Rˣ) (w : Module.Dual R L), (∀ z, χ (π (Multiplicative.ofAdd z)) = ζ ^ (D.e y z).val) ∧
    D.h y = j w ∧ Γ.IsHT i M (p ^ n) χ w

def HTChartExists : Prop :=
  ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] [CharZero R] [Field K]
    [Algebra R K] [IsFractionRing R K] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (p n N : ℕ) [Fact p.Prime]
    (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G]
    (x : Spec (CommRingCat.of R) ⟶ S) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x (p ^ n) i → Smooth G.hom →
    ∀ (act : 𝓞 E → (G ⟶ G)), (∀ a, IsMonHom (act a)) →
    ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (ρ : 𝓞 E →+* Module.End R L), M.IsActOf act ρ →
    ∀ (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module R Ω] [IsScalarTower R K Ω] (j : Module.Dual R L →ₗ[R] Ω),
      IsBaseChange K j →
    ∀ (π : Multiplicative (Fin N → 𝓞 E) →* T), Function.Surjective π →
      (∀ y, π (Multiplicative.ofAdd y) = 1 ↔ ∃ y', y = (p ^ n) • y') →
      (∀ (a : 𝓞 E) y, (Γ.pt (π (Multiplicative.ofAdd (a • y)))).left ≫ i =
        (Γ.pt (π (Multiplicative.ofAdd y))).left ≫ i ≫ (act a).left) →
    ∀ (ζ : Rˣ), ζ ^ (p ^ n) = 1 →
    ∀ (e : (Fin N → 𝓞 E) →+ (Fin N → 𝓞 E) →+ ZMod (p ^ n)), (∀ y, e y y = 0) →
      (∀ (a : 𝓞 E) (y z : Fin N → 𝓞 E), e (a • y) z = e y (RingOfIntegers.mapRingEquiv c a • z)) →
      (∀ φ : (Fin N → 𝓞 E) →+ ZMod (p ^ n), ∃ y, e y = φ) → (∀ y, e y = 0 → ∃ y', y = (p ^ n) • y') →
    ∃ D : HT.HTChart R K c p n N Ω, D.e = e ∧ IsHTChartOf D Γ i M ρ j π ζ

end GlobalTheory.CompanionTheory.Ar.BT
end
end

-- bundled from Development.AutomorphicSpectrum.Statements.GeometryStatements.PropZ
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

def PropZ : Prop :=
  ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω]
    (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s] (ϖ : O), Irreducible ϖ →
    Function.Injective (algebraMap O Ω) → ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) →
    IsCptGen ξ → NormalCpt ξ → _root_.IsConnected (zeroSet ξ (algebraMap O Ω ϖ)) →
    ∀ (L : Lat ξ Ω) (σ : Ω), L.IsVB 1 ⊤ → TrivMod L (algebraMap O Ω ϖ) →
      (∀ p ∈ genFibre O ξ, L.IsGenAt p σ) →
      ∃ (M : ℕ) (a : ℤ), 0 < M ∧ ∀ p : Cpt ξ, OrderAt L σ (algebraMap O Ω ϖ) M a p

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

