module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpPair
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp

open AlgebraicGeometry CategoryTheory NumberField Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

def CmpPair : Prop :=
  ∀ (II : IntersectionSystem), IsFullIntersectionSystem II →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (g : HostAut H) (Φ : Xo.X ≅ Xo.X)
    (_ : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ.hom) (π : CMType H ≃ CMType H) (S : Finset ℕ) (n : ℕ)
    (M M' : Top.RootModel (CMType H) (D.p + D.q)) (T : HodgeTie Y S n M) (T' : HodgeTie Y S n M'),
    Mono (spMap β) → Φ.hom ≫ Xo.s = Xo.s → (∀ τ, (π τ).1 = τ.1.comp g.σ.toRingHom) →
    IsImageCpt Φ T.A T'.A → (∀ p ∈ S, T'.A.R p = T.A.R p) →
    ∀ w : Fin (Top.dimFl (CMType H) (D.p + D.q) + 1) → CMType H × Fin (D.p + D.q),
      Tendsto (fun t => II _ _ M.P _ (fun j => M.x t (w j)) / M.δ -
        II _ _ M'.P _ (fun j => M'.x t (π (w j).1, (w j).2)) / M'.δ) (𝓝[>] 0) (𝓝 0)

end GlobalTheory.CompanionTheory.Ar.Cmp
end
end

-- bundled from Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeLatticeFlagBound
section
namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar.Num
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal)

def HodgeLatticeFlagBound : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω]
    (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω)
    (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) →
    ∀ [Fintype (CMType H)] [DecidableEq (CMType H)] (Fl : 𝔐.Flag) (S₀ : Finset ℕ)
      (T : LocPair J ℤ (CMType H × Fin (D.p + D.q))), Fl.TwoLevels S₀ T →
    ∀ p ∈ S, p ∉ S₀ → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E →
    ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ →
      ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω],
      AtPlacesOver A Ω p fun O _ _ _ _ => FlagChernComparison (pointIdeal O y) d p D.p φ (T.map (Int.castRingHom O))

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Statements.GeometryStatements.TrivFlagOnHodge
section
namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar.Num
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal)

def TrivFlagOnHodge : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω]
    (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω)
    (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) →
    ∀ (Fl : 𝔐.Flag) (x : CMType H × Fin (D.p + D.q) → K → ℤ) (e : CMType H × Fin (D.p + D.q) → Ω),
      Fl.RootLines x e → ∀ p ∈ S, HT.HTFree 𝔐 p →
      ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω],
      AtPlacesOver A Ω p fun O _ _ _ _ => ∀ τ W, IsFibreComp (pointIdeal O y) W →
        TrivFlagAt W fun i : Fin (D.p + D.q) => x (τ, i)

end GlobalTheory.CompanionTheory.Ar
end

