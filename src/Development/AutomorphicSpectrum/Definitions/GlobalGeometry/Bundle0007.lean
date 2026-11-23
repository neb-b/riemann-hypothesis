module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0006
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenWeil
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

structure GenWeil (G : Over X) [GrpObj G] (L : LB G.left) (ξ : Spec (CommRingCat.of Ω) ⟶ X) (n : ℕ)
    (e : (Over.mk ξ ⟶ G) → (Over.mk ξ ⟶ G) → Ωˣ) : Prop where
  finite : Finite {x : Over.mk ξ ⟶ G // x ^ n = 1}
  mul_left : ∀ x x' g, x ^ n = 1 → x' ^ n = 1 → g ^ n = 1 → e (x * x') g = e x g * e x' g
  mul_right : ∀ x g g', x ^ n = 1 → g ^ n = 1 → g' ^ n = 1 → e x (g * g') = e x g * e x g'
  perfect : ∀ χ : (Over.mk ξ ⟶ G) → Ωˣ, (∀ g g', g ^ n = 1 → g' ^ n = 1 → χ (g * g') = χ g * χ g') →
    ∃ x, x ^ n = 1 ∧ ∀ g, g ^ n = 1 → χ g = e x g
  nondeg : ∀ g, g ^ n = 1 → (∀ x, x ^ n = 1 → e x g = 1) → g = 1
  weil : ∀ x g, x ^ n = 1 → g ^ n = 1 → ∀ (k : Type) [Field k] [IsAlgClosed k] (i : Ω →+* k)
    (xk gk : Over.mk (spMap i ≫ ξ) ⟶ G) (c : kˣ), xk.left = spMap i ≫ x.left → gk.left = spMap i ≫ g.left →
      (Out.WeilIs G L n xk gk (unitOn c) ↔ (c : k) = i (e x g))

end GlobalTheory.CompanionTheory.Ar
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HtWSpanSingleton
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HtLatCheck

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]
variable {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]
variable (M : LieModel G ξ E) (L : LB G.left) (n : ℕ) {O : Type} [CommRing O] (ρ : O →+* Module.End Ω E)
  (σ : O →+* Ω)

theorem secVal_one {B : Type} [CommRing B] {Z : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ Z) (W : Z.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ W) : secVal x W h 1 = 1 := by
  simp [secVal]

end GlobalTheory.CompanionTheory.Ar.HtLatCheck
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NonemptyLinearEquivOfPiFinPowFinite
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar.BT

structure TorsTower (p : ℕ) {O : Type} [CommRing O] [IsDomain O] {S : Scheme.{0}} (G : Over S) [GrpObj G]
    (y : Spec (CommRingCat.of O) ⟶ S) (La : Type) [AddCommGroup La] where

  Γ : ∀ n, QFGroup O (LevGrp La p n)

  i : ∀ n, (Γ n).G.left ⟶ G.left
  tors : ∀ n, (Γ n).IsTorsionAlong G y (p ^ n) (i n)
  compat : ∀ n (a : La), ((Γ n).pt (lev p n a)).left ≫ i n = ((Γ (n + 1)).pt (lev p (n + 1) (p • a))).left ≫ i (n + 1)

namespace TorsTower

variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] {S : Scheme.{0}} {G : Over S} [GrpObj G]
  {y : Spec (CommRingCat.of O) ⟶ S} {La : Type} [AddCommGroup La] (X : TorsTower p G y La)

def IsDer {L : Type} [AddCommGroup L] [Module O L] (M : LieModel G y L) (n : ℕ)
    (f : LevGrp La p n → O) (w : Module.Dual O L) : Prop :=
  ∃ s : Γ((X.Γ n).G.left, ⊤), (X.Γ n).HasValues s f ∧ ∀ e : L,
    ∃ v : Spec (CommRingCat.of (DualNumber (O ⧸ Ideal.span {((p ^ n : ℕ) : O)}))) ⟶ (X.Γ n).G.left,
      v ≫ (X.Γ n).G.hom = Spec.map (CommRingCat.ofHom ((algebraMap (O ⧸ Ideal.span {((p ^ n : ℕ) : O)})
        (DualNumber (O ⧸ Ideal.span {((p ^ n : ℕ) : O)}))).comp (Ideal.Quotient.mk _))) ∧
      v ≫ X.i n = Spec.map (CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {((p ^ n : ℕ) : O)})))) ≫
        (M.pt e).left ∧
      valAt v ⊤ le_top s = TrivSqZeroExt.inl (Ideal.Quotient.mk _ (f 1)) +
        TrivSqZeroExt.inr (Ideal.Quotient.mk (Ideal.span {((p ^ n : ℕ) : O)}) (w e))

def Induces (u : G ⟶ G) (φ : La →+ La) : Prop :=
  ∀ n (a : La), ((X.Γ n).pt (lev p n (φ a))).left ≫ X.i n = ((X.Γ n).pt (lev p n a)).left ≫ X.i n ≫ u.left

def PairingRegular (B : La →ₗ[ℤ] La →ₗ[ℤ] ℤ) (ζ : ℕ → Oˣ) : Prop :=
  ∀ n, ∃ s : Γ(((X.Γ n).G ⊗ (X.Γ n).G).left, ⊤), ∀ a b : La,
    valAt (lift ((X.Γ n).pt (lev p n a)) ((X.Γ n).pt (lev p n b))).left ⊤ le_top s =
      algebraMap O (FractionRing O) ((ζ n ^ B a b : Oˣ) : O)

end TorsTower

end GlobalTheory.CompanionTheory.Ar.HT
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TwTan
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* c.F} {β' : O' →+* c.F}

def TwTan {g : HostAut H} {Φ : Xo.X ⟶ Xo.X} (n : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ) (Y : Model Xo c β)
    (Y' : Model Xo c β') {T : Scheme.{0}} (u₁ : T ⟶ Y.t.G.left) (u₂ : T ⟶ Y'.t.G.left) : Prop :=
  ∃ (u : T ⟶ Y.oF.t.G.left) (u' : T ⟶ Y'.oF.t.G.left), u ≫ Y.m.φ = u₁ ∧ u' ≫ Y'.m.φ = u₂ ∧
    u' ≫ Y'.m0.toSABMap.φ = u ≫ (twistMap Y.m0.toSABMap g).φ ≫ n.φ ∧
    u' ≫ Y'.oF.t.G.hom ≫ pullback.snd _ _ = u ≫ Y.oF.t.G.hom ≫ pullback.snd _ _

end GlobalTheory.CompanionTheory.Ar
end
end

