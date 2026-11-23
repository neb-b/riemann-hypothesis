module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEquivOfSumEq
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TwoMulEqOfIsTypeFn
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CM

def TensorObjSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (k : IntermediateField ℚ ℂ), FiniteDimensional ℚ k → D.p = 0 ∨ D.q = 0 →
    ∃ (K₁ : IntermediateField ℚ ℂ) (_ : NumberField K₁) (hk : KA l ≤ K₁) (ω : 𝓞 K₁) (C : Ell H (𝓞 K₁) ω) (ε : ℤˣ)
      (h : D.La → D.La → OK H) (T : PAT H (Sp (𝓞 K₁)))
      (o : Obj D l (baseKA l) (spMap (IntermediateField.inclusion hk).toRingHom)),
      k ≤ K₁ ∧ C.IsPrincipalAt ((algebraMap K₁ ℂ).comp (algebraMap (𝓞 K₁) K₁)) ∧
      IsKForm D ε h ∧ Nonempty (IsTen C D h T) ∧ Nonempty (SABMap o.t T.t (spMap (algebraMap (𝓞 K₁) K₁)))

def CMExistsSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n)
    (Pe : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty Pe) (Z : CMLat hP D.p D.q)
    (k : IntermediateField ℚ ℂ), FiniteDimensional ℚ k →
    ∃ (K₁ : IntermediateField ℚ ℂ) (_ : NumberField K₁) (hk : KA l ≤ K₁) (ρ : 𝓞 K₁)
      (X : CMObj H K₁ ρ (algebraMap K₁ ℂ) D.p D.q) (y : Sp K₁ ⟶ Xo.X) (t₀ : SAB H (Sp K₁))
      (m : SABMap t₀ Xo.univ.t y) (m' : SABMap t₀ X.B.t (spMap (algebraMap (𝓞 K₁) K₁)))
      (gA : Bool → ℕ) (tyA : ∀ b, Fin (gA b) → (E →+* ℂ)) (PA : ∀ b, (Z.D₁ b).La →+ (Fin (gA b) → ℂ))
      (e : ∀ b, (Fin (gA b) → ℂ) → (Over.mk (spMap ((algebraMap K₁ ℂ).comp (algebraMap (𝓞 K₁) K₁))) ⟶ (X.A b).t.G))
      (F : ∀ j : Fin D.p ⊕ Fin D.q, (Fin (gA j.isLeft) → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
      k ≤ K₁ ∧ ((ρ : K₁) : ℂ) = H.rt0 ∧ X.hh = Z.hh ∧
      y ≫ Xo.s = spMap (IntermediateField.inclusion hk).toRingHom ∧ spMap (algebraMap K₁ ℂ) ≫ y = FU.u i Pe ∧
      (∀ b, IsTypeFn H (Z.D₁ b).p (Z.D₁ b).q (tyA b) ∧ IsExp (X.A b) _ (Z.D₁ b) (tyA b) (PA b) (e b)) ∧
      (∀ j a, F j (PA _ a) = Pe (Z.f j a)) ∧
      ∀ (j : Fin D.p ⊕ Fin D.q) (z : Fin (gA j.isLeft) → ℂ) (x : Sp ℂ ⟶ t₀.G.left), x ≫ t₀.G.hom = spMap (algebraMap K₁ ℂ) →
        x ≫ m'.φ = (e _ z ≫ X.φ j).left → x ≫ m.φ = (FU.ex i Pe (F j z)).left

namespace ExSt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

end ExSt

end GlobalTheory.CM
end
