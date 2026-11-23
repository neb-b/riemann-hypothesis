module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsUniqueIsConnOfLift
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsAbelianSchemeOfAbelianThickenings
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0466
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsHolFormConst
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0560
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsUniqueEqConstMulEllTheta

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers TensorProduct
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.CrysConn

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published

def DualAbelianScheme : Prop :=
  ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A →
    ∃ (B : Over S) (_ : GrpObj B) (P : LB (A ⊗ B).left), IsAbelianScheme B ∧
      (∀ g : ℕ, SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom) ∧
      IsDual A B P ∧ IsDual B A (swap P)

def CrystallineDeRham : Prop :=
  ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I), IsNilDP κ →
    ∀ (R₀ : Type) [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I →
    ∀ (X X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s₀ : X₀ ⟶ Sp R₀) (i : X₀ ⟶ X),
      Smooth s → IsSeparated s → QuasiCompact s → IsPullback i s₀ s (spMap π) →
    ∀ m : IsMor (dp0 R) s κ (s₀ ≫ spMap π) (RingHom.id R) i,
      Function.Bijective m.pull1 ∧ Function.Bijective m.pull2

def AbelianDualCrystal : Prop := DualAbelianScheme ∧ CrystallineDeRham

namespace AbelianDualCrystal

section Neron

variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
  [IsFractionRing V K] {A B : Over (Sp V)} [GrpObj A] [GrpObj B]

end Neron

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {κ : DividedPowers I} {π : R →+* R₀}
  {A B A' B' : Over (Sp R)} [GrpObj A] [GrpObj B] [GrpObj A'] [GrpObj B'] {A₀ B₀ : Over (Sp R₀)} [GrpObj A₀]
  [GrpObj B₀] {i : A₀.left ⟶ A.left} {j : B₀.left ⟶ B.left} {i' : A₀.left ⟶ A'.left} {j' : B₀.left ⟶ B'.left}
  {g g' : ℕ}

theorem duality (H : AbelianDeRham) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    (hB : IsAbelianScheme B) (hg' : SmoothOfRelativeDimension g' B.hom) {P : LB (A ⊗ B).left}
    (hP : IsPerfect A B P) :
    (∃! φ, IsCorrForm (dp0 R) (𝟙 _) A B P φ) ∧ ∀ φ, IsCorrForm (dp0 R) (𝟙 _) A B P φ →
      φ.IsPerfPair ∧ (∀ x, x ∈ Fil A ↔ ∀ y ∈ Fil B, φ x y = 0) ∧ ∀ y, y ∈ Fil B ↔ ∀ x ∈ Fil A, φ x y = 0 := by
  have C : CupSquare (dp0 R) (𝟙 _) (A ⊗ B) :=
    cupSquare_of_free H.1 (ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor A B hA hB) (smooth_prod hg hg')
  obtain ⟨φ, hφ⟩ := exists_isCorrForm C hP.isLB hP.zero_left hP.zero_right
  exact ⟨⟨φ, hφ, fun φ' hφ' => IsCorrForm.unique C hP.isLB hφ' hφ⟩,
    fun φ hφ => IsCorrForm.perfect H hA hg hB hg' hP hφ⟩

theorem cupSquare_crys (H : AbelianDeRham.Free) (H' : CrystallineDeRham) (hκ : IsNilDP κ)
    (hπ : Function.Surjective π) (hI : RingHom.ker π = I) (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) (h : IsPullback i A₀.hom A.hom (spMap π))
    (m : GrpMor (dp0 R) (𝟙 _) A κ (spMap π) A₀ (RingHom.id R) (spMap π) i) : CupSquare κ (spMap π) A₀ := by
  have C0 : CupSquare (dp0 R) (𝟙 _) A := cupSquare_of_free H hA hg
  have hs : Smooth (A.hom ≫ 𝟙 _) := by
    rw [Category.comp_id]; exact hA.smooth
  have hsep : IsSeparated (A.hom ≫ 𝟙 _) := by
    rw [Category.comp_id]; haveI := hA.proper; infer_instance
  have hqc : QuasiCompact (A.hom ≫ 𝟙 _) := by
    rw [Category.comp_id]; haveI := hA.proper; infer_instance
  have hpb : IsPullback i A₀.hom (A.hom ≫ 𝟙 _) (spMap π) := by simpa using h
  obtain ⟨h1, h2⟩ := H' R I κ hκ R₀ π hπ hI A.left A₀.left (A.hom ≫ 𝟙 _) A₀.hom i hs hsep hqc hpb m.isMor
  exact CupSquare.of_bijective C0 m h1 h2

theorem cupSquare_crys_prod (H : AbelianDeRham.Free) (H' : CrystallineDeRham) (hκ : IsNilDP κ)
    (hπ : Function.Surjective π) (hI : RingHom.ker π = I) (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) (hB : IsAbelianScheme B) (hg' : SmoothOfRelativeDimension g' B.hom)
    (h : IsGrpPullback A₀ A (spMap π) i) (k : IsGrpPullback B₀ B (spMap π) j) :
    CupSquare κ (spMap π) (A₀ ⊗ B₀) := by
  obtain ⟨l, l₁, l₂⟩ := exists_prod_pullback h k
  exact cupSquare_crys H H' hκ hπ hI (ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor A B hA hB)
    (smooth_prod hg hg') (isPullback_prod h.1 k.1 l₁ l₂) (grpMor_prod (liftMor κ h) (liftMor κ k) l₁ l₂)

theorem exists_crystal_pairing (κ : DividedPowers I) (h : IsGrpPullback A₀ A (spMap π) i)
    (k : IsGrpPullback B₀ B (spMap π) j) {l : (A₀ ⊗ B₀).left ⟶ (A ⊗ B).left}
    (l₁ : l ≫ (fst A B).left = (fst A₀ B₀).left ≫ i) (l₂ : l ≫ (snd A B).left = (snd A₀ B₀).left ≫ j)
    {P : LB (A ⊗ B).left} (hP : P.IsLB) {P₀ : LB (A₀ ⊗ B₀).left} (hP₀ : P₀.IsLB) (e : LBIso (P.pull l) P₀)
    {φ : HdR A →ₗ[R] HdR B →ₗ[R] R} (hφ : IsCorrForm (dp0 R) (𝟙 _) A B P φ) :
    ∃ φ₀, IsCorrForm κ (spMap π) A₀ B₀ P₀ φ₀ ∧ ∀ x y, φ₀ x y = φ (crysToDR κ h x) (crysToDR κ k y) := by
  obtain ⟨φ', h₁, h₂⟩ := IsCorrForm.pull hφ hP (liftMor κ h) (liftMor κ k) l₁ l₂ hP₀ e
  refine ⟨φ', h₁, fun x y => h₂ _ _ _ _ (fun c => ?_) (fun c => ?_)⟩
  · exact (crysToDR_apply κ h x c).symm
  · exact (crysToDR_apply κ k y c).symm

variable {M : Type} [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]
  {T : Type} [CommRing T] [Algebra T R] [Module T M] [IsScalarTower T R M]

end AbelianDualCrystal

end GlobalTheory.Published
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsRapoportOfBasis
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechPic

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult.Elliptic

section

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A]

variable {A}

theorem cls_pull_lam {L : LB A.left} (hL : L.IsLB) {T : Over S} (x y : T ⟶ A)
    (h : ((abelian₂ A L).pull (lift x y).left).IsLB) : cls _ h = lam (cls L hL) x y := by
  rw [cls_pull (L := abelian₂ A L) (LB.isLB_linComb hL _ _) _ h]
  erw [cls_cube_two hL (fst A A) (snd A A)]
  rw [pull_lam, lift_fst, lift_snd]

end

variable {k : Type} [Field k] [IsAlgClosed k] (Q : Out.PolAV (Sp k)) (hg : Q.g = 1)

end GlobalTheory.RealMult.Elliptic

namespace GlobalTheory.RealMult

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R : Type} [CommRing R]

end GlobalTheory.RealMult
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published

def PoincareDeRhamDuality : Prop :=
  ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A →
    IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom →
    ∀ P : LB (A ⊗ B).left, GlobalTheory.AbDual.IsDual A B P →
    ∀ φ : HdR A →ₗ[R] HdR B →ₗ[R] R, GlobalTheory.AbDual.IsCorrForm (dp0 R) (𝟙 _) A B P φ →
      LinearMap.IsPerfPair φ ∧ ∀ x ∈ Fil A, ∀ y ∈ Fil B, φ x y = 0

end GlobalTheory.Published
end
end

