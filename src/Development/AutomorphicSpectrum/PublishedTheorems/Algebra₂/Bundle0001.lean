module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
public import ReciprocityTheory.DualLattices.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.FarguesExact
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT

open TensorProduct GlobalTheory.PDivGroup

def FarguesExact : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal)
    (O : Type) [CommRing O] [Algebra O C] [Algebra ℤ_[p] O], v.Integers O → v (p : C) < 1 →
    IsAdicComplete (Ideal.span {(p : O)}) O → ∀ G : PDivGroup p O,
    ∀ (ζ : ℕ → O) (h0 : ζ 0 = 1) (h : ∀ n, ζ (n + 1) ^ p = ζ n), ζ 1 ≠ 1 →
      ∀ B : O ⊗[ℤ_[p]] G.Tate →ₗ[O] O ⊗[ℤ_[p]] G.dual.Tate →ₗ[O] O,
        (∀ (x : G.Tate) (χ : G.dual.Tate), ∃ a : ℤ_[p], pairing G O x χ = a • muTate O ζ h0 h ∧
          B (1 ⊗ₜ x) (1 ⊗ₜ χ) = algebraMap ℤ_[p] O a) →
        ∀ x, hodgeTateLinear G x = 0 ↔ ∀ y, dlogLinear G y = 0 → B x y = 0

end GlobalTheory.CompanionTheory.Ar.HT
end
end

-- bundled from Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.FarguesHodgeTate
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT

open TensorProduct GlobalTheory.PDivGroup

def FarguesHodgeTate : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal)
    (O : Type) [CommRing O] [Algebra O C] [Algebra ℤ_[p] O], v.Integers O → v (p : C) < 1 →
    IsAdicComplete (Ideal.span {(p : O)}) O → ∀ G : PDivGroup p O,
    (∀ κ : O, (if p = 2 then v (algebraMap O C κ) ≤ v (4 : C) else v (algebraMap O C κ) ^ (p - 1) ≤ v (p : C)) →
      ∀ w : G.dual.omega, κ • w ∈ LinearMap.range (hodgeTateLinear G)) ∧
    ∀ (ζ : ℕ → O) (h0 : ζ 0 = 1) (h : ∀ n, ζ (n + 1) ^ p = ζ n), ζ 1 ≠ 1 →
      ∀ B : O ⊗[ℤ_[p]] G.Tate →ₗ[O] O ⊗[ℤ_[p]] G.dual.Tate →ₗ[O] O,
        (∀ (x : G.Tate) (χ : G.dual.Tate), ∃ a : ℤ_[p], pairing G O x χ = a • muTate O ζ h0 h ∧
          B (1 ⊗ₜ x) (1 ⊗ₜ χ) = algebraMap ℤ_[p] O a) →
        ∀ x, hodgeTateLinear G x = 0 ↔ ∀ y, dlogLinear G y = 0 → B x y = 0

end GlobalTheory.CompanionTheory.Ar.HT
end
end

-- bundled from Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.QuotientByFiniteFlatStatement
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GR

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up
open scoped Matrix
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

def QuotientByFiniteFlatStatement : Prop :=
  ∀ (R : Type) [CommRing R] (A : Over (Spec (CommRingCat.of R))) [GrpObj A] (L : LB A.left),
    IsAbelianScheme A → L.IsLB → Out.RelAmple A L →
    ∀ (B : Type) [CommRing B] [Algebra R B] (h : sp (R₀ := R) B ⟶ A), IsFinFlatSub A B h →
    ∃ (A' : Over (Spec (CommRingCat.of R))) (_ : GrpObj A') (L' : LB A'.left) (q : A ⟶ A'),
      IsAbelianScheme A' ∧ L'.IsLB ∧ Out.RelAmple A' L' ∧ IsMonHom q ∧
      IsFinite q.left ∧ Flat q.left ∧ Surjective q.left ∧
      ∀ (S : Type) [CommRing S] [Algebra R S] (z : sp (R₀ := R) S ⟶ A),
        z ≫ q = 1 ↔ ∃ φ : B →ₐ[R] S, spMap φ ≫ h = z

end GlobalTheory.CompanionTheory.Ar.GR
end
end

-- bundled from Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.ZarhinStatement
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GR

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up
open scoped Matrix
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

def ZarhinStatement : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C], v.Integers R →
    ∀ (A : Over (Spec (CommRingCat.of R))) [GrpObj A] (L : LB A.left),
      IsAbelianScheme A → L.IsLB → Out.RelAmple A L →
      ∃ (P : Out.PolAV (Spec (CommRingCat.of R))) (i : A ⟶ P.A) (r : P.A ⟶ A),
        IsMonHom i ∧ IsMonHom r ∧ i ≫ r = 𝟙 A

end GlobalTheory.CompanionTheory.Ar.GR
end
end

