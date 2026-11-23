module

public import Mathlib
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.IsPolarisationOfRelAmple
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.PolQuasiInverse
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZarhinDualPolarisation.FlatFiniteFibres.FlatOfFibresFinite

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.IsLBZb
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B]

section Bundle

variable (mu : B ⟶ A) (α : Matrix (Fin 4) (Fin 4) ℤ) {Ω : Type} [Field Ω] (s : Sp Ω ⟶ S)

def pA (i : Fin 4) : (Over.pullback s).obj (G4 (A ⊗ B)) ⟶ (Over.pullback s).obj A :=
  (Over.pullback s).map (prj (A ⊗ B) i ≫ fst A B)

def pM (i : Fin 4) : (Over.pullback s).obj (G4 (A ⊗ B)) ⟶ (Over.pullback s).obj A :=
  (Over.pullback s).map (prj (A ⊗ B) i ≫ snd A B ≫ mu)

def phiL : Fin 4 × Fin 4 → (((Over.pullback s).obj (G4 (A ⊗ B))).left ⟶ ((Over.pullback s).obj A).left)
  | (0, i) => (pA s i).left
  | (1, i) => (pA s i)⁻¹.left
  | (2, i) => (pM mu s i).left
  | (3, i) => (pM mu s i)⁻¹.left

def phiP (ij : Fin 4 × Fin 4) : ((Over.pullback s).obj (G4 (A ⊗ B))).left ⟶ (A ⊗ B).left :=
  (toBase (G4 (A ⊗ B)) s (𝟙 _) ≫ lift (prj (A ⊗ B) ij.1 ≫ fst A B) (prj (A ⊗ B) ij.2 ≫ snd A B)).left

def zb (P : LB (A ⊗ B).left) (L : LB ((Over.pullback s).obj A).left) :
    LB ((Over.pullback s).obj (G4 (A ⊗ B))).left :=
  tens (LB.LinComb L (phiL mu s) fun _ => 1) (LB.LinComb P (phiP s) fun ij => α ij.1 ij.2)

theorem isLB_zb {P : LB (A ⊗ B).left} (hP : P.IsLB) {L : LB ((Over.pullback s).obj A).left} (hL : L.IsLB) :
    (zb mu α s P L).IsLB :=
  isLB_tens (LB.isLB_linComb hL _ _) (LB.isLB_linComb hP _ _)

end Bundle

end PositivityTheory.PrwZar
end
end

-- bundled from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.OneCompPrj
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B]


omit [GrpObj A] [GrpObj B] in
theorem one_comp_prj {G : Over S} [GrpObj G] {Y : Over S} (i : Fin 4) : (1 : Y ⟶ G4 G) ≫ prj G i = 1 := by
  fin_cases i <;> simp [prj]

theorem zc_rigid {P : LB (A ⊗ B).left} (hD : IsDual A B P) (l : A ⟶ B) [IsMonHom l] (mu : B ⟶ A) [IsMonHom mu]
    (α : Matrix (Fin 4) (Fin 4) ℤ) :
    pull (lift (1 : G4 (A ⊗ B) ⟶ G4 (A ⊗ B)) (𝟙 _)).left (zc hD.isLB l mu α) = 0 ∧
      pull (lift (𝟙 _) (1 : G4 (A ⊗ B) ⟶ G4 (A ⊗ B))).left (zc hD.isLB l mu α) = 0 := by
  have e1 : ∀ {Y : Over S} (t : Y ⟶ B), evc hD.isLB (1 : Y ⟶ A) t = 0 :=
    fun t => IsAdditive.evc_one hD.isLB hD.additive t
  have e2 : ∀ {Y : Over S} (a : Y ⟶ A), evc hD.isLB a (1 : Y ⟶ B) = 0 :=
    fun a => evc_one_right hD.isLB hD.zero a
  have o1 : ∀ {Y : Over S} (i : Fin 4) (f : A ⊗ B ⟶ A) [IsMonHom f],
      (1 : Y ⟶ G4 (A ⊗ B)) ≫ prj _ i ≫ f = 1 := by
    intro Y i f _; rw [← Category.assoc, one_comp_prj, MonObj.one_comp]
  have o2 : ∀ {Y : Over S} (i : Fin 4) (f : A ⊗ B ⟶ B) [IsMonHom f],
      (1 : Y ⟶ G4 (A ⊗ B)) ≫ prj _ i ≫ f = 1 := by
    intro Y i f _; rw [← Category.assoc, one_comp_prj, MonObj.one_comp]
  constructor <;>
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [zc, zcPair, map_add (f := _), map_sum, map_nsmul, map_zsmul, pull_evc, lift_fst_assoc, lift_snd_assoc,
      Category.id_comp, o1, o2, e1, e2, smul_zero, add_zero, zero_add, Finset.sum_const_zero]

end PositivityTheory.PrwZar
end
end

-- bundled from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.QiDefs
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual

attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)

namespace PositivityTheory.PrwZar

open GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Ar.GR

def QuasiInverseR : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C], v.Integers R →
    ∀ (A B : Over (Spec (CommRingCat.of R))) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left) (l : A ⟶ B),
      ∀ g : ℕ, IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom →
      SmoothOfRelativeDimension g B.hom → IsDual A B P → IsDual B A (swap P) → Zarhin.IsPolarisation A B P l →
        ∃ (m : ℕ) (mu : B ⟶ A), 1 ≤ m ∧ IsMonHom mu ∧ l ≫ mu = 𝟙 A ^ m ∧ mu ≫ l = 𝟙 B ^ m

def PolFibreIsogAny : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C], v.Integers R →
    ∀ (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left) (l : A ⟶ B),
      ∀ g : ℕ, IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom →
      SmoothOfRelativeDimension g B.hom → IsDual A B P → IsDual B A (swap P) → Zarhin.IsPolarisation A B P l →
      ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (s : Sp Ω ⟶ Sp R),
        IsFinite ((Over.pullback s).map l).left ∧ Flat ((Over.pullback s).map l).left ∧
          Surjective ((Over.pullback s).map l).left

def KilledAny : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C], v.Integers R →
    ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (F : Type) [CommRing F] [Algebra R F]
      (h : sp (R₀ := R) F ⟶ G), IsFinFlatSub G F h →
      ∃ n : ℕ, 0 < n ∧ ∀ (S : Type) [CommRing S] [Algebra R S] (φ : F →ₐ[R] S), (spMap φ ≫ h) ^ n = 1

end PositivityTheory.PrwZar
end
end

