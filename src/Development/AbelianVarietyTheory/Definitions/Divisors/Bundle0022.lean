module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.MirSet
section
noncomputable section

namespace GlobalTheory.JSW

def colGL {R : Type} [CommRing R] {a : ℕ} (r : ℕ) (x : Fin a → R) : GL (Fin a) R :=
  ⟨1 + Matrix.of (fun i j : Fin a => if (j : ℕ) = r ∧ (i : ℕ) < r then x i else 0),
   1 - Matrix.of (fun i j : Fin a => if (j : ℕ) = r ∧ (i : ℕ) < r then x i else 0),
   by
    have h : Matrix.of (fun i j : Fin a => if (j : ℕ) = r ∧ (i : ℕ) < r then x i else 0) *
        Matrix.of (fun i j : Fin a => if (j : ℕ) = r ∧ (i : ℕ) < r then x i else 0) = 0 := by
      refine Matrix.ext fun i j => ?_
      simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hk : (k : ℕ) = r
      · simp [hk]
      · simp [hk]
    rw [mul_sub, add_mul, add_mul, one_mul, mul_one, one_mul, h]; abel,
   by
    have h : Matrix.of (fun i j : Fin a => if (j : ℕ) = r ∧ (i : ℕ) < r then x i else 0) *
        Matrix.of (fun i j : Fin a => if (j : ℕ) = r ∧ (i : ℕ) < r then x i else 0) = 0 := by
      refine Matrix.ext fun i j => ?_
      simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hk : (k : ℕ) = r
      · simp [hk]
      · simp [hk]
    rw [sub_mul, mul_add, mul_add, one_mul, mul_one, one_mul, h]; abel⟩

def mirSet (R : Type) [CommRing R] (m : ℕ) : Set (GL (Fin (m + 1)) R) :=
  {g | ∀ j, (g : Matrix (Fin (m + 1)) (Fin (m + 1)) R) (Fin.last m) j = if j = Fin.last m then 1 else 0}


end GlobalTheory.JSW
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ProjectiveNotIsUnit
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw

namespace GlobalTheory.FormalAlg

structure Charts {R : Type} [CommRing R] (I : Ideal R)
    (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
    (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (n : ℕ) where

  D : ∀ e, Fin (n + 1) → (Y e).left.Opens

  aff : ∀ e i, IsAffineOpen (D e i)

  cover : ∀ e, ⨆ i, D e i = ⊤

  pre : ∀ e i, β e ⁻¹ᵁ D (e + 1) i = D e i

  ρ : ∀ e i, Fin (n + 1) → Γ((Y e).left, D e i)

  ρ_pull : ∀ e i j, ((β e).appLE (D (e + 1) i) (D e i) (pre e i).ge).hom (ρ (e + 1) i j) = ρ e i j

  ρ_self : ∀ i, ρ 0 i i = 1

  basic : ∀ i j, (Y 0).left.basicOpen (ρ 0 i j) = D 0 i ⊓ D 0 j

  cocycle : ∀ i j l, rs (Y 0).left (inf_le_left : D 0 i ⊓ D 0 j ≤ D 0 i) (ρ 0 i l) =
    rs (Y 0).left (inf_le_left : D 0 i ⊓ D 0 j ≤ D 0 i) (ρ 0 i j) *
      rs (Y 0).left (inf_le_right : D 0 i ⊓ D 0 j ≤ D 0 j) (ρ 0 j l)

  surj : ∀ i, Function.Surjective (MvPolynomial.eval₂Hom (cst (Y 0).hom (D 0 i)) (ρ 0 i))

variable {R : Type} [CommRing R] {I : Ideal R}
  {Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}
  {β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left} {n : ℕ}

def towerIdeal (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (e : ℕ) (J : Ideal R)
    (V : (Y e).left.Opens) : Ideal Γ((Y e).left, V) :=
  J.map (cst ((Y e).hom ≫ thick R I e) V)

def Charts.ev (C : Charts I Y β n) (e : ℕ) (i : Fin (n + 1)) :
    MvPolynomial (Fin (n + 1)) R →+* Γ((Y e).left, C.D e i) :=
  MvPolynomial.eval₂Hom (cst ((Y e).hom ≫ thick R I e) (C.D e i)) (C.ρ e i)

section Projective

open GlobalTheory.ProjSpace
open ReciprocityTheory.ChartRestriction.G.Semi (LB)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)


end Projective

end GlobalTheory.FormalAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.SmoothSpanLeMspan
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory

namespace GlobalTheory.JSW.SpanModel

open GlobalTheory.CuspRep GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def leftInv (E : Type) [Field E] [NumberField E] (a : ℕ) : Submodule ℂ (GA E a → ℂ) where
  carrier := {F | ∀ γ g, F (ratGL E a γ * g) = F g}
  add_mem' hF hG γ g := by simp [hF γ g, hG γ g]
  zero_mem' _ _ := rfl
  smul_mem' c F hF γ g := by simp [hF γ g]

end GlobalTheory.JSW.SpanModel
end
end

