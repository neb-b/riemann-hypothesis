module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2204
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2489
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2329
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2523

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.HasRepOfPublished
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.DualCon

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem Fam.ev {T Y : Over S} {N : LB (A ⊗ T).left} (h : Fam A N) (y : Y ⟶ T) :
    Fam A (ev N (fst A Y) (snd A Y ≫ y)) := by
  have hN' : (GlobalTheory.AbDual.ev N (fst A Y) (snd A Y ≫ y)).IsLB := pull_isLB h.isLB _
  refine ⟨hN', (isAdditive_iff hN').2 fun Z a a' t => ?_⟩
  simp only [evc_ev h.isLB (fst A Y) (snd A Y ≫ y) hN', lift_fst, lift_snd_assoc]
  exact (isAdditive_iff h.isLB).1 h.add Z a a' (t ≫ y)


end GlobalTheory.DualCon
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ChartGlue GlobalTheory.ArInt GlobalTheory.VolBr

namespace GlobalTheory.HSAmp

section Gram

variable {S : Type} {Y : S → Type} [∀ σ, MeasurableSpace (Y σ)] {ι : Type}

def gram (μ : ∀ σ, Measure (Y σ)) (v : ∀ σ, Y σ → ι → ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun i j => ∑ᶠ σ, ∫ y, v σ y i * (starRingEnd ℂ) (v σ y j) ∂μ σ

def cmb [Fintype ι] (v : ∀ σ, Y σ → ι → ℂ) (c : ι → ℂ) (σ : S) (y : Y σ) : ℝ := ‖∑ i, c i * v σ y i‖ ^ 2

def l2 [Fintype ι] (μ : ∀ σ, Measure (Y σ)) (v : ∀ σ, Y σ → ι → ℂ) (c : ι → ℂ) : ℝ :=
  ∑ᶠ σ, ∫ y, cmb v c σ y ∂μ σ

def bergmanDensity [Fintype ι] [DecidableEq ι] (μ : ∀ σ, Measure (Y σ)) (v : ∀ σ, Y σ → ι → ℂ) (σ : S) (y : Y σ) : ℝ :=
  (∑ i, ∑ j, (gram μ v)⁻¹ j i * (v σ y i * (starRingEnd ℂ) (v σ y j))).re

structure IsFam (μ : ∀ σ, Measure (Y σ)) (v : ∀ σ, Y σ → ι → ℂ) : Prop where

  finite : Finite S

  integrable : ∀ σ i j, Integrable (fun y => v σ y i * (starRingEnd ℂ) (v σ y j)) (μ σ)

end Gram

def ellCount {ι : Type} [Fintype ι] (A : Matrix ι ι ℝ) (R : ℝ) : ℕ :=
  {z : ι → ℤ | ∑ i, ∑ j, A i j * (z i : ℝ) * (z j : ℝ) ≤ R ^ 2}.ncard

variable {k : Type} [CommRing k] {X : Scheme.{0}}

structure VolDens (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) where

  dens : AlgChart p σ D → CxPts p σ → ℝ

  cont : ∀ c, ContinuousOn (dens c) c.e.source

  pos : ∀ c, ∀ y ∈ c.e.source, 0 < dens c y

  trans : ∀ c c', ∀ y ∈ c.e.source, y ∈ c'.e.source → dens c y = ‖transDet c.e c'.e y‖ ^ 2 * dens c' y

def VolDens.meas {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} (ω : VolDens p σ D) : Measure (CxPts p σ) :=
  glueMeas (fun c : AlgChart p σ D => c.e) fun c y => ENNReal.ofReal (ω.dens c y)

def VolDens.IsRatio {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} (ω : VolDens p σ D) {B : LB X} (φ : Weight p σ B)
    (ρ : CxPts p σ → ℝ) : Prop :=
  Continuous ρ ∧ ∀ c : AlgChart p σ D, ∀ y ∈ c.e.source, c.chernDens φ y = ρ y * ω.dens c y

structure SmFn (p : X ⟶ Sp k) where

  u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ

  cInf : ∀ σ y, CInfAt (u σ) y

  conj : ∀ σ σ', (Weight.ofFun (u σ)).IsConj (Weight.ofFun (u σ'))

def SmFn.smul {p : X ⟶ Sp k} (t : ℝ) (u : SmFn p) : SmFn p where
  u σ y := t * u.u σ y
  cInf σ y := (u.cInf σ y).const_mul t
  conj σ σ' i y y' h hy := congrArg (t * ·) (u.conj σ σ' i y y' h hy)

def SmFn.pull {p : X ⟶ Sp k} (u : SmFn p) {Y : Scheme.{0}} {q : Y ⟶ Sp k} (π : Y ⟶ X) (hπ : π ≫ p = q) : SmFn q where
  u σ y := u.u σ (Points.PtsOver.map π hπ _ y)
  cInf σ _ := CInfAt.pull π hπ (u.cInf σ _)
  conj σ σ' _ _ _ h _ := u.conj σ σ' PUnit.unit _ _ ((congrArg (· ≫ π) h).trans (Category.assoc _ _ _)) mem_ptsIn_top

abbrev up {p : X ⟶ Sp k} (L : HermLB p) (u : SmFn p) : HermLB p := L.raise u.u u.cInf u.conj

variable [IsIntegral X] {p : X ⟶ Sp k}

def upperParabolic (P : Pair p) (u : SmFn p) : Pair p := ⟨up P.L u, P.A, P.r, P.r', P.hr, P.hr'⟩

def val (P : Pair p) (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField) : ℂ :=
  ratVal (P.loc a b f (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y)) y *
    (Real.exp (-(a * (P.L.φ σ).φ (pick (P.L.φ σ).isLB y) y + b * (P.A.φ σ).φ (pick (P.A.φ σ).isLB y) y) / 2) : ℝ)

theorem norm_val (P : Pair p) (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField) :
    ‖val P a b σ y f‖ = P.nu a b σ y f := by
  rw [val, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  rfl

def vals (P : Pair p) (a b : ℤ) {ι : Type} (f : ι → X.functionField) (σ : k →+* ℂ) (y : CxPts p σ) (i : ι) : ℂ :=
  val P a b σ y (f i)

def NV (P : Pair p) (a b : ℤ) (f : X.functionField) : Set X :=
  {x | ∀ i j, x ∈ P.L.B.U i → x ∈ P.A.B.U j → UnitAt x (P.loc a b f i j)}

def ballIn (P : Pair p) (Λ : AddSubgroup X.functionField) (a b : ℤ) (R : ℝ) : Set X.functionField :=
  {f | f ∈ Λ ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ), P.nu a b σ y f ≤ R}

theorem ballIn_H (P : Pair p) (a b : ℤ) (R : ℝ) : ballIn P (P.H a b) a b R = P.Bl a b R := rfl

structure GoodFam (P : Pair p) (D : ℕ) (g : ℝ) (Λ : ℕ → AddSubgroup X.functionField) : Prop where

  le : ∀ m : ℕ, Λ m ≤ P.H m 1

  fg : ∀ m, (Λ m).FG

  small : ∃ C : ℝ, 1 ≤ C ∧ ∀ m : ℕ, 1 ≤ m → Λ m ≤ AddSubgroup.closure (ballIn P (Λ m) m 1 (C ^ m))

  rank : Tendsto (fun m : ℕ => (Module.finrank ℤ (Λ m) : ℝ) / (m : ℝ) ^ D) atTop (𝓝 g)

structure Gens (P : Pair p) (D e : ℕ) (x : Fin (D + 1) → X.functionField) : Prop where

  pos : 0 < e

  mem : ∀ l, x l ∈ P.H e 0

  cover : ∀ z : X, ∃ l, z ∈ NV P e 0 (x l)

def IsCan (P : Pair p) {D : ℕ} (e n : ℕ) (x : Fin (D + 1) → X.functionField) (u : SmFn p) : Prop :=
  ∀ σ y, u.u σ y = ((e : ℝ) * n)⁻¹ * Real.log (∑ l, P.nu e 0 σ y (x l) ^ (2 * n))

def ratF {K : Type} [Field K] {D : ℕ} (x : Fin (D + 1) → K) : Subfield K :=
  Subfield.closure (Set.range fun j : Fin D => x j.succ / x 0)

def ratR {K : Type} [Field K] {D : ℕ} (x : Fin (D + 1) → K) (l : Fin (D + 1)) : Subring K :=
  Subring.closure (Set.range fun j => x j / x l)


omit [IsIntegral X] in
def fib (X : Scheme.{0}) (ℓ : ℕ) : Set X := {x | ringChar (X.residueField x) = ℓ}

section Inhabitants

open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open scoped ComplexOrder

omit [IsIntegral X]


end Inhabitants

end GlobalTheory.HSAmp
end
end

