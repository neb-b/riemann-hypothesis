module

public import Mathlib
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020

@[expose] public section

open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4

noncomputable section

namespace GlobalTheory.Mean4O

section One

variable {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (Z : Set X) (r : X → ℝ) (Om : LocPot X)

def leviAt (P : LocPot X) (j : Fin A.n) (y w : Fin e → ℂ) : ℝ :=
  levi (P.φ ((A.chart j).symm y) ∘ (A.chart j).symm) y w

def LeviEq (P Q : LocPot X) : Prop := ∀ j, ∀ y ∈ (A.chart j).target, ∀ w, leviAt A P j y w = leviAt A Q j y w

def PshOff (P : LocPot X) : Prop := ∀ j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∉ Z → ∀ w, 0 ≤ leviAt A P j y w

def ToBot (u : X → ℝ) : Prop := ∀ a : ℝ, closure {x | x ∉ Z ∧ -a ≤ u x} ⊆ Zᶜ

def cut (S : Set X) (f : X → ℝ) : X → ℝ := (S ∩ Zᶜ).indicator f

def IsBd : Prop :=
  IsClosed Z ∧ (∀ j, MeasureTheory.volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Z) = 0) ∧
  IsPotential A Om ∧ IsPosPot A Om ∧ A.SmoothOn Zᶜ r ∧ (∀ x, x ∉ Z → Real.exp 1 ≤ r x) ∧ ToBot Z (fun x => -r x) ∧
  MIntegrable A (fun _ => Om) (cut Z Set.univ r) ∧
  ∃ c : ℝ, 0 < c ∧ PshOff A Z (Om + LocPot.ofFun fun x => -c * r x)

def ListForm (K : ℝ) (T : LocPot X) : Prop :=
  ∃ (θ : LocPot X) (u : X → ℝ), T = θ + LocPot.ofFun u ∧ IsPotential A θ ∧ IsPsh A (Om.rsmul K + θ) ∧
    IsPsh A (Om.rsmul K + θ.rsmul (-1)) ∧ A.SmoothOn Zᶜ u ∧ (∀ x, x ∉ Z → -(K * Real.log (r x)) ≤ u x ∧ u x ≤ 0) ∧
    (A.Smooth u ∨ ToBot Z u) ∧ PshOff A Z T

def Comb (K : ℝ) (P : LocPot X) : Prop :=
  IsPotential A P ∧ ∃ (T : Fin 3 → LocPot X) (c : Fin 3 → ℝ), (∀ l, ListForm A Z r Om K (T l) ∧ |c l| ≤ K) ∧
    ∀ j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∉ Z → ∀ w, leviAt A P j y w = ∑ l, c l * leviAt A (T l) j y w

end One

structure Man (e : ℕ) where

  n : ℕ

  X : Fin (n + 1) → Type
  [top : ∀ σ, TopologicalSpace (X σ)]
  [cpt : ∀ σ, CompactSpace (X σ)]
  [t2 : ∀ σ, T2Space (X σ)]
  [ne : ∀ σ, Nonempty (X σ)]

  A : ∀ σ, FinHolAtlas e (X σ)

  Z : ∀ σ, Set (X σ)

  r : ∀ σ, X σ → ℝ

  Om : ∀ σ, LocPot (X σ)
  bd : ∀ σ, IsBd (A σ) (Z σ) (r σ) (Om σ)

  κ : ℝ
  κ_pos : 0 < κ
  κ_eq : κ = ((n : ℝ) + 1)⁻¹ := by first | exact GlobalTheory.Mean4O.Man.κ_eq _ | simp

attribute [instance] Man.top Man.cpt Man.t2 Man.ne

namespace Man

variable {e : ℕ} (M : Man e)

abbrev Fun : Type := ∀ σ, M.X σ → ℝ

abbrev Pot : Type := ∀ σ, LocPot (M.X σ)

def int (P : Fin e → M.Pot) (u : M.Fun) : ℝ := M.κ * ∑ σ, mInt (M.A σ) (fun i => P i σ) (u σ)

def Smooth (u : M.Fun) : Prop := ∀ σ, (M.A σ).Smooth (u σ)

end Man

structure Calc {e : ℕ} (M : Man e) where

  V : Type
  [grp : AddCommGroup V]
  [mod : Module ℝ V]

  num : (Fin (e + 1) → V) →ₘₗ[ℝ] ℝ
  symm : ∀ (v : Fin (e + 1) → V) (π : Equiv.Perm (Fin (e + 1))), num (v ∘ π) = num v

  c1 : V → M.Pot
  firstChern_isPotential : ∀ v σ, IsPotential (M.A σ) (c1 v σ)
  isOneCochain_add : ∀ v w σ, LeviEq (M.A σ) (c1 (v + w) σ) (c1 v σ + c1 w σ)
  firstChern_smul_leviEq : ∀ (a : ℝ) v σ, LeviEq (M.A σ) (c1 (a • v) σ) ((c1 v σ).rsmul a)

  ar : M.Fun →ₗ[ℝ] V
  c1_ar : ∀ u, M.Smooth u → ∀ σ, LeviEq (M.A σ) (c1 (ar u) σ) (LocPot.ofFun (u σ))
  num_ar : ∀ u, M.Smooth u → ∀ v : Fin e → V, num (Fin.cons (ar u) v) = M.int (fun i => c1 (v i)) u

attribute [instance] Calc.grp Calc.mod

def Calc.top {e : ℕ} {M : Man e} (K : Calc M) (v : K.V) : ℝ := K.num fun _ => v

structure An {e : ℕ} (M : Man e) (ι : Type) (N : ℕ) where

  th : (ι → Fin N → ℝ) → M.Pot

  a : M.Pot

  ph : (ι → Fin N → ℝ) → M.Fun

  phR : ℝ → (ι → Fin N → ℝ) →ₗ[ℝ] M.Fun

  phS : (ι → Fin N → ℝ) → ℝ → M.Fun

namespace An

variable {e : ℕ} {M : Man e} {ι : Type} [Fintype ι] {N : ℕ} (F : An M ι N) (j : ℕ)


end An

variable {D : D7} (Y : ShimX D.what₂.Tau)

structure Real0 where

  M : Y.Comp → Man (dimY Y)

  F : ∀ c, An (M c) D.what₂.Tau Y.N

  K : ℝ → ∀ c, Calc (M c)

  L : ∀ B c, Wt Y →ₗ[ℝ] (K B c).V

  a : ∀ B c, (K B c).V
  th_pot : ∀ c u σ, IsPotential ((M c).A σ) ((F c).th u σ)
  a_pot : ∀ c σ, IsPotential ((M c).A σ) ((F c).a σ)
  c1_L : ∀ B c u σ, LeviEq ((M c).A σ) ((K B c).c1 (L B c u) σ) ((F c).th u σ)
  firstChern_leviEq_constant : ∀ B c σ, LeviEq ((M c).A σ) ((K B c).c1 (a B c) σ) ((F c).a σ)

variable {Y} (T : Real0 Y) (A : SlopeTestRemainingChoices Y)




variable (Y) in
structure Ht where

  h0 : Wt Y → Y.Pt → ℝ

  hH : Wt Y → Y.Pt → ℝ

  hA : Y.Pt → ℝ

  int : Set Y.Pt

  falt : Y.Pt → ℝ

variable (H : Ht Y)

variable (Y) in
def midWt : Wt Y := fun _ i => if (i : ℕ) < Y.j then 1 else 0


end GlobalTheory.Mean4O
