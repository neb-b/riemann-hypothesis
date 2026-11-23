module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AutomorphicSpectrum.Definitions.MembershipCriteria.LaEqSqrtSmulLam

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Definitions.MembershipCriteria.ExistsHarrisTaylorObjectOfLevelLift
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Complex
open scoped Classical

namespace GlobalTheory.CompanionTheory.OM

abbrev W (κ R : Type) : Type := (κ → R) × (κ → R)

variable {κ : Type} [Fintype κ]

def ofQ (κ R : Type) [CommRing R] [Algebra ℚ R] : W κ ℚ →+ W κ R where
  toFun w := (fun i => algebraMap ℚ R (w.1 i), fun i => algebraMap ℚ R (w.2 i))
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp

def re (Γ : AddSubgroup (W κ ℚ)) : AddSubgroup (W κ ℝ) := Γ.map (ofQ κ ℝ)

end GlobalTheory.CompanionTheory.OM

end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.MembershipCriteria.GoodChar
section
noncomputable section

open MeasureTheory Matrix GlobalTheory.WeilM

namespace GlobalTheory.CompanionTheory.VacLoc

section Ground

variable {R : Type} [CommRing R] [TopologicalSpace R]

structure GoodChar (ψ : AddChar R ℂ) (O : Subring R) (u : Rˣ) : Prop where
  norm_one : ∀ x, ‖ψ x‖ = 1
  compact : IsCompact (O : Set R)
  isOpen : IsOpen (O : Set R)
  ann : ∀ x : R, (∀ y ∈ O, ψ (x * y) = 1) ↔ ((u⁻¹ : Rˣ) : R) * x ∈ O
  basis : ∀ U ∈ nhds (0 : R), ∃ v : Rˣ, ∀ y ∈ O, (v : R) * y ∈ U
  den : ∀ x : R, ∃ v : Rˣ, (v : R) ∈ O ∧ (v : R) * x ∈ O

def pair {κ : Type} (μ : @Measure (κ → R) (borel _)) (φ φ' : (κ → R) → ℂ) : ℂ :=
  ∫ x, (starRingEnd ℂ) (φ x) * φ' x ∂μ

variable [Invertible (2 : R)] {W : Type} [AddCommGroup W] [Module R W] {B : W → W → R} {κ : Type} [Fintype κ]

def IsModel (ψ : AddChar R ℂ) (d : Darboux B κ) (μ : @Measure (κ → R) (borel _))
    (S : GlobalTheory.CompanionTheory.FinHeis.Sys W (SB (κ → R))) : Prop :=
  (∀ w (φ : SB (κ → R)), ((S.rho w φ : SB (κ → R)) : (κ → R) → ℂ) = d.rho ψ w φ) ∧
  (∀ φ φ' : SB (κ → R), S.B φ φ' = pair μ φ φ') ∧ ∀ w w', S.c w w' = ψ (⅟(2 : R) * B w w')

end Ground

variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

end GlobalTheory.CompanionTheory.VacLoc
end
end

