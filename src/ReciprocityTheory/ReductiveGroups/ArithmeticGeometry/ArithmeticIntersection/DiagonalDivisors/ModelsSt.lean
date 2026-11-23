module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0003

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AI.T

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

universe u

section Defs

variable {o : Type*} {Ω : Type*} [CommRing o] [Field Ω] [Algebra o Ω] {ι κ : Type*}
  {E : Type*} [AddCommGroup E] [Module Ω E] {r : ℕ}

variable {x : ι → Ω}

def dualLat (B : ChartBundle o x r E) (i : ι) : Set (E →ₗ[Ω] Ω) :=
  {ψ | ∀ v ∈ B.lat i, ψ v ∈ chartRing o x i}

def IsTwistedDualSec (B : ChartBundle o x r E) (φ : κ → E →ₗ[Ω] Ω) : Prop :=
  ∀ i, x i ≠ 0 → ∀ k, ∀ v ∈ B.lat i, φ k v ∈ lineLat o x 1 i

def IsTwistedDualGen [Fintype κ] (B : ChartBundle o x r E) (φ : κ → E →ₗ[Ω] Ω) : Prop :=
  ∀ i, x i ≠ 0 → ∀ ψ ∈ dualLat B i, ∃ c : κ → Ω, (∀ k, c k ∈ chartRing o x i) ∧
    ψ = ∑ k, c k • (x i)⁻¹ • φ k

variable {Φ : Type*} [Field Φ] [Algebra Ω Φ]

def detE (e : Module.Basis (Fin 2) Ω E) (u w : E) : Ω :=
  e.repr u 0 * e.repr w 1 - e.repr u 1 * e.repr w 0

def lineVal (e : Module.Basis (Fin 2) Ω E) (ψ : E →ₗ[Ω] Ω) (a : Φ) : Φ :=
  algebraMap Ω Φ (ψ (e 0)) + a * algebraMap Ω Φ (ψ (e 1))

variable [Algebra o Φ] [IsScalarTower o Ω Φ]

def diagSec (a : Fin 2 → Φ) : Φ := a 1 - a 0

end Defs

section Statements

variable {o : Type*} {Ω : Type*} [CommRing o] [Field Ω] [Algebra o Ω] {ι κ : Type*} [Fintype κ]
  {E : Type*} [AddCommGroup E] [Module Ω E] {x : ι → Ω}
  {Φ : Type*} [Field Φ] [Algebra Ω Φ] [Algebra o Φ] [IsScalarTower o Ω Φ]

end Statements

end ReciprocityTheory.ChartRestriction.G.AI.T
