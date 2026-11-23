module

public import Mathlib
public import Formalism.HermitianLattices.Bundle0003
public import Formalism.FlagUnipotentLattices.CardSubmodulesAndLinearEquivBounds

@[expose] public section

noncomputable section

open NumberField Matrix
open scoped ENNReal Classical

namespace GlobalTheory.Mass

def orbSum (G : Type*) [Group G] {α : Type*} [MulAction G α] (X : Set α) (N : α → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' q : {q : MulAction.orbitRel.Quotient G α // Quotient.out q ∈ X},
    ((ENat.card (MulAction.stabilizer G (Quotient.out q.1)) : ℕ∞) : ℝ≥0∞)⁻¹ * N (Quotient.out q.1)

def orbMass (G : Type*) [Group G] {α : Type*} [MulAction G α] (X : Set α) : ℝ≥0∞ :=
  orbSum G X fun _ => 1

def Stable (G : Type*) [Group G] {α : Type*} [MulAction G α] (X : Set α) : Prop :=
  ∀ (g : G), ∀ x ∈ X, g • x ∈ X

section Act

variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

instance latAct (h : V →ₗ⋆[K] V →ₗ[K] K) : MulAction (Formalism.HermitianLatticesTheory.isom h) (Submodule R V) where
  smul g L := Formalism.HermitianLatticesTheory.gmap (g : V ≃ₗ[K] V) L
  one_smul L := by
    ext x
    change x ∈ Formalism.HermitianLatticesTheory.gmap (1 : V ≃ₗ[K] V) L ↔ _
    simp [Formalism.HermitianLatticesTheory.gmap]
  mul_smul a b L := by
    ext x
    change x ∈ Formalism.HermitianLatticesTheory.gmap ((a : V ≃ₗ[K] V) * (b : V ≃ₗ[K] V)) L ↔
      x ∈ Formalism.HermitianLatticesTheory.gmap (a : V ≃ₗ[K] V) (Formalism.HermitianLatticesTheory.gmap (b : V ≃ₗ[K] V) L)
    simp [Formalism.HermitianLatticesTheory.gmap]

def primeTo (d : R) : Submonoid R where
  carrier := {s | ∀ P : Ideal R, P.IsMaximal → d ∈ P → s ∉ P}
  one_mem' := fun P hP _ h1 => hP.ne_top ((Ideal.eq_top_iff_one P).2 h1)
  mul_mem' := fun ha hb P hP hd hab =>
    (hP.isPrime.mem_or_mem hab).elim (ha P hP hd) (hb P hP hd)

def idxN {W : Type*} [AddCommGroup W] [Module R W] (A B : Submodule R W) : ℕ :=
  B.toAddSubgroup.relIndex A.toAddSubgroup

def discN (h : V →ₗ⋆[K] V →ₗ[K] K) (M : Submodule R V) : ℕ := idxN (Formalism.HermitianLatticesTheory.dual h M) M

def IsIntLat (h : V →ₗ⋆[K] V →ₗ[K] K) (M : Submodule R V) : Prop :=
  Submodule.IsFullLattice K M ∧ Formalism.HermitianLatticesTheory.IsIntegralLat h M

def IsMaxLat (h : V →ₗ⋆[K] V →ₗ[K] K) (M : Submodule R V) : Prop :=
  IsIntLat h M ∧ ∀ N : Submodule R V, IsIntLat h N → M ≤ N → N = M

def badP (h : V →ₗ⋆[K] V →ₗ[K] K) (M : Submodule R V) : Set (Ideal R) :=
  {P | P.IsMaximal ∧ ¬ Formalism.HermitianLatticesTheory.IsUnimodularAt h P M}

def hRes (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) : U →ₗ⋆[K] U →ₗ[K] K := h.domRestrict₁₂ U U

def latIn (U : Submodule K V) (M : Submodule R V) : Submodule R U :=
  M.comap (U.subtype.restrictScalars R)

def perp (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) : Submodule K V := ⨅ x ∈ U, LinearMap.ker (h x)

def latsDisc (h : V →ₗ⋆[K] V →ₗ[K] K) (n : ℕ) : Set (Submodule R V) :=
  {M | IsIntLat h M ∧ discN h M = n}

def primSp (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule R V) (j n : ℕ) : Set (Submodule K V) :=
  {U | Module.finrank K U = j ∧ discN (hRes h U) (latIn U L) = n}

end Act

def PD {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V] (h : V →ₗ⋆[K] V →ₗ[K] K) : Prop :=
  ∀ τ : K →+* ℂ, ∀ x : V, x ≠ 0 → 0 < (τ (h x x)).re

def qIn {K : Type*} [Field K] [NumberField K] (P : Ideal (𝓞 K)) : ℕ := Nat.sqrt (Ideal.absNorm P)

def lamMax {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (M : Submodule (𝓞 K) V) : ℝ :=
  ∏ᶠ P ∈ badP h M, ((qIn P : ℝ) ^ Module.finrank K V - (-1) ^ Module.finrank K V) / ((qIn P : ℝ) + 1)

end GlobalTheory.Mass
