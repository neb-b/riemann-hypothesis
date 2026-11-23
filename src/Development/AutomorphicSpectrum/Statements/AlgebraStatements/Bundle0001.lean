module

public import Mathlib
public import ReciprocityTheory.DualLattices.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Statements.AlgebraStatements.PolarisedAFStatement
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GR

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up
open scoped Matrix

def PolarisedAFStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    HodgeTateSetting p v R O σ cp → ∀ H : HodgeTateDatum p g v R O σ cp,
    let φ := algebraMap R C
    let AF := afLat p H.AA.carrier
    let H' : Set (Ix g → C) := {x | ∀ l ∈ AF, v (∑ i, φ (l i) * x i) ≤ 1}
    let hb : Matrix (Ix g) (Fin g) C := (((H.E.map (algebraMap ℤ_[p] R))ᵀ)⁻¹ * H.Htᵀ).map φ
    AF = Submodule.span R (Set.range fun k => Matrix.fromRows H.Ht H.Bt k) ∧
    (∀ l : Ix g → R, cp • l ∈ AF) ∧
    HasLen v R ((Ix g → R) ⧸ AF) (v (φ cp) ^ g) ∧
    HasLen v R (AFQuot p H.AA.carrier) (v (φ cp) ^ g) ∧
    (∀ x, x ∈ H' ↔ (∀ k, v ((H.Ht.map φ *ᵥ x) k) ≤ 1) ∧ ∀ k, v ((H.Bt.map φ *ᵥ x) k) ≤ 1) ∧
    (∀ x, (x ∈ H' ∧ H.Ht.map φ *ᵥ x = 0) ↔
      ∃ w : Fin g → C, (∀ k, v (w k) ≤ 1) ∧ x = (φ cp)⁻¹ • (hb *ᵥ w)) ∧
    (∀ w : Fin g → C, (∀ k, v (w k) ≤ 1) → ∃ x ∈ H', H.Ht.map φ *ᵥ x = w) ∧
    GenAF p H.AA.carrier ⊥ ∧ IsTight v p H.AA.carrier

end GlobalTheory.CompanionTheory.Ar.GR
end
end

-- bundled from Development.AutomorphicSpectrum.Statements.AlgebraStatements.PolarisedFlagStatement
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GR

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up
open scoped Matrix

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
  {F : Type} [Field F] {N : Type} [AddCommGroup N] [Module F N]

def FlagConcl (v : Valuation C NNReal) (p : ℕ) (M : Submodule R (N → C)) {n : ℕ}
    (b : Module.Basis (Fin n) F N) (σ : MulChar F R) : Prop :=
  ∃ c δ : Fin n → ℕ → R,
    (∀ i s, c i s ≠ 0 ∧
      idealX M (flagSub b i) (b i) (σ ^ p ^ s) = Ideal.span {c i s} ∧
      xIdeal (stepOrderRes M (flagSub b i) (b i)) (σ ^ p ^ s) = Ideal.span {c i s} ∧
      idealD p M (flagSub b i) (b i) (σ ^ p ^ s) = Ideal.span {c i s} ∧
      c i s ^ p = δ i s * c i (s + 1) ∧
      HasLen v R (OmType (stepOrder M (flagSub b i) (b i)) (σ ^ p ^ (s + 1)))
        (v (algebraMap R C (δ i s)))) ∧
    (∀ s, HasLen v R (OmType M (σ ^ p ^ (s + 1))) (∏ i, v (algebraMap R C (δ i s)))) ∧
    ∀ (j s : ℕ), HasLen v R
      (OmType (M.map (LinearMap.funLeft R C (Subtype.val : flagSub b j → N))) (σ ^ p ^ (s + 1)))
      (∏ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < j), v (algebraMap R C (δ i s)))

def FlagStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 →
  ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p]
    (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N]
    (AA : HopfOrder (C := C) R N), FStable (F := F) AA.carrier → IsTight v p AA.carrier →
  ∀ (n : ℕ) (b : Module.Basis (Fin n) F N),
    (∀ i : Fin n, GenAF p AA.carrier (flagSub b i).toAddSubgroup) →
  ∀ σ : MulChar F R, IsFund p σ → FlagConcl v p AA.carrier b σ

end GlobalTheory.CompanionTheory.Ar.GR
end
end

