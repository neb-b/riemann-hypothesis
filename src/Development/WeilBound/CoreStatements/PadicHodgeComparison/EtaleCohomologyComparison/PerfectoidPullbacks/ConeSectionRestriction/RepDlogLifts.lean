module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0153
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0255
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitLogRepresentativeCompat
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0102
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TopRepresentativeAdd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0161
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0007
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0001

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Pb

theorem rep_cupList : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (Φ : PDF R C) (Fil : ℤ → IdF Φ.A),
    IsFil Φ Fil → ∀ {m : ℕ} (ℓ : Fin m → CH.Cn (CH.modF Φ.A) 1), (∀ k, CH.d _ 1 (ℓ k) = 0) → (∀ k σ, ℓ k σ ∈ (Fil 1).S _) →
    ∃ c : CH.H (sq (Fil m) (Fil ((m : ℤ) + 1))) m, Rep (Fil m) (Fil ((m : ℤ) + 1)) (cupListC Φ.A ℓ) c := _root_.GlobalTheory.CompanionTheory.ConeRepCup.exists_rep

theorem dlog_ratios : ∀ {K R : Type} [Field K] [CommRing R] [Algebra K R] (n : ℕ) (t : Fin (n + 1) → Rˣ)
    (D : Fin (n + 1) → Derivation K R R), (∀ k j, D k (t j) = if k = j then 1 else 0) →
    let g : Fin (n + 1) → R := fun k => if h : (k : ℕ) = 0 then ((t 0)⁻¹ : Rˣ) else
      (t ⟨k - 1, by omega⟩ : R) * ((t k)⁻¹ : Rˣ)
    Ring.inverse (∏ k, g k) * (Matrix.of fun k l => D k (g l)).det = (((∏ k, t k)⁻¹ : Rˣ) : R) ∨
    Ring.inverse (∏ k, g k) * (Matrix.of fun k l => D k (g l)).det = -(((∏ k, t k)⁻¹ : Rˣ) : R) := GlobalTheory.T.torus_jacobian_det

end CrystallineSemistableComparison.Pb
