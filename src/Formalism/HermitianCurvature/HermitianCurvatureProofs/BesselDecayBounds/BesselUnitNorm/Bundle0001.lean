module

public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselLine
section
open MeasureTheory Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace PI.BesselLine

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions

def muSof {k r : ℕ} (μW μN : Measure (Mt k r)) : Measure (Mt k r) :=
  (μW.prod μN).map (fun p => fun i j => (Matrix.of p.1 * Matrix.of p.2) i j)

def atFormAtPoint {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Mt k r))
    (σ : Mx k r → (H →L[ℂ] H)) : Prop :=
  ∃ l : H → Wp, IsBesselMapSm z (psi k r z c) σ π l ∧
    (∀ w ∈ smoothVecs (k := k) (r := r) σ, ∀ v : H, IsKFinHpk (k := k) (r := r) σ v →
      Integrable (fun p : Mt k r × Mt k r =>
        (⟪v, σ (Matrix.of p.1 * Matrix.of p.2) w⟫_ℂ * star (psi k r z c (Matrix.of p.2))) • π (Matrix.of p.1)⁻¹)
        (μW.prod μN) ∧
      ∫ p : Mt k r × Mt k r,
        (⟪v, σ (Matrix.of p.1 * Matrix.of p.2) w⟫_ℂ * star (psi k r z c (Matrix.of p.2))) • π (Matrix.of p.1)⁻¹
        ∂(μW.prod μN) = (innerSL ℂ (l v)).smulRight (l w)) ∧
    ∀ w ∈ smoothVecs (k := k) (r := r) σ, w ≠ 0 → ∀ v : H, IsKFinHpk (k := k) (r := r) σ v →
      ENNReal.ofReal (‖l v‖ ^ 2) * l2SG νq (fun g => l (σ g w)) =
        ENNReal.ofReal (‖w‖ ^ 2 * ‖l v‖ ^ 2 / fdegH μG σ w)

def NearbyChamberParameters (D : D7) (Ch Cg Cq : ℝ) (L : LocBessel D.R.k D.R.rS) (lam0 μ : Fin (2 * D.R.rS + D.R.k + 1) → ℝ)
    (ka b κ : ℝ) : Prop :=
  (κ = 1 ∨ κ = ka) ∧ LocOk0 D Ch Cg L lam0 ka b κ ∧ IsHCParam μ ∧
    l1 μ lam0 ≤ q0 Cq (2 * D.R.rS + 2) L.ε L.u lam0

end PI.BesselLine

namespace PI

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.BesselLine

def BesselLine (D : D7) (Ch Cg Cq : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (lam0 μ : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (ka b κ : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mx D.R.k D.R.rS → (H →L[ℂ] H)) (μG νq νq' : Measure (Mt D.R.k D.R.rS)),
    NearbyChamberParameters D Ch Cg Cq L lam0 μ ka b κ → IsDSHpk D.R.k D.R.rS L.ε μ σ →
    IsHaarOn (UH (Hpk D.R.k D.R.rS)) μG → IsQuotMeas μG (muSof L.μW L.μN) νq → IsQuotMeas μG (muSof L.μW' L.μN) νq' →
      atFormAtPoint L.z L.c L.π L.μW L.μN μG νq σ ∧ atFormAtPoint L.z' L.c L.π' L.μW' L.μN μG νq' σ

end PI
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.UnitNorm
section
open MeasureTheory Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace PI.UnitNorm

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions

def GapAndSizeRange (D : D7) (Cg Cq : ℝ) (L : LocBessel D.R.k D.R.rS) (p : ℕ) : Prop :=
  AllGaps L.lam (Cg * p * ((2 * D.R.rS + 2 : ℕ) : ℝ)) ∧
    (((D.R.rS + 1) * (p + D.R.rS + 2) : ℕ) : ℝ) ≤ q0 Cq (2 * D.R.rS + 2) L.ε L.u L.lam

def InBig {k r : ℕ} (L : LocBessel k r) (q : (Fin r → ℂ) × ℂ) : Prop :=
  (∀ i, q.1 i ≠ 0) ∧ Tz k r L.z * Tz k r L.z' < Complex.normSq q.2

end PI.UnitNorm

namespace PI

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.UnitNorm

def UnitNorm (D : D7) (Ch Cg Cq : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) (ka b κ : ℝ) (p : ℕ),
    (κ = 1 ∨ κ = ka) → LocOk0 D Ch Cg L L.lam ka b κ → GapAndSizeRange D Cg Cq L p →
    IsSection D.R.k D.R.rS L.z L.z' μsec →
    ∀ ν : Fin (2 * D.R.rS + D.R.k + 1) → ℤ, ∑ s, |(ν s : ℝ)| ≤ ((D.R.rS + 1) * p : ℕ) →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ' : Mx D.R.k D.R.rS → (H →L[ℂ] H)), IsDSHpk D.R.k D.R.rS L.ε (L.lam + fun a => (ν a : ℝ)) σ' →
    ∀ f' : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp), IsKFinCoefH σ' f' →
      (∃ q : (Fin D.R.rS → ℂ) × ℂ, InBig L q ∧ L.J f' (bigCell D.R.k D.R.rS q.1 (μsec q.2)) ≠ 0) →
      ∃ f'' : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp), IsKFinCoefH σ' f'' ∧ jNorm2 L f'' μsec ≠ 0 ∧ jNorm2 L f'' μsec ≠ ⊤

end PI
end
end

