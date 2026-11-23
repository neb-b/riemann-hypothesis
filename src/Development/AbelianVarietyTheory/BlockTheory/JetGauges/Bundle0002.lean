module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import Formalism.PeriodIntegrals.UpqRep
public import Formalism.PeriodIntegrals.Bundle0011
public import Formalism.FormalDegreeBessel.StatementG
public import Formalism.FormalDegreeBessel.StatementDS
public import Formalism.PeriodIntegrals.Bundle0016
public import Formalism.HermitianCurvature.StatementB

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.JetGauges.HarmonicChartValues
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.HarmonicSystemChartValues

open AlgebraicGeometry CategoryTheory NumberField
open Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

abbrev SecAt {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (k : ℕ) : Type :=
  LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) (ptO Xo y.x))

def colSum {S : Type} [CommRing S] [Algebra c.F S] {n : ℕ} (v : Fin n → (Lt1 Dw →₀ ℕ) → S)
    (P : MvPolynomial (LtN Dw n) c.F) : S :=
  ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b : Fin n, v b (colOf m b)

def sysVal (nab : NabV Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (k : ℕ) {n : ℕ}
    (F : Fin n → SecAt Xo c y k) (P : MvPolynomial (LtN Dw n) c.F) : S :=
  colSum c (fun b α => nab y (k : ℤ) (F b) α) P

def IsHarmonic {n : ℕ} (P : MvPolynomial (LtN Dw n) c.F) : Prop :=
  ∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) (i' : Fin (Dw.mult (ComplexEmbedding.conjugate τ))),
    ∑ b : Fin n, MvPolynomial.pderiv (⟨τ, i, b⟩ : LtN Dw n)
      (MvPolynomial.pderiv (⟨ComplexEmbedding.conjugate τ, i', b⟩ : LtN Dw n) P) = 0

end GlobalTheory.IndefiniteRowSideFullHecke.HarmonicSystemChartValues
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.JetGauges.SideNormalisedGap
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SideNormalisedGap

open MeasureTheory Matrix
open scoped InnerProductSpace
open PI.UpqRep (IsDSHpk IsLowUnitH IsHCTypeW IsKFinHpk IsCayleyU IsOrthProjOnto InLieHpk lowKSub smoothVecs dsigW)
open Formalism.QuantumDeterminants (Mt UH Hpk Nset UWset inWb Tz IsHCParam GapAtLeast)
open Formalism.FourierDecayAlt.B (gN)

abbrev Mat (k r : ℕ) := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

def dimV (k r : ℕ) : ℝ := 2 * (r : ℝ) + k + 1

def decExp (r : ℕ) (h : ℝ) : ℝ := h / (8 * Real.sqrt (2 * ((r : ℝ) + 1)))

def decConst (r : ℕ) (h : ℝ) : ℝ := Real.exp (h / (16 * ((r : ℝ) + 1)))

def dimN (k r : ℕ) : ℝ := (r : ℝ) * ((r : ℝ) - 1) + 2 * (r : ℝ) * ((k : ℝ) + 1) + (r : ℝ) ^ 2

def thrG (k r : ℕ) : ℝ := 4 * ((k : ℝ) + r) * ((r : ℝ) + 1)

def thrS (k r : ℕ) : ℝ := (dimV k r - 1) * dimN k r

def propExp (r : ℕ) : ℝ := 2 * ((r : ℝ) ^ 2 + r + 1)

def thrSS (k r : ℕ) : ℝ := 2 * propExp r * thrS k r + 1

def DecGap (k r : ℕ) (h : ℝ) : Prop := 120 * dimV k r * ((r : ℝ) + 1) ^ ((3 : ℝ) / 2) ≤ h

def Size (k r : ℕ) (h : ℝ) : Prop :=
  DecGap k r h ∧ 16 * dimV k r ^ 5 * Real.sqrt (2 * ((r : ℝ) + 1)) ≤ h

def Thresholds (k r : ℕ) (a : ℝ) : Prop :=
  thrG k r < a / 2 ∧ thrS k r < a / 2 ∧ thrSS k r + thrG k r + 1 ≤ a ∧ thrS k r < a - 1

def mulP {k r : ℕ} (p : Mt k r × Mt k r) : Mt k r := fun i j => (Matrix.of p.1 * Matrix.of p.2) i j

theorem measurable_mulP {k r : ℕ} : Measurable (mulP (k := k) (r := r)) := by
  unfold mulP
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  simp only [Matrix.mul_apply, Matrix.of_apply]
  refine Finset.measurable_sum _ fun l _ => ?_
  fun_prop

def muS {k r : ℕ} (μW μN : Measure (Mt k r)) : Measure (Mt k r) := (μW.prod μN).map mulP

section Side

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {Vp : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]

def IsSide (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (σ : Mat k r → (H →L[ℂ] H)) (w₀ : H) (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (u : Fin k → ℝ)
    (π : Mat k r → (Vp →L[ℂ] Vp)) (μW μN μG ν : Measure (Mt k r)) : Prop :=
  1 ≤ k ∧
  (IsHCParam lam ∧ IsDSHpk k r ε lam σ ∧ GapAtLeast ε lam h) ∧
  IsLowUnitH k r ε lam σ w₀ ∧
  (inWb k r z ∧ 0 < Tz k r z) ∧
  c ≠ 0 ∧
  (IsHCParam u ∧ IsHCTypeW k r z u π) ∧
  (PI.BesselPeriodGGP.IsHaarOn (UWset k r z) μW ∧ PI.BesselPeriodGGP.IsHaarOn (Nset k r) μN ∧
    PI.BesselPeriodGGP.IsHaarOn (UH (Hpk k r)) μG) ∧
  (SigmaFinite ν ∧ PI.BesselPeriodGGP.IsQuotMeas μG (muS μW μN) ν)

def IsSideNormalised (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (σ : Mat k r → (H →L[ℂ] H)) (w₀ : H) (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (u : Fin k → ℝ)
    (π : Mat k r → (Vp →L[ℂ] Vp)) (μW μN μG ν : Measure (Mt k r)) : Prop :=
  IsSide k r ε lam h σ w₀ z c u π μW μN μG ν ∧ μW Set.univ = 1

def KFinDecay (k r : ℕ) (σ : Mat k r → (H →L[ℂ] H)) (a : ℝ) : Prop :=
  ∀ v v' : H, IsKFinHpk (k := k) (r := r) σ v → IsKFinHpk (k := k) (r := r) σ v' →
    ∃ C : ℝ, ∀ x ∈ UH (Hpk k r), ‖⟪v', σ x v⟫_ℂ‖ ≤ C * gN x ^ (-a)

def wordSeminorm {k r : ℕ} (σ : Mat k r → (H →L[ℂ] H)) (Ws : List (List (Mat k r))) (w : H) : ℝ :=
  (Ws.map fun D => ‖dsigW (k := k) (r := r) σ D w‖).sum

end Side

def DecKFin : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Mat k r → (H →L[ℂ] H)),
    1 ≤ k → IsHCParam lam → IsDSHpk k r ε lam σ → GapAtLeast ε lam h → DecGap k r h →
    KFinDecay k r σ (decExp r h)

def DecSmooth : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Mat k r → (H →L[ℂ] H)) (a : ℝ),
    IsHCParam lam → IsDSHpk k r ε lam σ → KFinDecay k r σ a →
    ∀ v₀ : H, IsKFinHpk (k := k) (r := r) σ v₀ →
      ∃ (C : ℝ) (Ws : List (List (Mat k r))), (∀ D ∈ Ws, ∀ X ∈ D, InLieHpk k r X) ∧
        ∀ w ∈ smoothVecs (k := k) (r := r) σ, ∀ x ∈ UH (Hpk k r),
          ‖⟪v₀, σ x w⟫_ℂ‖ ≤ C * wordSeminorm σ Ws w * gN x ^ (1 - a)

end GlobalTheory.IndefiniteRowSideFullHecke.SideNormalisedGap
end
end

