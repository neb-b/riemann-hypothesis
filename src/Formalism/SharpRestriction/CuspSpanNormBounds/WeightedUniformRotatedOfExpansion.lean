module

public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.FramesPt

@[expose] public section

noncomputable section

open Finset

namespace Formalism.MainNotions.RotatedPoints

open MeasureTheory Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.HermitianLatticeCounting.ExpansionTerms Formalism.MainNotions.BesselShellMomentBounds Formalism.MainNotions.S.Pv.Frames

section R

variable (D : D7)

def JSqR {Ch Cg : ℝ} {T T' : ℕ} {b dist : ℝ} (X : BData D Ch Cg T T' b dist)
    (γ : Point D.host.E (D.R.rS + 1)) : ENNReal :=
  ∏ v, orbSq (X.L v) (X.f v) (turnPt (ptLoc D v γ))

def BSumR {Ch Cg : ℝ} {T T' : ℕ} {b dist : ℝ} (X : BData D Ch Cg T T' b dist)
    (W : Point D.host.E (D.R.rS + 1) → ℝ) : ENNReal :=
  ∑' γ : {γ : Point D.host.E (D.R.rS + 1) // IsBPt D T T' γ},
    ENNReal.ofReal (wPt D γ.1 * ptWeightG D (rhoReal D) T T' γ.1.1 * W γ.1) * JSqR D X γ.1

def theoremBRotated (Aw Ch Cg Cb : ℝ) : Prop :=
  ∀ (T T' : ℕ) (b : ℝ) (X : BData D Ch Cg T T' b 0),
    (∀ v, AllGaps (X.L v).lam (Cg * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 4)) →
    BSumR D X (fun γ => normWt D T T' γ ^ (Aw * ((D.R.rS : ℝ) + 1) ^ 2)) ≤
      ENNReal.ofReal (Real.exp (Cb * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 5 * (Fintype.card D.what₂.Tau : ℝ) * Real.log b)) *
        jSqG D X

def OnePlaceR (Ch Cg dist : ℝ) (P : ∀ (T T' : ℕ) (b : ℝ), BData D Ch Cg T T' b dist → Prop) (A : ℕ) (CK : ℝ) (e : ℕ)
    (p : ℝ) : Prop :=
  ∀ (T T' : ℕ) (b : ℝ) (X : BData D Ch Cg T T' b dist), P T T' b X →
    ∀ γ : Point D.host.E (D.R.rS + 1), IsBPt D T T' γ → ∀ v,
    ENNReal.ofReal (wLoc D v γ ^ 2 * (1 + dLoc D v γ) ^ A * nLoc D T T' v γ * WLoc D T T' v γ ^ p) *
        orbSq (X.L v) (X.f v) (turnPt (ptLoc D v γ)) ≤
      ENNReal.ofReal (b ^ (CK * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ e) *
          max 1 (1 / absV D v (Gglob D T T' γ)) ^ A) * jNorm2 (X.L v) (X.f v) (X.μsec v)

variable {D}

theorem weighted_bound_rotated_of_one_place {Aw Ch Cg CK : ℝ} {A : ℕ} (hCg : 2 ≤ Cg)
    (hO : OnePlaceR D Ch Cg 0 (fun _ _ _ X => ∀ v, AllGaps (X.L v).lam (Cg * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 4)) A CK 5
      (Aw * ((D.R.rS : ℝ) + 1) ^ 2)) : theoremBRotated D Aw Ch Cg (CK + 6) := by
  exact Formalism.MainNotions.BesselShellMomentBounds.theorem_B_weighted_bound_one_place (D := D) hCg hO

variable (D)

def PlaceOKR (Ch Cg : ℝ) (T T' : ℕ) (b dist : ℝ) (v : D.what₂.Tau) (L : LocBessel D.R.k D.R.rS)
    (f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)) (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) : Prop :=
  LocOk D Ch Cg L (lamSH D.R (D.hc v)) (kaRe D) b (kaRe D) ∧ l1 L.lam (lamSH D.R (D.hc v)) ≤ dist ∧
    IsKFinCoefH L.σ f ∧ IsSection D.R.k D.R.rS L.z L.z' μsec ∧
    Tz D.R.k D.R.rS L.z = T ∧ Tz D.R.k D.R.rS L.z' = T'

variable {D}

end R

def WeightedBoundRotatedUniform : Prop :=
  ∀ Aw Ch : ℝ, 0 ≤ Aw → ∃ Cb Cg₀ : ℝ, ∀ Cg : ℝ, Cg₀ ≤ Cg → ∀ D : D7, theoremBRotated D Aw Ch Cg Cb

end Formalism.MainNotions.RotatedPoints
