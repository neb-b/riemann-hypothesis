module

public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0008
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0001
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.UniformGaussModelConditionEquivalent
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.Bundle0002

@[expose] public section

-- bundled from Formalism.LocalToGlobal.InertKernelTheory.DefsMMInv
section
noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

def UnitSubstLoc : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → jacobiSym (-(D.host.d : ℤ)) p = -1 →
    ∀ (lam : Qbar →+* ℂ_[p]) (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p]),
      IsModel lam (lamOf D cc δ) C → IsWq (C • wModel lam (lamOf D cc δ)) wq →
    ∀ (r : ℕ) (M : Fin r → Fin r → ℂ_[p] × ℂ_[p]), (∀ i j, M i j ∈ Formalism.MainNotions.GL3Theta.OKp D lam) →
      (∀ j j', ∑ i, M i j * (M i j').swap = if j = j' then 1 else 0) →
      ∃ S : Fin r → MvPowerSeries (Fin r) ℂ_[p],
        (∀ i, MvPowerSeries.constantCoeff (S i) = 0) ∧ (∀ i, IntegralMv (S i)) ∧
        (∀ i, PowerSeries.subst (S i) (flog (C • wModel lam (lamOf D cc δ)) wq) =
          ∑ j, algebraMap ℂ_[p] (MvPowerSeries (Fin r) ℂ_[p]) (M i j).1 *
            PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries (Fin r) ℂ_[p])
              (flog (C • wModel lam (lamOf D cc δ)) wq)) ∧
        ∃ V : MvPowerSeries (Fin r) ℂ_[p], IntegralMv V ∧
          ePh lam (lamOf D cc δ) C wq r = MvPowerSeries.subst S (ePh lam (lamOf D cc δ) C wq r) * V

end Formalism.L2.KerInert
end
end

-- bundled from Formalism.LocalToGlobal.InertKernelTheory.DefsMMOnb
section
noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

def OneCopyOrth : Prop :=
  ∀ (D : D7) (p : ℕ) [Fact p.Prime], 5 ≤ p → jacobiSym (-(D.host.d : ℤ)) p = -1 →
    ∃ (m : ℕ) (e : Fin m → Matrix (Fin 1) (Fin 1) D.host.E) (u : Fin m → ℚ),
      LocBasis D p (YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D 1) (Formalism.MainNotions.StandardLatticesGL3.stdL D 1)) e ∧
      (∀ i j, i ≠ j → hYY D (e i) (e j) = 0) ∧
      ∀ i, 0 < u i ∧ ¬ (p : ℤ) ∣ (u i).num ∧ ¬ p ∣ (u i).den ∧ hYY D (e i) (e i) = ((u i : ℚ) : D.host.K)

def UnitVec : Prop :=
  ∀ (D : D7) (p : ℕ) [Fact p.Prime], 5 ≤ p → jacobiSym (-(D.host.d : ℤ)) p = -1 →
    ∀ (k : ℕ) (e : Fin k → D.host.E),
      (∀ i, ∃ s : ℕ, Nat.Coprime s p ∧
        (s : D.host.E) * e i ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E)) →
      (∀ i j, i ≠ j → Algebra.trace D.host.K D.host.E (e i * D.host.conj (e j)) = 0) →
      (∀ i, ∃ u : ℚ, 0 < u ∧ ¬ (p : ℤ) ∣ u.num ∧ ¬ p ∣ u.den ∧
        Algebra.trace D.host.K D.host.E (e i * D.host.conj (e i)) = ((u : ℚ) : D.host.K)) →
      k < Module.finrank D.host.K D.host.E →
      ∃ z : D.host.E,
        (∃ s : ℕ, Nat.Coprime s p ∧ (s : D.host.E) * z ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E)) ∧
        (∀ i, Algebra.trace D.host.K D.host.E (z * D.host.conj (e i)) = 0) ∧
        ∃ u : ℚ, 0 < u ∧ ¬ (p : ℤ) ∣ u.num ∧ ¬ p ∣ u.den ∧
          Algebra.trace D.host.K D.host.E (z * D.host.conj z) = ((u : ℚ) : D.host.K)

end Formalism.L2.KerInert
end
end

-- bundled from Formalism.LocalToGlobal.InertKernelTheory.OneCopyTh1
section
noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (thetaS)
open Formalism.L2.Th1.Top (IsLTNorm phL)

def ReadTh1 (p : ℕ) [Fact p.Prime] {n : Type} [Fintype n] [DecidableEq n] (B' : Matrix n n ℂ_[p])
    (F : MvPowerSeries n ℂ_[p]) : MvPowerSeries n ℂ_[p] :=
  MvPowerSeries.subst (fun i => ∑ j, MvPowerSeries.C (B' i j) * Formalism.InvariantFactorPaths.G7.at1 j (Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p)) F

def liftT (D : D7) {p : ℕ} [Fact p.Prime] (F : MvPowerSeries D.what₂.Tau ℂ_[p]) :
    MvPowerSeries (D.what₂.Tau × Fin 1 × Fin 1) ℂ_[p] :=
  MvPowerSeries.subst (fun τ : D.what₂.Tau => (MvPowerSeries.X (τ, 0, 0) : MvPowerSeries (D.what₂.Tau × Fin 1 × Fin 1) ℂ_[p])) F

def OneCopyTh1 : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → jacobiSym (-(D.host.d : ℤ)) p = -1 →
    ∀ (lam : Qbar →+* ℂ_[p]) (ι : ℂ ≃+* ℂ_[p]), IotaExt lam ι →
    ∃ (g2 g3 ε s2 : MaximalUnramifiedExtension p) (σ : ℂ_[p] →+* ℂ_[p]) (r : ℕ) (v : Fin r → (D.what₂.Tau × Fin 1 × Fin 1 → ℂ_[p]))
      (e : D.what₂.Tau ≃ Fin r),
      IsLTNorm p B.L ι g2 g3 s2 ε ∧ ‖g2‖ ≤ 1 ∧ ‖g3‖ ≤ 1 ∧ ‖(g2 : ℂ_[p]) ^ 3 - 27 * (g3 : ℂ_[p]) ^ 2‖ = 1 ∧ ‖ε‖ = 1 ∧
      (∀ n, ‖PowerSeries.coeff n (thetaS p g2 g3 ε)‖ ≤ 1) ∧
      IsConjP D lam σ ∧ IsLocONB D p lam (YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D 1) (Formalism.MainNotions.StandardLatticesGL3.stdL D 1)) σ v ∧
      ∀ (t : D.what₂.Tau → ℂ) (N : ℕ), 0 < N → ¬ p ∣ N → (N : ℂ) • t ∈ B.lamM →
        Formalism.DworkPowerSeriesWeights.Integral (Formalism.DworkPowerSeriesWeights.mvExp (Formalism.L2.Th1.E.phSum (phL p g2 g3 s2 ε) : MvPowerSeries D.what₂.Tau ℂ_[p]) *
          ReadTh1 p (fun τ j => v (e j) (τ, 0, 0))
            (MvPowerSeries.map (ι : ℂ →+* ℂ_[p])
              (Formalism.L2.Th1.H.taylorMv (Formalism.L2.Th1.H.opU (Formalism.L2.Th1.H.matH (hOne B.L D.what₂.Tau)) t B.thMM))))

def CoordTie : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → jacobiSym (-(D.host.d : ℤ)) p = -1 →
    ∀ (lam : Qbar →+* ℂ_[p]) (ι : ℂ ≃+* ℂ_[p]), IotaExt lam ι → ∀ s : VC D 1 1,
      TorsPrime D p (La D B.tor (Formalism.MainNotions.StandardLatticesGL3.stdL D 1) (Formalism.MainNotions.StandardLatticesGL3.stdL D 1)) s →
      pSer D lam (U D B.tor s (B.thZero 1 1)) =
        liftT D (MvPowerSeries.map (ι : ℂ →+* ℂ_[p])
          (Formalism.L2.Th1.H.taylorMv (Formalism.L2.Th1.H.opU (Formalism.L2.Th1.H.matH (hOne B.L D.what₂.Tau)) (fun τ => s τ 0 0) B.thMM))) ∧
      ∃ N : ℕ, 0 < N ∧ ¬ p ∣ N ∧ (N : ℂ) • (fun τ => s τ 0 0) ∈ B.lamM

end Formalism.L2.KerInert
end
end

