module

public import Formalism.LocalToGlobal.InertKernelTheory.DefsMMIsom
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0006
public import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.Bundle0001
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.Bundle0002
public import Formalism.LocalToGlobal.InertKernelTheory.StatementInt
public import Formalism.LocalToGlobal.PairingIndexBounds.PendingAdmissibility.LocalFDerivAdmissibility.RepRed

@[expose] public section

-- bundled from Formalism.LocalToGlobal.InertKernelTheory.DefsFrONB
section
noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)

def LocBasisMM : Prop :=
  ∀ (D : D7) (p : ℕ) [Fact p.Prime], 5 ≤ p → jacobiSym (-(D.host.d : ℤ)) p = -1 → ∀ lam : Qbar →+* ℂ_[p],
    ∃ b : Fin (Fintype.card D.what₂.Tau) → Matrix (Fin 1) (Fin 1) D.host.E,
      LocBasis D p (YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D 1) (Formalism.MainNotions.StandardLatticesGL3.stdL D 1)) b ∧
      ‖(Matrix.of fun m n => lamC lam (D.host.φ₀ ((hYY D (b m) (b n) : D.host.K) : D.host.E))).det‖ = 1 ∧
      (Matrix.of fun (τ τ' : D.what₂.Tau) =>
        lamC lam (embT D τ (b (Fintype.equivFin D.what₂.Tau τ') 0 0))).det ≠ 0

def RatCoord : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → jacobiSym (-(D.host.d : ℤ)) p = -1 →
    ∀ g₁ : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ),
      Formalism.L2.Th1.H.IsIsom (Formalism.L2.Th1.H.matH (Formalism.L2.Th1.H.blk4 (hOne B.L D.what₂.Tau)))
        (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) (g₁ : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) →
      ¬ p ∣ Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau))
        (Formalism.L2.Th1.H.imgLat (g₁ : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM)) →
      Formalism.L2.Th1.H.relIdx
        (Formalism.L2.Th1.H.imgLat (g₁ : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))
        (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) ≠ 0 →
    ∀ b : Fin (Fintype.card D.what₂.Tau) → Matrix (Fin 1) (Fin 1) D.host.E,
      LocBasis D p (YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D 1) (Formalism.MainNotions.StandardLatticesGL3.stdL D 1)) b →
    ∃ c : Fin 4 × D.what₂.Tau → Fin 4 → Fin (Fintype.card D.what₂.Tau) → D.host.K,
      (∀ w i' τ, g₁.symm (Pi.single w 1) (i', τ) =
        ∑ m, D.host.φ₀ ((c w i' m : D.host.K) : D.host.E) * embT D τ (b m 0 0)) ∧
      (∀ w i' m, ∃ s : ℕ, Nat.Coprime s p ∧ IsIntegral ℤ ((s : D.host.K) * c w i' m)) ∧
      ∀ w w', ∑ i', ∑ m, ∑ n, ((c w i' m : D.host.K) : D.host.E) * ((hYY D (b m) (b n) : D.host.K) : D.host.E) *
        D.host.conj ((c w' i' n : D.host.K) : D.host.E) = if w = w' then 1 else 0

def FixConj : Prop :=
  ∀ (D : D7) (p : ℕ) [Fact p.Prime], 5 ≤ p → jacobiSym (-(D.host.d : ℤ)) p = -1 →
    ∀ (lam : Qbar →+* ℂ_[p]) (ι : ℂ ≃+* ℂ_[p]), IotaExt lam ι →
    ∀ σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p, Formalism.InvariantFactorPaths.G7.UnrOK (MaximalUnramifiedExtension p) p σ → ∀ y : MaximalUnramifiedExtension p, σ (σ y) = y →
      (y : ℂ_[p]) ∈ closure (Set.range fun x : D.host.K => lamC lam (D.host.φ₀ (x : D.host.E))) ∧
      ∀ σp : ℂ_[p] →+* ℂ_[p], IsConjP D lam σp → σp (y : ℂ_[p]) = ((σ y : MaximalUnramifiedExtension p) : ℂ_[p])

end Formalism.L2.KerInert
end
end

-- bundled from Formalism.LocalToGlobal.InertKernelTheory.DefsRep
section
noncomputable section

namespace Formalism.L2.KerInert.Rep

open Formalism.MainNotions.FormalGroupSystem Formalism.L2.Th1.D Formalism.L2.Th1.Top Formalism.L2.KerInert.K1
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (cob UnrOK IsLawOfLog)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.G.Pend (k0ToC wittFractionAlgebraCp OcC Frm thA thFOf)
open Formalism.MainNotions.FormalGroupSystem (Sys)

def CurveAt (l : ℕ) [Fact l.Prime] (be : MvPowerSeries (Fin 2) (K0 l)) (g2 g3 ε s2 : MaximalUnramifiedExtension l) : Prop :=
  ‖g2‖ ≤ 1 ∧ ‖g3‖ ≤ 1 ∧ ‖ε‖ = 1 ∧ (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) ∧
    (∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, UnrOK (MaximalUnramifiedExtension l) l σ →
      ∀ α : MaximalUnramifiedExtension l, ‖α‖ = 1 → σ (σ α) = α → NormRel l σ (phFF l g2 g3 s2 ε) α) ∧
    MvPowerSeries.constantCoeff be = 0 ∧
    ∃ F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l), IsLawOfLog l F ∧
      Formalism.InvariantFactorPaths.G7.Simeq (MvPowerSeries.map (k0ToC l) (inParam l be))
        (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype (cob F (phFF l g2 g3 s2 ε)))

def OrthInt (l : ℕ) [Fact l.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension l) {ι : Type} [Fintype ι] [DecidableEq ι]
    (Th : MvPowerSeries (ι ⊕ ι) ℂ_[l]) : Prop :=
  ∃ (r : ℕ) (Θ : MvPowerSeries (Fin r) ℂ_[l]) (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (f f' : ι → Fin r → MaximalUnramifiedExtension l),
    UnrOK (MaximalUnramifiedExtension l) l σ ∧ IsHypPair σ f f' ∧ Th = MvPowerSeries.subst (hypLin l f f') Θ ∧
    Integral (mvExp (Formalism.L2.Th1.E.phSum (phL l g2 g3 s2 ε) : MvPowerSeries (Fin r) ℂ_[l]) *
      @inParamK l _ (Fin r) ℂ_[l] _ (wittFractionAlgebraCp l) Θ)

section Glob

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

def thOrth (D : D7) {N N' r : ℕ} {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (c : ℂ_[p])
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (F₀ : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) :
    MvPowerSeries (Fin r) ℂ_[p] :=
  MvPowerSeries.subst (fun k : D.what₂.Tau × Fin N' × Fin N =>
    ∑ i, MvPowerSeries.C (c * lamC lam (embT D k.1 (b i k.2.1 k.2.2))) * MvPowerSeries.X i) F₀

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : Formalism.L2.G.Pend.CEmbC X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
    (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
    (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))
    (F : ∀ j, X.Lt j → X.Lt (j + 1) →
      MvPowerSeries (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p])

end Glob

def DictInt (D : Formalism.BasicNotions.D7) {p : ℕ} [Fact p.Prime] (lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[p]) (Λ : AddSubgroup ℂ) (c : ℂ_[p])
    (g2 g3 s2 ε : MaximalUnramifiedExtension p) : Prop :=
  ∃ (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p]),
    Formalism.MainNotions.TaylorLogMetric.IsModel lam Λ C ∧ Formalism.MainNotions.TaylorLogMetric.IsWq (C • Formalism.MainNotions.TaylorLogMetric.wModel lam Λ) wq ∧
    ∀ (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)
      (G : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]),
      Formalism.MainNotions.TaylorLogMetric.IntegralMv (Formalism.MainNotions.TaylorLogMetric.atLog D lam Λ C wq b G * Formalism.MainNotions.TaylorLogMetric.ePh lam Λ C wq r) →
      Integral (mvExp (Formalism.L2.Th1.E.phSum (phL p g2 g3 s2 ε) : MvPowerSeries (Fin r) ℂ_[p]) *
        @inParamK p _ (Fin r) ℂ_[p] _ (wittFractionAlgebraCp p) (thOrth D lam c b G))

end Formalism.L2.KerInert.Rep
end
end

