module

public import Mathlib
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.TaylorMvLinear
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0004
public import Formalism.LocalToGlobal.KernelLattices.KerStd
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.UniformGaussModelConditionEquivalent

@[expose] public section

-- bundled from Formalism.LocalToGlobal.InertKernelTheory.StatementAlg
section
noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions Classical
open Formalism.L2.Th1.H (taylorMv tens4 kernel4 alphaQ stdH matH)

def CoefIn1 (f : ℂ → ℂ) (M : IntermediateField ℚ ℂ) : Prop :=
  ∀ k : ℕ, PowerSeries.coeff k (Formalism.L2.Th1.F.taylor0 f) ∈ M

def CoefInMv {n : Type} [Fintype n] [DecidableEq n] (F : (n → ℂ) → ℂ) (M : IntermediateField ℚ ℂ) : Prop :=
  ∀ ν : n →₀ ℕ, MvPowerSeries.coeff ν (taylorMv F) ∈ M

def AlgMv {n : Type} [Fintype n] [DecidableEq n] (F : (n → ℂ) → ℂ) : Prop :=
  ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ CoefInMv F M

def ThetaConstantTermCoefficient : Prop :=
  ∀ (L : PeriodPair) (ω₀ : ℂ), ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice →
    ∀ M : IntermediateField ℚ ℂ, L.g₂ ∈ M → L.g₃ ∈ M → Formalism.L2.Th1.F.s2 L ∈ M → L.weierstrassP (ω₀ / 2) ∈ M →
      CoefIn1 (Formalism.L2.Th1.F.th0 L (ω₀ / 2)) M

def Tens4Alg : Prop :=
  ∀ (n : Type) [Fintype n] [DecidableEq n] (θ : (n → ℂ) → ℂ), AnalyticOnNhd ℂ θ Set.univ → θ ≠ 0 →
    AlgMv (tens4 θ) → AlgMv θ

section Data

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

def kerB (B : Ker.Base D cc δ) : (Fin 4 × D.what₂.Tau → ℂ) → ℂ :=
  kernel4 B.L B.ω₀ B.lamM (alphaQ B.cq (stdH B.L (Fin 4 × D.what₂.Tau))) B.gC

def KapAlg (B : Ker.Base D cc δ) : Prop := IsAlgebraic ℚ B.kappa

def IsTors (B : Ker.Base D cc δ) (x : D.what₂.Tau → ℂ) : Prop :=
  ∃ m : ℕ, 0 < m ∧ (m : ℂ) • x ∈ B.lamM

def trM (B : Ker.Base D cc δ) (x : D.what₂.Tau → ℂ) (θ : (D.what₂.Tau → ℂ) → ℂ) : (D.what₂.Tau → ℂ) → ℂ :=
  Formalism.L2.Th1.H.opU (matH (Ker.hOne B.L D.what₂.Tau)) x θ

def diag4 (x : D.what₂.Tau → ℂ) : Fin 4 × D.what₂.Tau → ℂ := fun w => x w.2

def KerTransAlg (B : Ker.Base D cc δ) : Prop :=
  ∀ x, IsTors B x →
    AlgMv (Formalism.L2.Th1.H.opU (stdH B.L (Fin 4 × D.what₂.Tau)) (diag4 x) (kerB B))

end Data

def ThMMTransAlg : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Ker.Base D cc δ), B.StdOK → KapAlg B → KerTransAlg B →
    ∀ x, IsTors B x → AlgMv (trM B x B.thMM)

end Formalism.L2.KerInert
end
end

-- bundled from Formalism.LocalToGlobal.InertKernelTheory.StatementKap
section
noncomputable section
open scoped BigOperators
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.KerInert

open Formalism.MainNotions Formalism.L2.Ker
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (thetaS)
open Formalism.L2.Th1.Top (IsLTNorm IsFrameH thetaH uniformGaussModelCondition)
open Formalism.L2.Th1.H (CmOK matH stdH stdLat pow4 imgLat relIdx StdData Th alphaQ kernel4 tens4)

def KapInert : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0),
    CmOK a₀ b₀ c₀ D.host.d → B.IsCm a₀ b₀ ha hd lam hlam →
    ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → jacobiSym (-(D.host.d : ℤ)) l = -1 → ∀ ι : ℂ ≃+* ℂ_[l], B.KappaAt l ι

def KappaFirstKernelHypothesis : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0),
    CmOK a₀ b₀ c₀ D.host.d → B.IsCm a₀ b₀ ha hd lam hlam →
    ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → jacobiSym (-(D.host.d : ℤ)) l = -1 → ∀ ι : ℂ ≃+* ℂ_[l],
    ∃ (g : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (e : ℂ),
      StdData B.L B.ω₀ (hOne B.L D.what₂.Tau) B.lamM (alphaQ B.cq (matH (hOne B.L D.what₂.Tau)))
        (alphaQ B.cq (stdH B.L (Fin 4 × D.what₂.Tau))) g ∧
      ¬ l ∣ relIdx (stdLat B.L (Fin 4 × D.what₂.Tau))
        (imgLat (g : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM)) ∧
      ‖ι e‖ = 1 ∧
      B.thMM ∈ Th (matH (hOne B.L D.what₂.Tau)) (alphaQ B.cq (matH (hOne B.L D.what₂.Tau))) B.lamM ∧
      tens4 B.thMM = e • kernel4 B.L B.ω₀ B.lamM (alphaQ B.cq (stdH B.L (Fin 4 × D.what₂.Tau))) g

end Formalism.L2.KerInert
end
end

