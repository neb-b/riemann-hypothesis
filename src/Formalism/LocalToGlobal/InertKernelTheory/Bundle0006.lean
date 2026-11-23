module

public import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionAlgebraCp
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.Bundle0001
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.Bundle0002
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0005
public import Mathlib
public import Formalism.LocalToGlobal.KernelLattices.KerStd
public import Formalism.LocalToGlobal.KernelLattices.ColumnData

@[expose] public section

-- bundled from Formalism.LocalToGlobal.InertKernelTheory.FirstKernelGeneratorOfOrthogonal
section
noncomputable section

namespace Formalism.L2.KerInert.K1

open Formalism.MainNotions.FormalGroupSystem Formalism.L2.Th1.D Formalism.L2.Th1.Top
open Formalism.L2.G.Pend (k0ToC wittFractionAlgebraCp OcC)
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (lgF cob UnrOK IsLawOfLog)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)

def sumBe (p : ℕ) [Fact p.Prime] {ι : Type} [Fintype ι] (be : MvPowerSeries (Fin 2) (K0 p)) :
    MvPowerSeries (ι ⊕ ι) (K0 p) :=
  ∑ e : ι, sub2 p be (MvPowerSeries.X (Sum.inl e)) (MvPowerSeries.X (Sum.inr e))

def FirstKernelGeneratorOfSum : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (ι : Type) [Fintype ι] (K1 : Type) [Field K1] [Algebra (K0 p) K1] (R1 : Subring K1)
    (be : MvPowerSeries (Fin 2) (K0 p)) (Th : MvPowerSeries (ι ⊕ ι) K1),
    BeProp p be →
    Formalism.MainNotions.FormalGroupSystem.Simeq p (MvPowerSeries.subst (fun i => -MvPowerSeries.X i) (sumBe p be) :
      MvPowerSeries (ι ⊕ ι) (K0 p)) (sumBe p be) →
    IntR R1 (inParamK p K1 (Th * MvPowerSeries.map (algebraMap (K0 p) K1) (expS p (sumBe p be)))) →
    ExtensionGeneratorCondition p K1 R1 be Th

def SumBeEven : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (ι : Type) [Fintype ι] (be : MvPowerSeries (Fin 2) (K0 p)),
    BeProp p be →
    Formalism.MainNotions.FormalGroupSystem.Simeq p (MvPowerSeries.subst (fun i => -MvPowerSeries.X i) (sumBe p be) :
      MvPowerSeries (ι ⊕ ι) (K0 p)) (sumBe p be)

def hypLin (l : ℕ) [Fact l.Prime] {ι n : Type} [Fintype ι] (f f' : ι → n → MaximalUnramifiedExtension l) (i : n) :
    MvPowerSeries (ι ⊕ ι) ℂ_[l] :=
  ∑ e : ι, (MvPowerSeries.C (f e i : ℂ_[l]) * MvPowerSeries.X (Sum.inl e) +
    MvPowerSeries.C (f' e i : ℂ_[l]) * MvPowerSeries.X (Sum.inr e))

def HypOfOrth : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l →
  ∀ g2 g3 ε s2 : MaximalUnramifiedExtension l, ‖g2‖ ≤ 1 → ‖g3‖ ≤ 1 → ‖ε‖ = 1 →
    (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) →
  ∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, UnrOK (MaximalUnramifiedExtension l) l σ →
  ∀ F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l), IsLawOfLog l F →
  (∀ α : MaximalUnramifiedExtension l, ‖α‖ = 1 → σ (σ α) = α → NormRel l σ (phFF l g2 g3 s2 ε) α) →
  ∀ (ι n : Type) [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
    (f f' : ι → n → MaximalUnramifiedExtension l), IsHypPair σ f f' →
  ∀ be : MvPowerSeries (Fin 2) (K0 l), MvPowerSeries.constantCoeff be = 0 →
    Formalism.InvariantFactorPaths.G7.Simeq (MvPowerSeries.map (k0ToC l) (inParam l be))
      (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype (cob F (phFF l g2 g3 s2 ε))) →
  ∀ Θ : MvPowerSeries n ℂ_[l],
    Integral (mvExp (Formalism.L2.Th1.E.phSum (phL l g2 g3 s2 ε) : MvPowerSeries n ℂ_[l]) *
      @inParamK l _ n ℂ_[l] _ (wittFractionAlgebraCp l) Θ) →
    IntR (OcC l) (@inParamK l _ (ι ⊕ ι) ℂ_[l] _ (wittFractionAlgebraCp l)
      (MvPowerSeries.subst (hypLin l f f') Θ * MvPowerSeries.map (k0ToC l) (expS l (sumBe l be))))

end Formalism.L2.KerInert.K1
end
end

-- bundled from Formalism.LocalToGlobal.InertKernelTheory.KerTransAll
section
noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions Classical
open Formalism.L2.Th1.H (taylorMv tens4 kernel4 alphaQ stdH matH)

def KerTransAll : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Ker.Base D cc δ),
    Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc → Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → KerTransAlg B

end Formalism.L2.KerInert
end
end

-- bundled from Formalism.LocalToGlobal.InertKernelTheory.StatementCurve
section
noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.KerInert

open Formalism.MainNotions
open Formalism.L2.Th1.H (cmL CmOK)

def CurveTie : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), cc ≠ ⊥ → Odd (Ideal.absNorm cc) → δ ≠ 0 →
    ∃ (a₀ g : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (hl : (g : ℂ) * δ ≠ 0),
      CmOK a₀ b₀ c₀ D.host.d ∧ Ideal.absNorm cc = g ^ 2 * a₀ ∧ cc ≤ Ideal.span {(g : 𝓞 D.host.K)} ∧
      TaylorLogMetric.lamOf D cc δ = (cmL a₀ b₀ D.host.d ha hd ((g : ℂ) * δ) hl).lattice.toAddSubgroup

def CmReBase : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ), TaylorLogMetric.IsCurveIdeal D cc → δ ≠ 0 →
    ∃ (a₀ g : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (hl : (g : ℂ) * δ ≠ 0),
      CmOK a₀ b₀ c₀ D.host.d ∧ Ideal.absNorm cc = g ^ 2 * a₀ ∧
      (cmL a₀ b₀ D.host.d ha hd ((g : ℂ) * δ) hl).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ ∧
      GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc δ) (((g : ℂ) * δ) * a₀ / 2) ∧
      (B.ω₀ - ((g : ℂ) * δ) * a₀) / 2 ∈ TaylorLogMetric.lamOf D cc δ

end Formalism.L2.KerInert
end
end

-- bundled from Formalism.LocalToGlobal.InertKernelTheory.StatementReBase
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

def ThMMReBase : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), TaylorLogMetric.IsCurveIdeal D cc →
    ∃ (a₀ g : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (hl : (g : ℂ) * δ ≠ 0) (B' : Base D cc δ),
      CmOK a₀ b₀ c₀ D.host.d ∧ Ideal.absNorm cc = g ^ 2 * a₀ ∧ B'.IsCm a₀ b₀ ha hd ((g : ℂ) * δ) hl ∧
      B'.L.lattice = B.L.lattice ∧ B'.γ₀ = B.γ₀ ∧ B'.gC = B.gC ∧ B'.kappa = B.kappa ∧
      (B.ω₀ - B'.ω₀) / 2 ∈ B.L.lattice ∧ B'.IsThMM = B.IsThMM ∧ B'.thMM = B.thMM

end Formalism.L2.KerInert
end
end

