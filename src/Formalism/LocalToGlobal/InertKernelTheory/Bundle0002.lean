module

public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Mathlib
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.SemiChar
public import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem

@[expose] public section

-- bundled from Formalism.LocalToGlobal.InertKernelTheory.DefsBeW
section
namespace Formalism.L2.KerInert

open Formalism.BasicNotions Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric NumberField

def PhWAll : Prop := ∀ D : D7, phW D

def EndIntInert : Prop :=
  ∀ (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p), At D cc δ g →
    5 ≤ p → InertK D p → ModelOverW g.lam g.abelian₂ g.C →
    ∀ α ∈ OKp D g.lam, IntegralMv (g.mulBy α.1 (Xv ()) : MvPowerSeries Unit ℂ_[p])

def BiaddInert : Prop :=
  ∀ (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p), At D cc δ g →
    5 ≤ p → InertK D p → ModelOverW g.lam g.abelian₂ g.C →
    Simeq (g.be (g.add (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p])
      (g.be (Xv 0) (Xv 2) + g.be (Xv 1) (Xv 2)) ∧
    Simeq (g.be (Xv 0) (g.add (Xv 1) (Xv 2)) : MvPowerSeries (Fin 3) ℂ_[p])
      (g.be (Xv 0) (Xv 1) + g.be (Xv 0) (Xv 2))

def PhNormOKInert : Prop :=
  ∀ (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p), At D cc δ g →
    5 ≤ p → InertK D p → ModelOverW g.lam g.abelian₂ g.C →
    ∀ a : 𝓞 D.host.K, Nat.Coprime (Algebra.norm ℤ a).natAbs p →
      Simeq (g.phAt (g.mulBy (tauK D g.lam (a : D.host.K)) (Xv ())) : MvPowerSeries Unit ℂ_[p])
        (MvPowerSeries.C (tauK D g.lam (a : D.host.K) * tauKc D g.lam (a : D.host.K)) * g.phAt (Xv ()))

end Formalism.L2.KerInert
end

-- bundled from Formalism.LocalToGlobal.InertKernelTheory.DefsSigma
section
noncomputable section

namespace Formalism.L2.KerInert.Sigma

open NumberField Formalism.BasicNotions

def InvAlg : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc → Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ L : PeriodPair, L.lattice.toAddSubgroup = Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ →
      L.g₂ ∈ Formalism.MainNotions.TaylorLogMetric.Qbar ∧ L.g₃ ∈ Formalism.MainNotions.TaylorLogMetric.Qbar

def SecondEisensteinAlgebraic : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc → Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ L : PeriodPair, L.lattice.toAddSubgroup = Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ →
      Formalism.L2.Th1.F.s2 L ∈ Formalism.MainNotions.TaylorLogMetric.Qbar

end Formalism.L2.KerInert.Sigma
end
end

-- bundled from Formalism.LocalToGlobal.InertKernelTheory.StatementBeW
section
namespace Formalism.L2.KerInert

open Formalism.BasicNotions

def BeWInert : Prop := ∀ D : D7, Formalism.MainNotions.GL3Theta.beW D

end Formalism.L2.KerInert
end

-- bundled from Formalism.LocalToGlobal.InertKernelTheory.StatementZ
section
noncomputable section

namespace Formalism.L2.KerInert

open Formalism.MainNotions.G Formalism.BasicNotions Formalism.MainNotions.FormalGroupSystem Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

def BeJetInt (p : ℕ) [Fact p.Prime] (be : MvPowerSeries (Fin 2) (K0 p)) : Prop :=
  MvPowerSeries.constantCoeff be = 0 ∧
    ∀ n : Fin 2 →₀ ℕ, ((∏ x ∈ n.support, (n x).factorial : ℕ) : K0 p) * MvPowerSeries.coeff n be ∈
      Set.range (algebraMap (WW p) (K0 p))

def LowAtZero : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (Y : Pend X), BeJetInt p Y.be → ∀ v, ∀ j < X.mm, Y.LowAt j v 0

def Adm11OfIntegralJets : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (p : ℕ) [Fact p.Prime] (X : Sys p) (Y : Pend X), BeJetInt p Y.be → adm11 D X Y

def BeJetOfProp : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (be : MvPowerSeries (Fin 2) (K0 p)), BeProp p be → BeJetInt p be

end Formalism.L2.KerInert
end
end

