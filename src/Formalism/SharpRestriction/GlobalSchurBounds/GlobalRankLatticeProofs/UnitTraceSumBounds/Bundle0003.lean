module

public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.TaylorLogMetric
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0007

@[expose] public section

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.AddPtW
section
open Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric Formalism.BasicNotions

namespace Formalism.MainNotions.Ext

def PtW {p : ℕ} [Fact p.Prime] {σ : Type} (a : MvPowerSeries σ ℂ_[p]) : Prop :=
  IntegralW a ∧ MvPowerSeries.constantCoeff a = 0

def AddPtW : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), g.Ok → IntegralW (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) →
    ∀ (σ : Type) (a b : MvPowerSeries σ ℂ_[p]), PtW a → PtW b → PtW (g.add a b)

def MulPtW : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), g.Ok → ∀ c : ℂ_[p], IntegralW (g.mulBy c (Xv ()) : MvPowerSeries Unit ℂ_[p]) →
    ∀ (σ : Type) (a : MvPowerSeries σ ℂ_[p]), PtW a → PtW (g.mulBy c a)

end Formalism.MainNotions.Ext
end

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.CubeIdentityFromAdditionFormula
section
open Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric

namespace Formalism.MainNotions.Ext.CutA

def UnitTraceSumSecondBound : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), g.Ok → IntegralMv (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) →
    ∃ n : MvPowerSeries (Fin 2) ℂ_[p], IntegralMv n ∧ MvPowerSeries.constantCoeff n = 1 ∧
      (Xv 0) ^ 2 * (PowerSeries.subst (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) g.wq)⁻¹ -
          (Xv 1) ^ 2 * (PowerSeries.subst (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) g.wq)⁻¹ =
        g.add (Xv 0) (Xv 1) * g.sub (Xv 0) (Xv 1) * n

def CubeIdentityFromAdditionFormula : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), g.Ok →
    PowerSeries.constantCoeff (ePhi1 g.lam g.abelian₂ g.C g.wq) = 1 →
    g.add (Xv 0) (Xv 1) * g.sub (Xv 0) (Xv 1) *
        PowerSeries.subst (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) (ePhi1 g.lam g.abelian₂ g.C g.wq) *
        PowerSeries.subst (g.sub (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) (ePhi1 g.lam g.abelian₂ g.C g.wq) =
      ((Xv 0) ^ 2 * (PowerSeries.subst (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) g.wq)⁻¹ -
          (Xv 1) ^ 2 * (PowerSeries.subst (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) g.wq)⁻¹) *
        PowerSeries.subst (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) (ePhi1 g.lam g.abelian₂ g.C g.wq) ^ 2 *
        PowerSeries.subst (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) (ePhi1 g.lam g.abelian₂ g.C g.wq) ^ 2 →
    (∃ n : MvPowerSeries (Fin 2) ℂ_[p], IntegralMv n ∧ MvPowerSeries.constantCoeff n = 1 ∧
      (Xv 0) ^ 2 * (PowerSeries.subst (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) g.wq)⁻¹ -
          (Xv 1) ^ 2 * (PowerSeries.subst (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) g.wq)⁻¹ =
        g.add (Xv 0) (Xv 1) * g.sub (Xv 0) (Xv 1) * n) →
    Simeq (g.phAt (g.add (Xv 0) (Xv 1)) + g.phAt (g.sub (Xv 0) (Xv 1)) : MvPowerSeries (Fin 2) ℂ_[p])
      (2 * g.phAt (Xv 0) + 2 * g.phAt (Xv 1))

end Formalism.MainNotions.Ext.CutA
end

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.CubeOfTwoIdentities
section
open Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric

namespace Formalism.MainNotions.Ext.CutA

def CubeOfTwoIdentities : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), g.Ok →
    Simeq (g.phAt (g.add (Xv 0) (Xv 1)) + g.phAt (g.sub (Xv 0) (Xv 1)) : MvPowerSeries (Fin 2) ℂ_[p])
      (2 * g.phAt (Xv 0) + 2 * g.phAt (Xv 1)) →
    Simeq (g.phAt (g.add (g.add (Xv 0) (Xv 1)) (Xv 2)) + g.phAt (g.sub (Xv 0) (Xv 1)) +
        g.phAt (g.sub (Xv 1) (Xv 2)) + g.phAt (g.sub (Xv 2) (Xv 0)) : MvPowerSeries (Fin 3) ℂ_[p])
      (3 * (g.phAt (Xv 0) + g.phAt (Xv 1) + g.phAt (Xv 2))) →
    Simeq (g.phAt (g.add (g.add (Xv 0) (Xv 1)) (Xv 2)) - g.phAt (g.add (Xv 0) (Xv 1)) -
        g.phAt (g.add (Xv 1) (Xv 2)) - g.phAt (g.add (Xv 2) (Xv 0)) +
        g.phAt (Xv 0) + g.phAt (Xv 1) + g.phAt (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p]) 0

def PhGramG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p) (S : Set (ℂ_[p] × ℂ_[p])), g.Ok →
    (∀ α ∈ S, α.swap ∈ S) →
    (∀ α ∈ S, IntegralMv (g.mulBy α.1 (Xv ()) : MvPowerSeries Unit ℂ_[p])) →
    IntegralMv (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) →
    (∀ α ∈ S, Simeq (g.phAt (g.mulBy α.1 (Xv ())) : MvPowerSeries Unit ℂ_[p])
        (MvPowerSeries.C (α.1 * α.2) * g.phAt (Xv ()))) →
    (∀ α ∈ S, Simeq (g.be (g.mulBy α.1 (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
        (g.be (Xv 0) (g.mulBy α.2 (Xv 1)))) →
    Simeq (g.be (g.add (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p])
      (g.be (Xv 0) (Xv 2) + g.be (Xv 1) (Xv 2)) →
    ∀ (κ : Type) [Fintype κ] (k : ℕ) (A : Fin k → κ → ℂ_[p] × ℂ_[p]), (∀ j i, A j i ∈ S) →
      Simeq (g.PhOn A)
        (∑ j, MvPowerSeries.C (hP (A j) (A j)).1 * g.phAt (Xv j) +
          ∑ j, ∑ j' ∈ Finset.univ.filter (fun j' => j < j'), g.be (g.mulBy (hP (A j) (A j')).1 (Xv j)) (Xv j'))

def GramUnitEq : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), g.Ok →
    ∀ (n : ℕ) (de : Fin n → Fin n → ℂ_[p] × ℂ_[p]), (∀ i j, hP (de i) (de j) = if i = j then 1 else 0) →
      (∑ j, MvPowerSeries.C (hP (de j) (de j)).1 * g.phAt (Xv j) +
          ∑ j, ∑ j' ∈ Finset.univ.filter (fun j' => j < j'), g.be (g.mulBy (hP (de j) (de j')).1 (Xv j)) (Xv j') :
        MvPowerSeries (Fin n) ℂ_[p]) = ∑ j, g.phAt (Xv j)

def JetsHigh : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), g.Ok →
    Simeq (g.phAt (g.add (g.add (Xv 0) (Xv 1)) (Xv 2)) - g.phAt (g.add (Xv 0) (Xv 1)) -
        g.phAt (g.add (Xv 1) (Xv 2)) - g.phAt (g.add (Xv 2) (Xv 0)) +
        g.phAt (Xv 0) + g.phAt (Xv 1) + g.phAt (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p]) 0 →
    ∀ i : ℕ, i ≠ 1 → i ≠ 2 → IsIntP (g.jetPh i)

def JetsOne : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), g.Ok → p ≠ 2 →
    Simeq (g.phAt (g.mulBy (-1) (Xv ())) : MvPowerSeries Unit ℂ_[p]) (g.phAt (Xv ())) →
    IsIntP (g.jetPh 1)

def JetsTwo : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p) (a b : ℂ_[p]), g.Ok →
    Simeq (g.be (g.mulBy a (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) (g.be (Xv 0) (g.mulBy b (Xv 1))) →
    IsIntP ((a - b) * g.jetPh 2)

end Formalism.MainNotions.Ext.CutA
end

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.EndIntWOf
section
open Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric Formalism.BasicNotions

namespace Formalism.MainNotions.Ext

def CoefWfRing : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (f g : MvPowerSeries σ ℂ_[p]), CoefWf f → CoefWf g →
    CoefWf (f + g) ∧ CoefWf (f - g) ∧ CoefWf (f * g) ∧ ∀ c : ℂ_[p], InWf c → CoefWf (MvPowerSeries.C c * f)

def SubstWf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (f : PowerSeries ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]),
    CoefWf f → IntegralW a → MvPowerSeries.constantCoeff a = 0 → CoefWf (PowerSeries.subst a f)

def EndIntWG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), g.Ok → ModelOverW g.lam g.abelian₂ g.C → ∀ α ∈ W2pair p,
    IntegralMv (g.mulBy α.1 (Xv ()) : MvPowerSeries Unit ℂ_[p]) →
    IntegralW (g.mulBy α.1 (Xv ()) : MvPowerSeries Unit ℂ_[p])

end Formalism.MainNotions.Ext
end

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.ModelShortOf
section
namespace Formalism.MainNotions.Ext

end Formalism.MainNotions.Ext

open Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric Formalism.BasicNotions

namespace Formalism.MainNotions.Ext

def BiaddOfCube : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), g.Ok →
    Simeq (g.phAt (g.add (g.add (Xv 0) (Xv 1)) (Xv 2)) - g.phAt (g.add (Xv 0) (Xv 1)) -
        g.phAt (g.add (Xv 1) (Xv 2)) - g.phAt (g.add (Xv 2) (Xv 0)) +
        g.phAt (Xv 0) + g.phAt (Xv 1) + g.phAt (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p]) 0 →
    Simeq (g.be (g.add (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p])
      (g.be (Xv 0) (Xv 2) + g.be (Xv 1) (Xv 2)) ∧
    Simeq (g.be (Xv 0) (g.add (Xv 1) (Xv 2)) : MvPowerSeries (Fin 3) ℂ_[p])
      (g.be (Xv 0) (Xv 1) + g.be (Xv 0) (Xv 2))

def AddIntG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), g.Ok →
    IntegralMv (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) ∧
    (ModelOverW g.lam g.abelian₂ g.C → IntegralW (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]))

end Formalism.MainNotions.Ext

open Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric Formalism.BasicNotions NumberField

namespace Formalism.MainNotions.Ext

def OkpInertG : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (c : K →+* K) (p : ℕ) [Fact p.Prime] (τ : K →+* ℂ_[p]),
    Module.finrank ℚ K = 2 → (∃ x, c x ≠ x) → p ≠ 2 → (Ideal.span {(p : 𝓞 K)}).IsPrime →
    closure (Set.range fun a : 𝓞 K => (τ (a : K), τ (c (a : K)))) = W2pair p

end Formalism.MainNotions.Ext
end

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.PhNormOfUnits
section
open Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric

namespace Formalism.MainNotions.Ext.CutA

def PhNormClosed : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p) (T : Set (ℂ_[p] × ℂ_[p])), g.Ok →
    (∀ α ∈ T, IntegralMv (g.mulBy α.1 (Xv ()) : MvPowerSeries Unit ℂ_[p])) →
    (∀ α ∈ T, Simeq (g.phAt (g.mulBy α.1 (Xv ())) : MvPowerSeries Unit ℂ_[p])
        (MvPowerSeries.C (α.1 * α.2) * g.phAt (Xv ()))) →
    ∀ α ∈ closure T, Simeq (g.phAt (g.mulBy α.1 (Xv ())) : MvPowerSeries Unit ℂ_[p])
        (MvPowerSeries.C (α.1 * α.2) * g.phAt (Xv ()))

def PhNormOfUnits : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p) (S : Set (ℂ_[p] × ℂ_[p])), g.Ok → p ≠ 2 →
    ((2 : ℂ_[p]), (2 : ℂ_[p])) ∈ S → (∀ α ∈ S, α.swap ∈ S) → (∀ α ∈ S, ∀ β ∈ S, α + β ∈ S) →
    (∀ α ∈ S, ∀ β ∈ S, α * β ∈ S) →
    (∀ α ∈ S, IntegralMv (g.mulBy α.1 (Xv ()) : MvPowerSeries Unit ℂ_[p])) →
    IntegralMv (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) →
    (∀ α ∈ S, ∃ n : ℤ_[p], α.1 + α.2 = zc n) → (∀ α ∈ S, ∃ n : ℤ_[p], α.1 * α.2 = zc n) →
    (∀ α ∈ S, ∃ β ∈ S, ∃ γ ∈ S, ‖β.1‖ = 1 ∧ ‖β.2‖ = 1 ∧ ‖γ.1‖ = 1 ∧ ‖γ.2‖ = 1 ∧ α = β + γ) →
    Simeq (g.be (g.add (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p])
      (g.be (Xv 0) (Xv 2) + g.be (Xv 1) (Xv 2)) →
    (∀ α ∈ S, ‖α.1‖ = 1 → ‖α.2‖ = 1 → Simeq (g.phAt (g.mulBy α.1 (Xv ())) : MvPowerSeries Unit ℂ_[p])
        (MvPowerSeries.C (α.1 * α.2) * g.phAt (Xv ()))) →
    ∀ α ∈ S, Simeq (g.phAt (g.mulBy α.1 (Xv ())) : MvPowerSeries Unit ℂ_[p])
        (MvPowerSeries.C (α.1 * α.2) * g.phAt (Xv ()))

end Formalism.MainNotions.Ext.CutA
end

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.ReadWHolds
section
namespace Formalism.MainNotions.GL3Theta

theorem readW_holds : readW := expIntegralWitt

end Formalism.MainNotions.GL3Theta
end

