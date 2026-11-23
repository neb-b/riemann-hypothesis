module

public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle0003
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0002
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0014
public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CubeFormalIdentities.CoeffPowMulPowEqZero
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0001
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0010
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0008
public import Formalism.PeriodIntegrals.Bundle0001
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0012
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0013
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.SharpRestriction.GlobalSchurBounds.Bundle0002
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0030
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0022

@[expose] public section

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.AdditionIdentityOfSigmaFormula
section
namespace Formalism.MainNotions.Ext.CutA

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta NumberField

def EPhiOne (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p), At D cc δ g →
    PowerSeries.constantCoeff (ePhi1 g.lam g.abelian₂ g.C g.wq) = 1

def PAdicSigmaAdditionFormula (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p), At D cc δ g →
    g.add (Xv 0) (Xv 1) * g.sub (Xv 0) (Xv 1) *
        PowerSeries.subst (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) (ePhi1 g.lam g.abelian₂ g.C g.wq) *
        PowerSeries.subst (g.sub (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) (ePhi1 g.lam g.abelian₂ g.C g.wq) =
      ((Xv 0) ^ 2 * (PowerSeries.subst (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) g.wq)⁻¹ -
          (Xv 1) ^ 2 * (PowerSeries.subst (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) g.wq)⁻¹) *
        PowerSeries.subst (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) (ePhi1 g.lam g.abelian₂ g.C g.wq) ^ 2 *
        PowerSeries.subst (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) (ePhi1 g.lam g.abelian₂ g.C g.wq) ^ 2

theorem addition_identity_of_sigma_formula (H31 : UnitTraceSumSecondBound) (HC : CubeIdentityFromAdditionFormula) (D : D7) (hQ : PAdicSigmaAdditionFormula D) (hE : EPhiOne D) (ha : addInt D) :
    cube2 D := by
  intro p _ cc δ g hA
  have ok : g.Ok := hA.2.2.2.2
  exact HC p g ok (hE p cc δ g hA) (hQ p cc δ g hA) (H31 p g ok (ha p cc δ g hA).1)

end Formalism.MainNotions.Ext.CutA
end

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.FormalGroupLawFirstHalfHolds
section
namespace Formalism.MainNotions.Ext

theorem biaddOfCube_holds : BiaddOfCube :=
  fun p _ g hOk hc => biadditiveOfCube_holds p g.l g.ex g.ph hOk.2.2.1 hOk.2.2.2 hc

theorem beBiadd_of_cube (D : Formalism.BasicNotions.D7) (h : Formalism.MainNotions.GL3Theta.cube D) : Formalism.MainNotions.GL3Theta.beBiadd D := by
  intro p _ cc δ g hA
  exact biaddOfCube_holds p g hA.2.2.2.2 (h p cc δ g hA)

theorem addIntG_holds : AddIntG := fun p _ g hOk =>
  additive_integral_generation p g.W g.wq g.ex hOk.1.1 hOk.1.2.1 hOk.1.2.2.1 hOk.1.2.2.2.1 hOk.1.2.2.2.2.1 hOk.2.1 hOk.2.2.1 hOk.2.2.2

theorem addInt_holds (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.GL3Theta.addInt D := by
  intro p _ cc δ g hA
  exact addIntG_holds p g hA.2.2.2.2

end Formalism.MainNotions.Ext
end

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.RetcutA
section
namespace Formalism.MainNotions.Ext.CutA

theorem phNormOfUnits_holds : PhNormOfUnits := by
  intro p _ g S hok
  exact phase_norm_units p g.l g.ex g.ph S hok.2.2.1 hok.2.2.2

theorem phNormClosed_holds : PhNormClosed := by
  intro p _ g S hok
  exact phase_norm_limit_target p g.l g.ex g.ph S hok.2.2.1 hok.2.2.2

end Formalism.MainNotions.Ext.CutA
end

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.StmtEndIntWOfOkp
section
namespace Formalism.MainNotions.Ext

theorem substWf_holds : SubstWf :=
  fun p _ σ f a hf ha h0 => witt_substitution p σ f a hf (fun n => ⟨0, by rw [pow_zero, one_mul]; exact ha n⟩) h0

theorem coefWfRing_holds : CoefWfRing := witt_ring_structure

theorem endIntWG_holds : EndIntWG :=
  fun p _ g hOk hW α hα hI =>
    witt_frobenius_end p g.W g.wq g.ex hW.1 hW.2.1 hW.2.2.1 hW.2.2.2.1 hW.2.2.2.2 hOk.2.1 hOk.2.2.1 hOk.2.2.2 α.1
      ⟨0, by simpa using witt_pairing p α hα⟩ hI

end Formalism.MainNotions.Ext
end

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TraceSum
section
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 NumberField

namespace Formalism.MainNotions.Ext

def TraceSum : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (K : IntermediateField ℚ E) (φ₀ : E →+* ℂ) (S : Type) [Fintype S]
    (emb : S → E →+* ℂ), Function.Injective emb → (∀ (s : S) (a : K), emb s (a : E) = φ₀ (a : E)) →
    Fintype.card S = Module.finrank K E →
    ∀ y : E, ∑ s, emb s y = φ₀ ((Algebra.trace K E y : K) : E)

end Formalism.MainNotions.Ext
end

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.UpperSlopeOfMaximalConstant
section
namespace Formalism.MainNotions.flipTwoThree

theorem hookBound_holds : HookBound := hook_length_bound

end Formalism.MainNotions.flipTwoThree
end

