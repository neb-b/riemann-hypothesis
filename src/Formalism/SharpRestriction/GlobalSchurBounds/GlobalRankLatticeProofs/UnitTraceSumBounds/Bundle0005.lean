module

public import Formalism.SharpRestriction.GlobalSchurBounds.StatementTranslationInvariantSeventh
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle0003
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle0004
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0005
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0011
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0002
public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupSplitting.ExpCongruenceExtendsToSum
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupSplitting.Development
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupSplitting.Bundle0001
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0008
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Columns
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MonomialFrameSpan.DetSubmatrixFun
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IsometryDerivative.ExistsOePerm
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0006
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WwMain
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0004

@[expose] public section

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.BeConjOfNorm
section
open Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3r7

namespace Formalism.MainNotions.Ext.CutA

def SDiffOfGram : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p) (S : Set (ℂ_[p] × ℂ_[p])), g.Ok →
    (0 : ℂ_[p] × ℂ_[p]) ∈ S → (∀ α ∈ S, α.swap ∈ S) → (∀ α ∈ S, ∀ β ∈ S, α + β ∈ S) → (∀ α ∈ S, ∀ β ∈ S, α * β ∈ S) →
    (∀ (κ : Type) [Fintype κ] (k : ℕ) (A : Fin k → κ → ℂ_[p] × ℂ_[p]), (∀ j i, A j i ∈ S) →
      Simeq (g.PhOn A)
        (∑ j, MvPowerSeries.C (hP (A j) (A j)).1 * g.phAt (Xv j) +
          ∑ j, ∑ j' ∈ Finset.univ.filter (fun j' => j < j'), g.be (g.mulBy (hP (A j) (A j')).1 (Xv j)) (Xv j'))) →
    (∀ α ∈ S, Simeq (g.be (g.mulBy α.1 (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
        (g.be (Xv 0) (g.mulBy α.2 (Xv 1)))) →
    ∀ (κ ι ι' : Type) [Fintype κ] [Fintype ι] [Fintype ι'] (a : ι → κ → ℂ_[p] × ℂ_[p]) (a' : ι' → κ → ℂ_[p] × ℂ_[p]),
      (∀ e k, a e k ∈ S) → (∀ e k, a' e k ∈ S) →
      Simeq (sdL g a a') (sdR g a a') ∧ Simeq (sdL g a a') (sdR' g a a')

def SplitZeroG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p) (S : Set (ℂ_[p] × ℂ_[p])), g.Ok → p ≠ 2 →
    (∀ α ∈ S, α.swap ∈ S) →
    (∀ α ∈ S, IntegralMv (g.mulBy α.1 (Xv ()) : MvPowerSeries Unit ℂ_[p])) →
    IntegralMv (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) →
    (∀ α ∈ S, Simeq (g.be (g.mulBy α.1 (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
        (g.be (Xv 0) (g.mulBy α.2 (Xv 1)))) →
    Simeq (g.be (g.add (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p])
      (g.be (Xv 0) (Xv 2) + g.be (Xv 1) (Xv 2)) →
    Simeq (g.phAt (g.mulBy (-1) (Xv ())) : MvPowerSeries Unit ℂ_[p]) (g.phAt (Xv ())) →
    (∃ α ∈ S, ∃ a b : ℤ_[p], α = (zc a, zc b) ∧ IsUnit (a - b)) →
    Simeq (g.be (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) 0 ∧ Simeq (g.phAt (Xv ()) : MvPowerSeries Unit ℂ_[p]) 0

def BeConjOfNorm : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p) (S : Set (ℂ_[p] × ℂ_[p])), g.Ok →
    (∀ α ∈ S, α.swap ∈ S) → (∀ α ∈ S, ∀ β ∈ S, α + β ∈ S) →
    (∀ α ∈ S, IntegralMv (g.mulBy α.1 (Xv ()) : MvPowerSeries Unit ℂ_[p])) →
    IntegralMv (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) →
    (∀ α ∈ S, ∃ n : ℤ_[p], α.1 * α.2 = zc n) →
    (∀ α ∈ S, ∃ β ∈ S, ∃ γ ∈ S, ‖β.1‖ = 1 ∧ ‖γ.1‖ = 1 ∧ α = β + γ) →
    (∀ α ∈ S, Simeq (g.phAt (g.mulBy α.1 (Xv ())) : MvPowerSeries Unit ℂ_[p])
        (MvPowerSeries.C (α.1 * α.2) * g.phAt (Xv ()))) →
    Simeq (g.be (g.add (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p])
      (g.be (Xv 0) (Xv 2) + g.be (Xv 1) (Xv 2)) →
    ∀ α ∈ S, Simeq (g.be (g.mulBy α.1 (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
        (g.be (Xv 0) (g.mulBy α.2 (Xv 1)))

end Formalism.MainNotions.Ext.CutA
end

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.CoefWfPhAt
section
namespace Formalism.MainNotions.Ext

open Formalism.BasicNotions Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric

section

variable {p : ℕ} [Fact p.Prime]

theorem ptW_X {σ : Type} (i : σ) : PtW (Xv i : MvPowerSeries σ ℂ_[p]) := by
  classical
  unfold PtW
  constructor
  · intro n
    rw [MvPowerSeries.coeff_X]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  · simp

theorem coefWf_add {σ : Type} {f g : MvPowerSeries σ ℂ_[p]} (hf : CoefWf f) (hg : CoefWf g) : CoefWf (f + g) := (coefWfRing_holds p σ f g hf hg).1

theorem coefWf_sub {σ : Type} {f g : MvPowerSeries σ ℂ_[p]} (hf : CoefWf f) (hg : CoefWf g) : CoefWf (f - g) := (coefWfRing_holds p σ f g hf hg).2.1

theorem coefWf_phAt (g : G1 p) (hph : CoefWf g.ph) {σ : Type} {a : MvPowerSeries σ ℂ_[p]} (ha : PtW a) : CoefWf (g.phAt a) := by
  obtain ⟨ha1, ha2⟩ := ha
  exact substWf_holds p σ g.ph a hph ha1 ha2

theorem coefWf_be (HA : AddPtW) (g : G1 p) (hOk : g.Ok) (hF : IntegralW (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]))
    (hph : CoefWf g.ph) {σ : Type} {a b : MvPowerSeries σ ℂ_[p]} (ha : PtW a) (hb : PtW b) : CoefWf (g.be a b) := by
  have hab : PtW (g.add a b) := HA p g hOk hF σ a b ha hb
  show CoefWf (g.phAt (g.add a b) - g.phAt a - g.phAt b)
  exact coefWf_sub (coefWf_sub (coefWf_phAt g hph hab) (coefWf_phAt g hph ha)) (coefWf_phAt g hph hb)

theorem simeqW_of {σ : Type} {f g : MvPowerSeries σ ℂ_[p]} (hf : CoefWf f) (hg : CoefWf g) (h : Simeq f g) : SimeqW f g := by

  obtain ⟨h0, hI⟩ := h
  have hr : SimeqW (f - g) 0 :=
    readW_holds p σ (f - g) (coefWf_sub hf hg) (And.intro (by simpa using h0) (by simpa using hI))
  obtain ⟨r0, rI⟩ := hr
  exact And.intro (by simpa using r0) (by simpa using rI)

end

end Formalism.MainNotions.Ext
end

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.LevelRestrictionOfGroupLawHolds
section
namespace Formalism.MainNotions.Ext.CutA

open Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3r7

theorem ph0 {p : ℕ} [Fact p.Prime] (g : G1 p) : PowerSeries.constantCoeff g.ph = 0 := by
  unfold G1.ph
  rw [map_neg, neg_eq_zero]
  show logMv _ 0 = 0
  unfold logMv
  simp

theorem fglData {p : ℕ} [Fact p.Prime] (g : G1 p) (h : g.Ok) : PI.FglGram.Data g.l g.ex g.ph :=
  ⟨h.2.2.1, h.2.2.2, ph0 g⟩

theorem cube_of_two_identities_holds : CubeOfTwoIdentities := by
  intro p _ g h
  exact cube_relation_of_parallelogram p g.l g.ex g.ph (fglData g h)

theorem phGramG_holds : PhGramG := by
  first
  | exact phase_gram'
  | (intro p _ g; intros; apply phase_gram' <;> first | exact fglData g ‹_› | assumption)
  | (unfold PhGramG; done)

theorem gramUnitEq_holds : GramUnitEq := by
  first
  | exact gramExpansion_orthonormal
  | (intro p _ g; intros; apply gramExpansion_orthonormal <;> first | exact fglData g ‹_› | assumption)
  | (unfold GramUnitEq; done)

theorem jetsHigh_holds : JetsHigh :=
  fun p _ g hOk => jets_high p g.W g.wq g.ex g.ph hOk.1.1 hOk.1.2.1 hOk.1.2.2.1 hOk.1.2.2.2.1 hOk.1.2.2.2.2.1 hOk.2.1 hOk.2.2.1
    hOk.2.2.2

theorem jetsOne_holds : JetsOne :=
  fun p _ g hOk => jets_one p g.W g.wq g.ex g.ph hOk.1.1 hOk.1.2.1 hOk.1.2.2.1 hOk.1.2.2.2.1 hOk.1.2.2.2.2.1 hOk.2.1 hOk.2.2.1
    hOk.2.2.2

theorem jetsTwo_holds : JetsTwo :=
  fun p _ g a b hOk => jets_two p g.W g.wq g.ex g.ph a b hOk.1.1 hOk.1.2.1 hOk.1.2.2.1 hOk.1.2.2.2.1 hOk.1.2.2.2.2.1 hOk.2.1
    hOk.2.2.1 hOk.2.2.2

end Formalism.MainNotions.Ext.CutA
end

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.ThetaIsometryFactsHold
section
namespace Formalism.MainNotions.GL3Columns

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric

theorem wwCB_holds (D : D7) : wwCB D := fun k _ N nu y => cauchy_binet_minors (Bool × HH D) k N nu y

theorem ww_holds (D : D7) : ww D :=
  fun l _ N0 N1 nu Th ph Q hQ y' => minor_identity (Bool × HH D) l N0 N1 nu Th ph Q hQ y'

theorem wwInj_holds (D : D7) : wwInj D :=
  fun l _ N nu ph hy J => wwInjective_of cauchy_binet_minors (Bool × HH D) l N nu ph hy J

end Formalism.MainNotions.GL3Columns
end

