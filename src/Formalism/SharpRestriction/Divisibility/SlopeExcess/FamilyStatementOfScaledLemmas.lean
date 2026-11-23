module

public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Mathlib
public import Formalism.LocalRingCardinality.DataArith
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.PolygonSlopeSum
public import Formalism.HarderNarasimhan.Statement
public import Formalism.HermitianLattices.HermitianLatticesProofs.IndexBasic
public import Formalism.SizeWindowBrackets.ChainSlopeWindows.TruncatedLatticeHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndexDeterminant.NegLogValuation
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdempotentTransfer.NormAtAddLe
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0029
public import Formalism.PeriodIntegrals.GTDefs
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitPowerNormScale.NormUnitsZpowSq
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinTopCoefficient.CardEraseIccMin
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinTopCoefficient.InterlacingDefectEqCard
public import Formalism.LocalRingCardinality.FactDelDualNabla

@[expose] public section

noncomputable section

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.PrimeDegreeVariant

namespace Formalism.MainNotions.DIV.Proofs.ScaledLatticeNorms

section Norms

variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]

end Norms

section Lat

variable {K : Type} [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]
  {W κ : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
  [Fintype κ] [DecidableEq κ]

theorem mu_le_muMax (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det)
    (M : Submodule (𝓞 K) V) (hM : M.FG) (hM0 : M ≠ ⊥) :
    Formalism.HN.muDef b X M ≤ Formalism.HN.muMaxDef b X M := by
  have hL := (Formalism.HN.plLat K V ι b X hX M hM).1
  have := (Formalism.HN.muChar (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X) M hL hM0).2.2.2.2
  unfold Formalism.HN.muDef Formalism.HN.muMaxDef; linarith

end Lat

section Level

variable {K : Type} [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K]

end Level

section Reals

end Reals

section Zero

theorem scaled_lattice_nonzero_holds (D : D7) : Formalism.MainNotions.PrimeDegreeVariant.Conclusion0 D := by
  have : ∀ k, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  intro Y hY
  unfold Formalism.BasicNotions.lam0
  rw [D.nd.restN_card_levelGroup_eq]
  have hNpos : ∀ k, 0 < Nat.card (GL (Fin D.R.r) (ZMod (D.host.g k))) := fun k => Nat.card_pos
  have hNle : ∀ k, Nat.card (GL (Fin D.R.r) (ZMod (D.host.g k))) ≤ D.host.g k ^ (D.R.r * D.R.r) := by
    intro k
    have h1 : Nat.card (GL (Fin D.R.r) (ZMod (D.host.g k))) ≤
        Nat.card (Fin D.R.r → Fin D.R.r → ZMod (D.host.g k)) :=
      Nat.card_le_card_of_injective (fun u : GL (Fin D.R.r) (ZMod (D.host.g k)) => ((u : Matrix _ _ _) :
        Fin D.R.r → Fin D.R.r → ZMod (D.host.g k))) (fun a b h => Units.ext h)
    have h2 : Nat.card (Fin D.R.r → Fin D.R.r → ZMod (D.host.g k)) = D.host.g k ^ (D.R.r * D.R.r) := by
      rw [Nat.card_fun, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin, ← pow_mul]
    exact h2 ▸ h1
  have hg2 : ∀ k, (2 : ℝ) ≤ D.host.g k := fun k => by exact_mod_cast (D.host.g_prime k).two_le
  have hk : ∀ k, Real.log (Nat.card (GL (Fin D.R.r) (ZMod (D.host.g k))) : ℝ) ≤
      (D.R.r : ℝ) ^ 2 * Real.log (2 * Y) := by
    intro k
    have hNr : (Nat.card (GL (Fin D.R.r) (ZMod (D.host.g k))) : ℝ) ≤ (D.host.g k : ℝ) ^ (D.R.r * D.R.r) := by
      exact_mod_cast hNle k
    calc Real.log (Nat.card (GL (Fin D.R.r) (ZMod (D.host.g k))) : ℝ)
          ≤ Real.log ((D.host.g k : ℝ) ^ (D.R.r * D.R.r)) :=
          Real.log_le_log (by exact_mod_cast hNpos k) hNr
      _ = (D.R.r : ℝ) ^ 2 * Real.log (D.host.g k) := by rw [Real.log_pow]; push_cast; ring
      _ ≤ (D.R.r : ℝ) ^ 2 * Real.log (2 * Y) :=
          mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith [hg2 k]) (hY k)) (by positivity)
  push_cast
  rw [Real.log_prod (fun k _ => by have := hNpos k; positivity), Fin.sum_univ_two, Real.log_pow,
    Real.log_pow]
  have hf : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left (hk 0) hf, mul_le_mul_of_nonneg_left (hk 1) hf]

end Zero

section Main

attribute [local instance] Formalism.MainNotions.PrimeDegreeVariant.finiteLevelGroupFintype

variable {D : D7} {X : BaseLevelRowSide D}

end Main

end Formalism.MainNotions.DIV.Proofs.ScaledLatticeNorms

namespace Formalism.MainNotions.DIV.Proofs

open Formalism.MainNotions

end Formalism.MainNotions.DIV.Proofs
