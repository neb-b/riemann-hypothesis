module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0073
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XRootnumDual
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0025
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0021
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0067
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0075
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0072
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0070
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0065
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0068
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XXgzChowMahlerFibreavg
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0066
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0030
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0069
public import Development.WeilBound.CoreStatements.CommonZeroEvaluation.ConeBallLogGapIntegral
public import Development.WeilBound.CoreStatements.CommonZeroEvaluation.EvalEqZeroOfCommonZero
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.PluckerCoord

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualBundleIntersection
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem ck_rootNum_dual : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (V₁ : Type) [AddCommGroup V₁] [Module Ω V₁] (β : V →ₗ[Ω] V₁ →ₗ[Ω] Ω) (E E' : ChartBundle O (mseg x) N V) (F F' : ChartBundle O (mseg x) N V₁), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → SameGeneric O x E E' → IsDualLat O x β E.lat F.lat → IsDualLat O x β E'.lat F'.lat → (∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d + 1 - k) → ck O x d N F F' k L Q = (-1) ^ k * ck O x d N E E' k L Q) ∧ ∀ (j : ℕ), j ≤ d → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d - j) → ∀ a : O, a ≠ 0 → rootNum O x d N F (psum (Fin N) ℤ j) L Q a = (-1) ^ j * rootNum O x d N E (psum (Fin N) ℤ j) L Q a :=
  @PositivityTheory.Xgn.t_rootnum_dual

end GlobalTheory.CompanionTheory.Ar.Num
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MahlerSectionStatementHolds
section
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.Short

open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial

theorem mahlerDefect_eq_sum {n e δ : ℕ} (h : HermNorm n) {Z : ProjCycle ℂ n}
    {f : MvPolynomial (Fin (e + 1) × Fin n) ℂ} (hd : IsChowCycleData Z e δ f) :
    ∃ (c : ℂ) (g : Ideal (MvPolynomial (Fin n) ℂ) → MvPolynomial (Fin (e + 1) × Fin n) ℂ)
      (d : Ideal (MvPolynomial (Fin n) ℂ) → ℕ),
      (∀ W ∈ Z.support, IsChowForm W (e + 1) (g W) ∧ IsMultiHomog (d W) (g W)) ∧
      ∀ u : Fin n → ℂ, IsAdmissible Z u →
        mahlerDefect h e Z f u = Real.log ‖c‖ + ∑ W ∈ Z.support, (Z W : ℝ) *
          (mahler h e (specFirst (g W) u) - coneIntegral h W e (fsLog h u)) := by
  obtain ⟨c, hc, g, hg, hf⟩ := hd.chow
  have hf0 : C c * ∏ W ∈ Z.support, g W ^ Z W ≠ 0 :=
    mul_ne_zero (C_ne_zero.mpr hc)
      (Finset.prod_ne_zero_iff.mpr fun W hW => pow_ne_zero _ (hg W hW).1)
  have hhom : IsMultiHomog δ (C c * ∏ W ∈ Z.support, g W ^ Z W) := hf ▸ hd.homog
  obtain ⟨d, hdW, -⟩ := exists_degrees_of_chowFormCycle (Nat.succ_pos e) Z c g hg hhom hf0
  refine ⟨c, g, d, fun W hW => ⟨hg W hW, hdW W hW⟩, fun u hu => ?_⟩
  have hspec : specFirst f u = C c * ∏ W ∈ Z.support, specFirst (g W) u ^ Z W := by
    rw [hf]
    simp only [specFirst, map_mul, map_prod, map_pow, bind₁_C_right]
  have hq : ∀ W ∈ Z.support, specFirst (g W) u ≠ 0 ∧ IsMultiHomog (d W) (specFirst (g W) u) :=
    fun W hW => ⟨SpecFirstNe.full ℂ n e W (g W) u (hd.prime W hW) (hg W hW) (hu W hW),
      SpecFirstHomog.proof n e (d W) (g W) u (hdW W hW)⟩
  rw [mahlerDefect, hspec, _root_.GlobalTheory.CompanionTheory.Ar.Short.Crofton.mahler_C_mul_prod_pow n e h Z.support (fun W => specFirst (g W) u) d (fun W => Z W) c hc hq,
    cycleIntegral]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

theorem defectConstDim (e : ℕ) : DefectConstDim e := by
  intro n δ h Z f u u' hd hu hu'
  obtain ⟨c, g, d, hg, hsum⟩ := mahlerDefect_eq_sum h hd
  have hW : ∀ W ∈ Z.support, (Z W : ℝ) * (mahler h e (specFirst (g W) u) - coneIntegral h W e (fsLog h u)) =
      (Z W : ℝ) * (mahler h e (specFirst (g W) u') - coneIntegral h W e (fsLog h u')) := fun W hW => by
    have := _root_.GlobalTheory.CompanionTheory.Ar.Short.Crofton.defect_eq_of_linForm_notMem n e (d W) h W (g W) u u' (hd.prime W hW) (hg W hW).1 (hg W hW).2 (hu W hW)
      (hu' W hW)
    rw [this]
  rw [hsum u hu, hsum u' hu', Finset.sum_congr rfl hW]

theorem mahlerSection : GroundTheory.Heights₂.Heights.MahlerSection.Statement := by
  intro n e δ h Z f u hp hc hm ha
  exact GroundTheory.Heights₂.Heights.AutoClose.MahlerSectionOfConst e (defectConstDim e) n δ h Z f u ⟨hp, hc, hm⟩ ha

end GlobalTheory.CompanionTheory.Ar.Short
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SameGenericBaseExtensionStatement
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.same_generic_base_extension : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E E' : ChartBundle O (mseg x) N V), SameGeneric O x E E' → ∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) d → fnField O (joinCoord x z) = fnField O x → ∀ EB E'B : ChartBundle O (mseg (joinCoord x z)) N V, IsPull O x z E EB → IsPull O x z E' E'B → (∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d + 1 - k) → ck O (joinCoord x z) d N EB E'B k (fun j => pullDeg (K' := K') (L j)) Q = ck O x d N E E' k L Q) ∧ (∀ (c : ℕ) (G : MvPolynomial (Fin N) ℤ), G.IsSymmetric → G.IsHomogeneous c → c ≤ d → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d - c) → ∀ a : O, a ≠ 0 → rootNum O (joinCoord x z) d N EB G (fun j => pullDeg (K' := K') (L j)) Q a = rootNum O x d N E G L Q a) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CkPullBirat.main | exact GlobalTheory.CompanionTheory.Ar.CkPullBirat.main | (intros; apply GlobalTheory.CompanionTheory.Ar.CkPullBirat.main <;> assumption)
end

