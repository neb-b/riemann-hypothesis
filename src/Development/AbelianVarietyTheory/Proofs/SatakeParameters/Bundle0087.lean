module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
public import Formalism.LocalToGlobal.KernelLattices.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0084
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0086
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0008
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.FrobeniusOrbits.HostCorollaries
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0012
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.Bundle0001
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.KJoint
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.TransW
public import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.FinalD
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KurComplete
public import Formalism.LocalRingCardinality.DataKerI
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DatumCurveIntegralUnitDiscModel
public import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Th0TranslateProduct
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotRedOfMem
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassPAddOfNeOfDerivNeZero
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaloisTorsionConjugacy.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0015
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTaylorCoeffAlgebraicAndConjugate
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodLatticeSesquilinearFormIsHerm
public import Formalism.LocalToGlobal.TorsionIntegrality.ComplexLatticeClosure.LatticeAreaPositivity.ThetaTranslationOperatorApply

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AtLinAdaptedCoefEqStandardSeries
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical

namespace GlobalTheory

theorem atLin_adCoef_eq_stdSer : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N N' : ℕ) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E) (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]), atLin (Formalism.L2.Ker.adCoef lam P P') (fun j => MvPowerSeries.X j) F = stdSer D lam (fun _ => 1) P P' F := by
  intro D p _ lam N N' P P' F
  unfold stdSer
  congr 1
  funext k j
  rw [one_mul]
  unfold Formalism.L2.Ker.adCoef chgB
  dsimp only
  split_ifs with h
  · rw [h]
  · rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CmLatticeGoodModelUnramifiedStatement
section
open NumberField IsDedekindDomain Neutral.HilbertClassField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmLattice_good_model_unramified : (∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω], ∃ art : (Ω ≃ₐ[E] Ω) →* ClassGroup (𝓞 E), IsOpen (art.ker : Set (Ω ≃ₐ[E] Ω)) ∧ (∀ (A : ValuationSubring Ω) (g : Ω ≃ₐ[E] Ω), ReciprocityTheory.ChartRestriction.L1.InertiaEl A g → art g = 1) ∧ ∀ (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (φ : Ω ≃ₐ[E] Ω), LiesAbove A v → IsArithFrobenius A v φ → art φ = ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩) → ReciprocityTheory.ChartRestriction.L1.ChebOmSt → Formalism.L2.Th1.CM.CM2 := by
  first | exact @GlobalTheory.ArtinClassCM.good_model | exact GlobalTheory.ArtinClassCM.good_model | (intros; apply GlobalTheory.ArtinClassCM.good_model <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HodgeTateJumpsCoefficientExtensionStatement
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeTateJumps_coefExt_of_roomy_adm7 : ∀ {D : D7} (L : SizeData₂ D) (C₀ : ℝ) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw), Roomy L C₀ → LocalSituation.adm7 D → (∀ i, TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i) → LJ.ConclusionJa D → RecS.PtIn i r ρ π → ∃ (ε : ℤˣ) (κ : D.host.E →+* ↥Cx.LL.1), JumpIn (D.loc (D.nd.l i)) (K := (D.nbr i w hw).Kw) D (liftIdx D i) ε (Br.cEw D.nbr i w hw) κ (fun x => TruncatedSeriesCountingIdentities.locC Cx (rDuO D.nd i r x)) (TruncatedSeriesCountingIdentities.locC Cx (T2O D.nd i ρ π)) := by
  first | exact @GlobalTheory.HTW.Rec.hodgeTateJumps_coefficientExtension | exact GlobalTheory.HTW.Rec.hodgeTateJumps_coefficientExtension | (intros; apply GlobalTheory.HTW.Rec.hodgeTateJumps_coefficientExtension <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntSExpMulTranslate
section
noncomputable section

open scoped BigOperators
open Formalism.L2.Th1
open Formalism.L2.Th1.CM (HasCMBy omegaK)
open Formalism.L2.Th1.E (IntCurve Unif)
open Formalism.L2.Th1.A (logSer expSer wpReg)
open Formalism.L2.Th1.D (normInt)
open Formalism.G (unitBall)

namespace GlobalTheory.ThLoc

theorem endoDatum_of_model (d : ℕ) (L : PeriodPair) (hmod : d % 4 = 3) (hCM : HasCMBy d L)
    (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (W : WeierstrassCurve ℂ_[p]) (hU : Unif p L ι W)
    (hW : IntCurve W) (m n : ℤ) (hN : ¬ (p : ℤ) ∣ normInt d m n) :
    ∃ (S : Finset ℂ) (neg : S → S) (xP yP : S → ℂ_[p]),
      C.IsEndoCurve W neg xP yP (ι ((m : ℂ) + (n : ℂ) * omegaK d)) ∧
      (∀ P, ‖xP P‖ ≤ 1) ∧ (∀ P, ‖yP P‖ ≤ 1) ∧
      ι ((m : ℂ) + (n : ℂ) * omegaK d) * ι ((m : ℂ) + (n : ℂ) * (1 - omegaK d)) =
        (Fintype.card S : ℂ_[p]) + 1 ∧
      ι ((m : ℂ) + (n : ℂ) * omegaK d) *
          (ι ((m : ℂ) + (n : ℂ) * omegaK d) - ι ((m : ℂ) + (n : ℂ) * (1 - omegaK d))) *
          ι (F.s2 L) = ∑ P, (xP P + W.b₂ / 12) := by
  have hN0 : normInt d m n ≠ 0 := by
    intro h
    apply hN
    rw [h]
    exact dvd_zero _
  obtain ⟨S, neg, hcard, hker, hnegP, hE, hprod, hs2C⟩ := D.CurveNormEndomorphisms.cdata L hmod hCM m n hN0
  have hpN : ¬ p ∣ (S.card + 1) := by
    intro h
    apply hN
    rw [← hcard]
    exact_mod_cast h
  have hpt : ∀ P : S, E.ptW p L ι W (P : ℂ) =
      .some _ _ (E.AnaSysW.nonsing hU (P : ℂ) (hker P).2) := by
    intro P
    unfold E.ptW
    rw [dite_eq_left ⟨(hker P).2, E.AnaSysW.nonsing hU (P : ℂ) (hker P).2⟩]
  have hint : ∀ P : S, ‖E.AnaSysW.xc p L ι W P‖ ≤ 1 ∧ ‖E.AnaSysW.yc p L ι W P‖ ≤ 1 := by
    intro P
    have h := E.TransW.ptW_int E.analytic_point_map_add E.analytic_point_eq_zero_iff hU hW (P : ℂ) (S.card + 1) hpN
      (hker P).1 (hker P).2
    rw [hpt P] at h
    exact h
  refine ⟨S, neg, fun P => E.AnaSysW.xc p L ι W P, fun P => E.AnaSysW.yc p L ι W P,
    ?_, fun P => (hint P).1, fun P => (hint P).2, ?_, ?_⟩
  · apply D.CurveNormEndomorphisms.endoCurve_of_endoZ (RingHom.id ℂ_[p]) W
      (wF := fun P : S => PowerSeries.map (ι : ℂ →+* ℂ_[p])
        (F.taylor0 (fun z => L.weierstrassP (z + (P : ℂ)))))
    · intro P
      exact (E.AnaSysW.nonsing hU (P : ℂ) (hker P).2).1
    · intro P
      constructor
      · simp only [E.AnaSysW.xc, (hnegP P).1]
      · simp only [WeierstrassCurve.Affine.negY, E.AnaSysW.xc, E.AnaSysW.yc]
        rw [(hnegP P).2, (hnegP P).1, map_neg]
        ring
    · have h := D.CurveNormEndomorphisms.isEndoZ_map (ι : ℂ →+* ℂ_[p]) hE
      simp only [PowerSeries.map_id, RingHom.id_apply, E.AnaSysW.xc, sub_add_cancel]
      rw [E.weierstrass_series_eq_transported p L ι W hU]
      exact h
  · rw [← map_mul, hprod, Fintype.card_coe]
    simp
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [← map_sub, ← map_mul, ← map_mul, hs2C, map_sum]
      simp [E.AnaSysW.xc]

theorem jets_phW_three (d : ℕ) (L : PeriodPair) (hmod : d % 4 = 3) (h3 : d % 3 = 2) (hCM : HasCMBy d L)
    (ι : ℂ ≃+* ℂ_[3]) (W : WeierstrassCurve ℂ_[3]) (hU : Unif 3 L ι W) (hW : IntCurve W)
    (i : ℕ) (hi : 1 ≤ i) : ‖C.jet (logSer W) (E.phW 3 L ι W) i‖ ≤ 1 := by
  have hnorm : normInt d (-1) 2 = d := by
    obtain ⟨k, hk⟩ : ∃ k : ℤ, (d : ℤ) + 1 = 4 * k := ⟨((d : ℤ) + 1) / 4, by omega⟩
    have hdiv : ((d : ℤ) + 1) / 4 = k := by omega
    unfold normInt
    rw [hdiv]
    linear_combination -hk
  have hN : ¬ ((3 : ℕ) : ℤ) ∣ normInt d (-1) 2 := by
    rw [hnorm]
    omega
  obtain ⟨S, neg, xP, yP, hE, hx, hy, hprod, hs⟩ :=
    endoDatum_of_model d L hmod hCM 3 ι W hU hW (-1) 2 hN
  set al := ι (((-1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * omegaK d) with hal
  set albar := ι (((-1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * (1 - omegaK d)) with halbar
  have hsum : al + albar = ((0 : ℤ) : ℂ_[3]) := by
    rw [hal, halbar, ← map_add (f := _)]
    have e : (((-1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * omegaK d) +
        (((-1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * (1 - omegaK d)) = 0 := by
      push_cast
      ring
    rw [e]
    simp
  have hsq : al ^ 2 = -(d : ℂ_[3]) := by
    rw [hal, ← map_pow]
    have e : (((-1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * omegaK d) ^ 2 = -(d : ℂ) := by
      push_cast
      linear_combination 4 * D.CurveNormEndomorphisms.omega_sq d
    rw [e, map_neg, map_natCast]
  have h2 : ‖(2 : ℂ_[3])‖ = 1 := Top.OrthogonalGaussModelNormLemmas.norm_two 3 (by norm_num)
  have hal1 : ‖al‖ = 1 := by
    have h1 := congrArg norm hsq
    rw [norm_pow, norm_neg, E.ScaledModelNorms.norm_nat 3 (show ¬ 3 ∣ d by omega)] at h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h1
  have hdiff : ‖al - albar‖ = 1 := by
    have e : al - albar = 2 * al := by
      have := hsum
      push_cast at this
      linear_combination -this
    rw [e, norm_mul, h2, hal1, one_mul]
  have hb : ‖(al ^ 2 - 1) * (W.b₂ / 12)‖ ≤ 1 := by
    obtain ⟨k, hk⟩ : ∃ k : ℕ, d + 1 = 3 * k := ⟨(d + 1) / 3, by omega⟩
    have hk' : (d : ℂ_[3]) + 1 = 3 * (k : ℂ_[3]) := by exact_mod_cast hk
    have e : (al ^ 2 - 1) * (W.b₂ / 12) = -((k : ℂ_[3]) * W.b₂) / 2 ^ 2 := by
      rw [hsq]
      linear_combination (-W.b₂ / 12) * hk'
    have hb2 : ‖W.b₂‖ ≤ 1 := by
      have hm : W.b₂ ∈ unitBall ℂ_[3] := by
        obtain ⟨a1, a2, -⟩ := Top.OrthogonalGaussModelNormLemmas.coeffIn hW
        unfold WeierstrassCurve.b₂
        exact add_mem (pow_mem a1 2) (mul_mem (ofNat_mem _ 4) a2)
      exact hm
    rw [e, norm_div, norm_pow, h2, one_pow, div_one, norm_neg, norm_mul]
    exact mul_le_one₀ (IsUltrametricDist.norm_natCast_le_one _ k) (norm_nonneg _) hb2
  have h := G.curveJetsUnramThm ℂ_[3] W (Top.OrthogonalGaussModelNormLemmas.coeffIn hW) h2 (ι (F.s2 L)) al albar 0 S neg xP yP
    hE hx hy hprod hal1 hsum hdiff hb hs i hi
  unfold E.phW
  rw [← E.weierstrass_series_eq_transported 3 L ι W hU]
  exact h

theorem intS_exp_mul_translate (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (L : PeriodPair) (ι : ℂ ≃+* ℂ_[p])
    (W : WeierstrassCurve ℂ_[p]) (hU : Unif p L ι W) (hW : IntCurve W) (ω₀ : ℂ) (hω : ω₀ ∈ L.lattice)
    (hω2 : ω₀ / 2 ∉ L.lattice) (s : ℂ) (N : ℕ) (hN : 0 < N) (hlN : ¬ p ∣ N)
    (hNs : (N : ℂ) * s ∈ L.lattice) :
    E.IntS (B.fExp (E.phW p L ι W) * E.inW p ι W (F.opU L s (F.th0 L (ω₀ / 2)))) := by
  have hl2' : ¬ p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h)
  have h2t : ((2 : ℕ) : ℂ) * (ω₀ / 2) ∈ L.lattice := by simpa using E.TransW.half_mem hω 1
  obtain ⟨hc1, -⟩ := E.analytic_translate_model p L ι W hU hW (ω₀ / 2) 2 (by norm_num) hl2' h2t hω2
  have hN2 : ¬ p ∣ 2 * N := fun h => ((Nat.Prime.dvd_mul Fact.out).1 h).elim hl2' hlN
  have m3 : ((2 * N : ℕ) : ℂ) * (s + ω₀ / 2) ∈ L.lattice := by
    rw [mul_add]
    exact add_mem (E.TransW.two_mem hNs) (E.TransW.half_mem hω N)
  have hsim := (E.TransW.hW_sim p L ι W (ω₀ / 2) s (2 * N) (by omega) (E.TransW.two_mem hNs)
    (E.TransW.half_mem hω N) hω2).mul_left (B.fExp (E.phW p L ι W))
  refine (hsim.gaussOne ?_).1
  rw [mul_left_comm, ← E.TransW.gW_eq]
  exact E.Tor.gaussOne_C_mul (by rw [norm_inv, hc1, inv_one])
    (E.TransW.gW_gauss E.analytic_translate_system_model E.analytic_point_map_add E.analytic_point_eq_zero_iff hU hW _ (2 * N) hN2 m3)

theorem thetaZJetsThree : ThetaZJetsThree := by
  intro d L hd8 hd3 hCM ι W hU hW ω₀ hω h1 _ n _ κ _ r s N hr hN h3N hs
  have hω2 : ω₀ / 2 ∉ L.lattice := fun h => h1 (hCM _ h)
  obtain ⟨hlp, -, -, -, hu⟩ := C.curveFrame ℂ_[3] (unitBall ℂ_[3]) W (Top.OrthogonalGaussModelNormLemmas.coeffIn hW)
  have hph : PowerSeries.constantCoeff (E.phW 3 L ι W) = 0 := E.AnaSysW.cc_phW 3 L ι W
  obtain ⟨e1, hInt⟩ := E.prodInt ℂ_[3] κ n (E.phW 3 L ι W) r
    (fun k i => B.fExp (E.phW 3 L ι W) * E.inW 3 ι W (F.opU L (s k i) (F.th0 L (ω₀ / 2))))
    hph hr (fun k i => intS_exp_mul_translate 3 (by norm_num) L ι W hU hW ω₀ hω hω2 (s k i) N hN h3N
      (hs k i))
  have key := (G.kernelTwo ℂ_[3] _ _ _ hlp hu hph
    (jets_phW_three d L (by omega) hd3 hCM ι W hU hW) n (fun _ => 1) (fun _ => by simp) _
    (fun m => hInt m)).1
  obtain ⟨hl0, -, hv0, -, hlv⟩ := hlp
  rw [Top.KJ.phSum_one] at key
  change Formalism.DworkPowerSeriesWeights.JetsIntegral (G.toZ _ (Formalism.DworkPowerSeriesWeights.mvExp _ * _)) at key
  rw [← e1, Top.KJ.toZ_thetaProd hv0] at key
  convert key using 1
  unfold Top.thetaZ
  congr 1
  funext k i
  change _ = PowerSeries.subst _ (B.fExp (-(E.phW 3 L ι W)) * _)
  rw [← mul_assoc, ← B.fExp_add (by rw [map_neg]; exact neg_eq_zero.2 hph) hph,
    neg_add_cancel, B.ParO.fExp_zero, one_mul]
  unfold E.inW
  rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hl0)
    (PowerSeries.HasSubst.of_constantCoeff_zero' hv0), hlv]
  exact (PowerSeries.X_subst _).symm

end GlobalTheory.ThLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralWOfMulEqOne
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Classical

namespace GlobalTheory.CompareInert

section Letters

variable (D : D7) (p : ℕ) [Fact p.Prime]

variable {D p}

end Letters

section Rings

open Formalism.MainNotions.GL3Theta

variable {l : ℕ} [Fact l.Prime]

theorem mem_Wp_of_kur {x : ℂ_[l]} (hx : x ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension l) (h1 : ‖x‖ ≤ 1) : x ∈ Wp l := by
  have hp : l.Prime := Fact.out
  have hB := ((Formalism.L2.Th1.D.kurIntegers l).1 x).2 ⟨hx, h1⟩
  have hS : Formalism.L2.Th1.D.muPrime l = {ζ : ℂ_[l] | ∃ n : ℕ, 0 < n ∧ Nat.Coprime n l ∧ ζ ^ n = 1} := by
    ext ζ
    simp only [Formalism.L2.Th1.D.muPrime, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨n, h0, hn, h⟩
      exact ⟨n, h0, Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hn), h⟩
    · rintro ⟨n, h0, hn, h⟩
      exact ⟨n, h0, (Nat.Prime.coprime_iff_not_dvd hp).mp (Nat.coprime_comm.mp hn), h⟩
  unfold Formalism.L2.Th1.D.ringB Formalism.L2.Th1.D.ringA at hB
  rw [hS] at hB
  exact hB

theorem Wp_subset_Kur {x : ℂ_[l]} (hx : x ∈ Wp l) : x ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension l := by
  refine closure_mono (s := ((Subring.closure {ζ : ℂ_[l] | ∃ n : ℕ, 0 < n ∧ Nat.Coprime n l ∧ ζ ^ n = 1} : Subring ℂ_[l]) : Set ℂ_[l])) ?_ hx
  intro y hy
  have hle : Subring.closure {ζ : ℂ_[l] | ∃ n : ℕ, 0 < n ∧ Nat.Coprime n l ∧ ζ ^ n = 1} ≤
      (Subfield.closure {ζ : ℂ_[l] | ∃ n : ℕ, 0 < n ∧ ¬ l ∣ n ∧ ζ ^ n = 1}).toSubring := by
    refine Subring.closure_le.2 ?_
    rintro ζ ⟨n, h0, hn, h⟩
    exact Subfield.subset_closure ⟨n, h0, (Nat.Prime.coprime_iff_not_dvd Fact.out).mp (Nat.coprime_comm.mp hn), h⟩
  exact hle hy

theorem exists_pow_norm_le {K : Type*} [NormedField K] {a : K} (ha : ‖a‖ < 1) (x : K) : ∃ k : ℕ, ‖a ^ k * x‖ ≤ 1 := by
  by_cases hr : x = 0
  · exact ⟨0, by simp [hr]⟩
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (inv_pos.2 (norm_pos_iff.2 hr)) ha
  refine ⟨k, ?_⟩
  rw [norm_mul, norm_pow]
  have h0 : 0 < ‖x‖ := norm_pos_iff.2 hr
  calc ‖a‖ ^ k * ‖x‖ ≤ ‖x‖⁻¹ * ‖x‖ := by gcongr
    _ = 1 := inv_mul_cancel₀ h0.ne'

theorem norm_l_lt : ‖(l : ℂ_[l])‖ < 1 := by
  have h : ‖(l : ℂ_[l])‖ = ‖(l : ℚ_[l])‖ := by
    rw [← map_natCast (algebraMap ℚ_[l] ℂ_[l]) l]
    exact norm_algebraMap' ℂ_[l] _
  rw [h]
  exact Padic.norm_p_lt_one

end Rings

section Props

open Formalism.MainNotions.GL3Theta MvPowerSeries

variable {l d : ℕ} [Fact l.Prime] [NeZero d]

end Props

section Sign

open Formalism.MainNotions.GL3Theta MvPowerSeries

variable {l d : ℕ} [Fact l.Prime] [NeZero d]

end Sign

section Reps

variable (D : D7) (p : ℕ)

end Reps

section Hyp

end Hyp

section Statements

variable {D : D7} {Dx : DivX D} {Tw : TwForms D}

end Statements

section Units

open MvPowerSeries

variable {D : D7} {p : ℕ} [Fact p.Prime]

end Units

section Direction

open GlobalTheory.InertCompare GlobalTheory.Proof.IdempotentLatticeSequence

variable (D : D7) {l : ℕ} [Fact l.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[l])

end Direction

section Main

variable (D : D7) {Dx : DivX D} {Tw : TwForms D}

end Main

end GlobalTheory.CompareInert
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MonomialParamAsLogSeries
section
noncomputable section

namespace GlobalTheory.TwU

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

theorem inParam_eq_subst_log (p : ℕ) [Fact p.Prime] {ι : Type} (f : MvPowerSeries ι (K0 p)) :
    inParam p f = MvPowerSeries.subst (Formalism.MainNotions.FormalGroupSystem.Pf.en_aL p (K0 p)) f := by
  have h : Formalism.MainNotions.FormalGroupSystem.Pf.en_L p (K0 p) = logF p := by
    ext k; simp [Formalism.MainNotions.FormalGroupSystem.Pf.en_L]
  unfold inParam Formalism.MainNotions.FormalGroupSystem.Pf.en_aL
  rw [h]

theorem monomial_param_as_log_series : ∀ (p : ℕ) [Fact p.Prime] (ι : Type) [Fintype ι] (n : ι →₀ ℕ),
    ∃ U : MvPowerSeries ι (K0 p), inParam p U = MvPowerSeries.monomial n 1 ∧
      (∀ m : ι →₀ ℕ, m.degree < n.degree → MvPowerSeries.coeff m U = 0) := by
  intro p _ ι _ n
  have hs := Formalism.MainNotions.FormalGroupSystem.Pf.en_Ec_hs p (K0 p) (ι := ι)
  have hl := Formalism.MainNotions.FormalGroupSystem.Pf.en_aL_hs p (K0 p) (ι := ι)
  refine ⟨MvPowerSeries.subst (Formalism.MainNotions.FormalGroupSystem.Pf.en_Ec p (K0 p)) (MvPowerSeries.monomial n (1 : K0 p)), ?_, ?_⟩
  · rw [inParam_eq_subst_log, MvPowerSeries.subst_comp_subst_apply hs hl]
    simp only [Formalism.MainNotions.FormalGroupSystem.Pf.en_aL_Ec]
    rw [MvPowerSeries.subst_self]
    rfl
  · intro m hm
    apply MvPowerSeries.coeff_of_lt_order
    refine lt_of_lt_of_le (Nat.cast_lt.mpr hm) ?_
    rw [MvPowerSeries.subst_monomial hs, map_one, one_mul, Finsupp.prod]
    refine le_trans ?_ (MvPowerSeries.le_order_prod _ _)
    have hd : n.degree = ∑ i ∈ n.support, n i := rfl
    rw [hd, Nat.cast_sum]
    exact Finset.sum_le_sum fun s _ =>
      MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero _ (Formalism.MainNotions.FormalGroupSystem.Pf.en_Ec_zero p (K0 p) s)

end GlobalTheory.TwU

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaZeroPeriodLatticeEq
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators ComplexConjugate

namespace GlobalTheory.JetsGenusOne

theorem sgStar_eq (L : PeriodPair) : TaylorLogMetric.sgStar L.lattice.toAddSubgroup = Formalism.L2.Th1.F.sgStar L := by
  rw [GlobalTheory.OddTheta.sgStar_eq L _ (fun _ => Iff.rfl), GlobalTheory.Mem.Col2.ThetaVec.sgStar_eq]

end GlobalTheory.JetsGenusOne

namespace GlobalTheory.JetsGenusOne

end GlobalTheory.JetsGenusOne
end

