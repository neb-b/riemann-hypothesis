module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1277
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0012
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeanLogPeriodConjugatesEqChowlaSelberg
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ExistsPowPrincipalFractionalIdeal
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0039
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import GroundTheory.GlobalFields.TateThesis.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1276
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistContinuousInvolutionIntegralProperties
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

namespace GlobalTheory.BCT.ThBasic

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cj_mem_integers (hU : Unr E) (w : Pl E) (x : w.adicCompletion E) (hx : x ∈ Ov E w) : cj w x ∈ Ov E w := by
  have h := (_root_.GlobalTheory.ConjAtPlace.main E hU w).2.2.1 x
  change Valued.v (cj w x) ≤ 1
  rw [h]; exact hx

theorem thL_thL (hU : Unr E) (n : ℕ) (w : Pl E) (g : GLw n w) : thL n w (thL n w g) = g := by
  unfold thL
  split_ifs
  · rfl
  · exact GlobalTheory.ThetaPull.thetaGL_thetaGL _ (_root_.GlobalTheory.ConjAtPlace.main E hU w).2.1 g

theorem continuous_thL (hU : Unr E) (n : ℕ) (w : Pl E) : Continuous (thL n w) := by
  unfold thL
  split_ifs
  · exact continuous_id
  · exact GlobalTheory.ThetaPull.continuous_thetaGL _ (_root_.GlobalTheory.ConjAtPlace.main E hU w).1

theorem thL_mem_KGL (hU : Unr E) (n : ℕ) (w : Pl E) (k : GLw n w) (hk : k ∈ GlobalTheory.LFun.KGL w (n := n)) :
    thL n w k ∈ GlobalTheory.LFun.KGL w (n := n) := by
  unfold thL
  split_ifs
  · exact hk
  · obtain ⟨k', rfl⟩ := hk
    let c' : Ov E w →+* Ov E w := (cj w).restrict (Ov E w) (Ov E w) (cj_mem_integers hU w)
    refine ⟨thetaGL n c' k', ?_⟩
    exact GlobalTheory.ThetaPull.map_thetaGL (Ov E w).subtype c' (cj w) (fun x => rfl) k'

theorem nrmL_twist (hU : Unr E) (n : ℕ) (w : Pl E) (g y : GLw n w) :
    nrmL n w (g⁻¹ * y * thL n w g) = g⁻¹ * nrmL n w y * g := by
  unfold nrmL
  have h2 := thL_thL hU n w g
  unfold thL at h2 ⊢
  split_ifs with hs
  · simp [hs] at *
  · simp only [hs, if_false] at h2 ⊢
    rw [map_mul, map_mul, map_inv, h2]
    group

theorem isClosed_UL (hU : Unr E) (n : ℕ) (w : Pl E) : IsClosed (UL n w : Set (GLw n w)) := by
  unfold UL
  split_ifs
  · exact isClosed_univ
  · have hc := (_root_.GlobalTheory.ConjAtPlace.main E hU w).1
    have : Continuous fun g : GLw n w => cT (cj w) (g : Matrix (Fin n) (Fin n) _) * 1 * (g : Matrix (Fin n) (Fin n) _) := by
      refine Continuous.mul (Continuous.mul ?_ continuous_const) Units.continuous_val
      exact continuous_matrix fun i j => hc.comp (Units.continuous_val.matrix_elem _ _)
    exact isClosed_singleton.preimage this

theorem charpoly_nrmL (hU : Unr E) (n : ℕ) (w : Pl E) (δ : GL (Fin n) E) :
    (nrmL n w (locEl n w δ)).val.charpoly = atPl w (δ * thE E n δ).val.charpoly := by
  unfold nrmL locEl
  split_ifs with hs
  · exact (Matrix.charpoly_map _ _)
  · have hm : thetaGL n (cj w) (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ) =
        GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) (thE E n δ) :=
      (GlobalTheory.ThetaPull.map_thetaGL _ _ _ (fun x => ((_root_.GlobalTheory.ConjAtPlace.main E hU w).2.2.2.1 hs).1 x |>.symm) δ).symm
    rw [hm, ← map_mul]
    exact (Matrix.charpoly_map _ _)

theorem cLoc_mem_UL (hU : Unr E) (n : ℕ) (w : Pl E) (x : UA E n) : cLoc w x ∈ UL n w := by
  unfold UL
  split_ifs with hs
  · exact Subgroup.mem_top _
  · have hp := ((_root_.GlobalTheory.ConjAtPlace.main E hU w).2.2.2.1 hs).2.2.1
    have hx := x.2
    change cT (conjAd E) (x.1 : Matrix (Fin n) (Fin n) (Ad E)) * 1 * (x.1 : Matrix (Fin n) (Fin n) (Ad E)) = 1 at hx
    change cT (cj w) ((cLoc w x : GLw n w) : Matrix (Fin n) (Fin n) _) * 1 * ((cLoc w x : GLw n w) : Matrix (Fin n) (Fin n) _) = 1
    have := congrArg (((pLoc E w).comp (pFin E)).mapMatrix) hx
    rw [map_one, map_mul, map_mul, map_one] at this
    convert this using 3
    · refine Matrix.ext fun i j => ?_
      show cj w (pLoc E w (pFin E ((x.1 : Matrix (Fin n) (Fin n) (Ad E)) j i))) =
        pLoc E w (pFin E (conjAd E ((x.1 : Matrix (Fin n) (Fin n) (Ad E)) j i)))
      rw [← hp]
      rfl
    · rfl

theorem twist_basic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E), Continuous (thL n w) ∧ (∀ g, thL n w (thL n w g) = g) ∧ (∀ k ∈ GlobalTheory.LFun.KGL w (n := n), thL n w k ∈ GlobalTheory.LFun.KGL w (n := n)) ∧ (∀ g y, nrmL n w (g⁻¹ * y * thL n w g) = g⁻¹ * nrmL n w y * g) ∧ IsOpen (GlobalTheory.LFun.KGL w (n := n) : Set (GLw n w)) ∧ IsCompact (GlobalTheory.LFun.KGL w (n := n) : Set (GLw n w)) ∧ IsOpen (KL n w : Set (UL n w)) ∧ IsCompact (KL n w : Set (UL n w)) ∧ (∀ δ : GL (Fin n) E, (nrmL n w (locEl n w δ)).val.charpoly = atPl w (δ * thE E n δ).val.charpoly) ∧ ∀ x ∈ locU n w, cLoc w x ∈ UL n w := by
  intro E _ _ _ hU n w
  have hK := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n
  refine ⟨continuous_thL hU n w, thL_thL hU n w, thL_mem_KGL hU n w, nrmL_twist hU n w, hK.1, hK.2, ?_, ?_,
    charpoly_nrmL hU n w, fun x _ => cLoc_mem_UL hU n w x⟩
  · rw [KL, Subgroup.coe_subgroupOf]
    exact hK.1.preimage continuous_subtype_val
  · rw [KL, Subgroup.coe_subgroupOf]
    exact (isClosed_UL hU n w).isClosedEmbedding_subtypeVal.isCompact_preimage hK.2

end GlobalTheory.BCT.ThBasic
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanLogPeriodChowlaSelberg
section
noncomputable section

namespace GlobalTheory.MeanPeriodClosed

open NumberField Formalism.BasicNotions
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5 (brN br_meanLogOm_eq br_b_spec absNorm_inv_mul_different natAbs_discr_eq
  discr_K discriminant_mod_four br_sqrt_sq br_finrank_K br_finrank_E)

theorem two_log_brN (D : D7) :
    (2 / (Module.finrank ℚ D.host.E : ℝ)) * Real.log (brN D) =
      Real.log D.host.rdE - Real.log (Real.sqrt (D.host.d : ℝ)) := by
  haveI : Fact D.host.d.Prime := ⟨D.host.hyp.2.1⟩
  have hd0 : (0 : ℝ) < D.host.d := by exact_mod_cast D.host.hyp.2.1.pos
  have hdK : NumberField.discr D.host.K = -(D.host.d : ℤ) :=
    discr_K D.host.K D.host.d (discriminant_mod_four D) _ (br_sqrt_sq D) (br_finrank_K D)
  have h1 := absNorm_inv_mul_different D.host.K D.host.E D.host.conj D.host.𝔟 (br_b_spec D)
  have h2 := natAbs_discr_eq D.host.K D.host.E D.host.d hdK
  set A : ℝ := (Ideal.absNorm (differentIdeal (𝓞 D.host.K) (𝓞 D.host.E)) : ℝ) with hA
  have hsq : brN D ^ 2 = A := by
    have := congrArg (fun q : ℚ => (q : ℝ)) h1
    simp only [Rat.cast_pow, Rat.cast_natCast] at this
    rw [hA, ← this]
    rfl
  set m : ℕ := Module.finrank D.host.K D.host.E with hm
  have hE : Module.finrank ℚ D.host.E = 2 * m := br_finrank_E D
  have hm0 : (m : ℝ) ≠ 0 := by
    have : 0 < m := Module.finrank_pos
    exact_mod_cast this.ne'
  have hdisc : |(NumberField.discr D.host.E : ℝ)| = A * (D.host.d : ℝ) ^ m := by
    have := congrArg (fun n : ℕ => (n : ℝ)) h2
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_natAbs, Int.cast_abs] at this
    rw [hA, ← this]
  have hdisc0 : |(NumberField.discr D.host.E : ℝ)| ≠ 0 := by
    simpa using NumberField.discr_ne_zero D.host.E
  have hA0 : A ≠ 0 := fun h => hdisc0 (by rw [hdisc, h, zero_mul])
  have hlogA : 2 * Real.log (brN D) = Real.log A := by
    rw [← hsq, Real.log_pow]; push_cast; ring
  have hrd : Real.log D.host.rdE =
      (Real.log A + (m : ℝ) * Real.log D.host.d) / (2 * (m : ℝ)) := by
    unfold Formalism.BasicNotions.Host.rdE
    rw [Real.log_rpow (abs_pos.2 (by simpa using NumberField.discr_ne_zero D.host.E)), hdisc,
      Real.log_mul hA0 (pow_ne_zero _ hd0.ne'), Real.log_pow, hE]
    push_cast
    field_simp
  rw [hrd, Real.log_sqrt hd0.le, hE]
  push_cast
  field_simp
  linear_combination hlogA

theorem meanPeriodAt (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hcc : Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc)
    (hδ : Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) : GlobalTheory.IndefiniteRowSideFullHecke.MeanPeriodLogarithms.MeanPeriodAt D cc δ := by
  intro M _ hM τ
  have hc : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ := ⟨hcc, hδ⟩
  have hpos : ∀ ρ : M →ₐ[ℚ] ℂ,
      0 < Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.area (Formalism.MainNotions.TaylorLogMetric.lamConj M ρ (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ)) :=
    fun ρ => GlobalTheory.Glob.area_lamConj_pos hc hM ρ
  have hmean := GlobalTheory.PeriodMean.mean_log_period D (GlobalTheory.InducedType.induced_type D).1 cc δ hc M
    hM.2.1 hM.2.2
  have e := br_meanLogOm_eq D (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ) M hM.1 τ hpos
  have hN := two_log_brN D
  show Formalism.MainNotions.TaylorLogMetric.meanLogOm D (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ) M τ = Formalism.MainNotions.TaylorLogMetric.logOmVal D
  rw [e, GlobalTheory.IndefiniteRowSideFullHecke.MeanPeriodLogarithms.logOmVal_eq]
  have hmean' : (∑ ρ : M →ₐ[ℚ] ℂ, Real.log (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.area
      (Formalism.MainNotions.TaylorLogMetric.lamConj M ρ (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ)) / Real.pi)) / (Module.finrank ℚ M : ℝ) =
      Real.eulerMascheroniConstant + Real.log (2 * Real.pi / Real.sqrt D.host.d) -
        Formalism.MainNotions.TaylorLogMetric.logDerivativeAtOne D := hmean
  rw [hmean']
  have hd0 : (0 : ℝ) < Real.sqrt D.host.d := Real.sqrt_pos.2 (by exact_mod_cast D.host.hyp.2.1.pos)
  have hr0 : 0 < D.host.rdE := by
    unfold Formalism.BasicNotions.Host.rdE
    exact Real.rpow_pos_of_pos (abs_pos.2 (by simpa using NumberField.discr_ne_zero D.host.E)) _
  rw [Real.log_div (by positivity) hd0.ne', Real.log_div (by positivity) hr0.ne']
  rw [neg_mul, hN]
  ring

theorem meanPeriod : GlobalTheory.IndefiniteRowSideFullHecke.MeanPeriodLogarithms.MeanPeriod :=
  fun D cc δ hcc hδ => meanPeriodAt D cc δ hcc hδ

end GlobalTheory.MeanPeriodClosed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanLogSupNormLossLeLinearInWeight
section
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal

namespace GlobalTheory.LamSize

theorem one_le_fdeg_of_cm (E : Type) [Field E] [NumberField E] [IsCMField E] : 1 ≤ fdeg E := by
  have h : Module.finrank ℚ E = 2 * fdeg E := by rw [fdeg, IsTotallyComplex.finrank E]; omega
  have := Module.finrank_pos (R := ℚ) (M := E)
  omega

theorem one_le_dE_field (E : Type) [Field E] [NumberField E] : 1 ≤ dE E := by
  unfold dE
  have h := Int.one_le_abs (NumberField.discr_ne_zero E)
  rw [← Int.cast_abs]
  exact_mod_cast h

theorem neg_log_epStar_le (f M d w : ℝ) (hf : 1 ≤ f) (hM : 1 ≤ M) (hd : 1 ≤ d) (hw : 1 ≤ w) :
    0 < epStar (2 * M * Real.sqrt d) f w 1 ∧ epStar (2 * M * Real.sqrt d) f w 1 ≤ 1 ∧
      -Real.log (epStar (2 * M * Real.sqrt d) f w 1) ≤
        Real.log 2 + Real.log M + 1 / 2 * Real.log d + Real.log f + Real.log w := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hpi := Real.pi_gt_three
  have hsd : 1 ≤ Real.sqrt d := by rw [Real.one_le_sqrt]; exact hd
  have hfw : 1 ≤ f * w := one_le_mul_of_one_le_of_one_le hf hw
  set A := 2 * M * Real.sqrt d * f * w with hA
  have hA1 : 1 ≤ A := by
    have h1 : 1 ≤ M * Real.sqrt d := one_le_mul_of_one_le_of_one_le hM hsd
    have : A = 2 * (M * Real.sqrt d) * (f * w) := by rw [hA]; ring
    rw [this]; nlinarith
  have hA0 : 0 < A := by linarith
  have hB : 0 < 2 * M * Real.sqrt d * (f * w + 2) * 1 * Real.log 2 := by positivity
  have hlow : 1 / A ≤ epStar (2 * M * Real.sqrt d) f w 1 := by
    unfold epStar
    refine le_min ((div_le_one hA0).2 hA1) ?_
    rw [div_le_div_iff₀ hA0 hB]
    have hMd : 0 < 2 * M * Real.sqrt d := by positivity
    have key : (f * w + 2) * Real.log 2 ≤ Real.pi * (f * w) := by nlinarith
    have : 1 * (2 * M * Real.sqrt d * (f * w + 2) * 1 * Real.log 2) = (2 * M * Real.sqrt d) * ((f * w + 2) * Real.log 2) := by ring
    rw [this]
    have : Real.pi * A = (2 * M * Real.sqrt d) * (Real.pi * (f * w)) := by rw [hA]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left key hMd.le
  have he0 : 0 < epStar (2 * M * Real.sqrt d) f w 1 := lt_of_lt_of_le (by positivity) hlow
  refine ⟨he0, min_le_left _ _, ?_⟩
  have h1 : Real.log (1 / A) ≤ Real.log (epStar (2 * M * Real.sqrt d) f w 1) :=
    Real.log_le_log (by positivity) hlow
  rw [one_div, Real.log_inv] at h1
  have hlA : Real.log A = Real.log 2 + Real.log M + 1 / 2 * Real.log d + Real.log f + Real.log w := by
    rw [hA, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_sqrt (by linarith)]
    ring
  linarith

theorem log_radius_le (E : Type) [Field E] [NumberField E] [IsCMField E] (r d M : ℕ) (w L : ℝ)
    (hr : 1 ≤ r) (hd : 1 ≤ d) (hM : 1 ≤ M) (hL : 1 ≤ L) (hw : 1 ≤ w)
    (hfr : Real.log (fdeg E * r) ≤ L) (hlM : Real.log M ≤ 30 * L) (hdE : Real.log (dE E) ≤ 4 * fdeg E * L)
    (hld : Real.log d ≤ 4 * L) (hlw : Real.log w ≤ 2 * L) :
    1 ≤ 2 * ReciprocityTheory.MultiplicativeHeights.approxR r (d5mu (fdeg E) r (dE E) (Real.sqrt (epsLev E d M w) / Real.sqrt (fdeg E)))
      (3 * frameRadius w r / 5) ∧
    Real.log (2 * ReciprocityTheory.MultiplicativeHeights.approxR r (d5mu (fdeg E) r (dE E) (Real.sqrt (epsLev E d M w) / Real.sqrt (fdeg E)))
      (3 * frameRadius w r / 5)) ≤ (4 * fdeg E + 32) * L := by
  have hf1 := one_le_fdeg_of_cm E
  have hf' : (1 : ℝ) ≤ fdeg E := by exact_mod_cast hf1
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hdE1 := one_le_dE_field E
  obtain ⟨he0, he1, hne⟩ := neg_log_epStar_le (fdeg E) M d w hf' hM' hd' hw
  have hepsdef : epsLev E d M w = epStar (2 * M * Real.sqrt d) (fdeg E) w 1 := rfl
  rw [← hepsdef] at he0 he1 hne
  obtain ⟨hX0, hX⟩ := GlobalTheory.room_log_radius (fdeg E) r (dE E) (epsLev E d M w) w hf1 hr hdE1 he0 hw
  set X := 2 * ReciprocityTheory.MultiplicativeHeights.approxR r (d5mu (fdeg E) r (dE E) (Real.sqrt (epsLev E d M w) / Real.sqrt (fdeg E)))
    (3 * frameRadius w r / 5) with hXdef
  clear_value X
  have hle : Real.log (epsLev E d M w) ≤ 0 := Real.log_nonpos he0.le he1
  have hn : (1 : ℝ) ≤ (fdeg E : ℝ) * r := one_le_mul_of_one_le_of_one_le hf' hr'
  have a1 : 0 ≤ Real.log (dE E) := Real.log_nonneg hdE1
  have a2 : 0 ≤ Real.log w := Real.log_nonneg hw
  have a3 : 0 ≤ Real.log (fdeg E : ℝ) := Real.log_nonneg hf'
  have a4 : 0 ≤ Real.log (r : ℝ) := Real.log_nonneg hr'
  have a5 : 0 ≤ Real.log ((fdeg E : ℝ) * r) := Real.log_nonneg hn
  have a6 : 0 ≤ Real.log (1600 / 3 : ℝ) := Real.log_nonneg (by norm_num)
  have a7 : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg hM'
  have a8 : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg hd'
  have hmul : Real.log ((fdeg E : ℝ) * r) = Real.log (fdeg E : ℝ) + Real.log r :=
    Real.log_mul (by positivity) (by positivity)
  have hc : Real.log (1600 / 3 : ℝ) ≤ 7 := by
    have h1 : Real.log (1600 / 3 : ℝ) ≤ Real.log ((2 : ℝ) ^ 10) := Real.log_le_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at h1
    have := Real.log_two_lt_d9
    push_cast at h1
    linarith
  have hl2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hfdL : 0 ≤ (fdeg E : ℝ) * L := by positivity
  have hX1 : 0 ≤ Real.log X := by rw [hX]; linarith
  refine ⟨?_, ?_⟩
  · by_contra hc'
    have := Real.log_neg hX0 (not_le.1 hc')
    linarith
  · rw [hX]
    have : (4 * (fdeg E : ℝ) + 32) * L = 4 * ((fdeg E : ℝ) * L) + 32 * L := by ring
    rw [this]
    linarith

theorem lamSup_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r q d M : ℕ) (Om s t L : ℝ), 1 ≤ r → 1 ≤ d → 1 ≤ M → 1 ≤ L → 0 ≤ s → 0 ≤ t → Real.log (fdeg E * r) ≤ L → Real.log M ≤ 30 * L → Real.log (dE E) ≤ 4 * fdeg E * L → Real.log d ≤ 4 * L → Real.log (s + t + 1) ≤ 2 * L → lamSup E r q d M Om s t ≤ ((1 + |Om|) / 2 + L + (2 * q + 1) * (6 * fdeg E + 48) * L) * (s + t) := by
  intro E _ _ _ r q d M Om s t L hr hd hM hL hs ht hfr hlM hdE hld hlw
  have hw : (1 : ℝ) ≤ s + t + 1 := by linarith
  obtain ⟨hX1, hXle⟩ := log_radius_le E r d M (s + t + 1) L hr hd hM hL hw hfr hlM hdE hld hlw
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hcm : cmLen E r q d M (s + t + 1) = (2 * ReciprocityTheory.MultiplicativeHeights.approxR r (d5mu (fdeg E) r (dE E)
      (Real.sqrt (epsLev E d M (s + t + 1)) / Real.sqrt (fdeg E))) (3 * frameRadius (s + t + 1) r / 5)) ^ (2 * q + 1) := rfl
  unfold lamSup
  rw [hcm]
  set X := 2 * ReciprocityTheory.MultiplicativeHeights.approxR r (d5mu (fdeg E) r (dE E)
      (Real.sqrt (epsLev E d M (s + t + 1)) / Real.sqrt (fdeg E))) (3 * frameRadius (s + t + 1) r / 5) with hXdef
  clear_value X
  have hX0 : 0 < X := by linarith
  have hlX : 0 ≤ Real.log X := Real.log_nonneg hX1
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
  unfold Formalism.L2.LamCM.pDeg
  push_cast
  set K : ℝ := 2 * (q : ℝ) + 1 with hK
  have hK0 : 0 ≤ K := by positivity
  set Y := K * Real.log X with hY
  have hY0 : 0 ≤ Y := mul_nonneg hK0 hlX
  have hYle : Y ≤ K * ((4 * fdeg E + 32) * L) := mul_le_mul_of_nonneg_left hXle hK0
  have hlr : Real.log r ≤ L := by
    have hf' : (1 : ℝ) ≤ fdeg E := by exact_mod_cast one_le_fdeg_of_cm E
    have : Real.log (r : ℝ) ≤ Real.log ((fdeg E : ℝ) * r) :=
      Real.log_le_log (by positivity) (le_mul_of_one_le_left (by positivity) hf')
    linarith
  have a4 : 0 ≤ Real.log (r : ℝ) := Real.log_nonneg hr'
  have hst : 0 ≤ s + t := by linarith
  have c1 : s * (Real.log r + Y) ≤ (s + t) * (L + Y) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) hst
  have c2 : (3 / 2 * Y) * (s + t) ≤ (K * (6 * fdeg E + 48) * L) * (s + t) := by
    refine mul_le_mul_of_nonneg_right ?_ hst
    have : K * (6 * (fdeg E : ℝ) + 48) * L = 3 / 2 * (K * ((4 * fdeg E + 32) * L)) := by ring
    rw [this]; linarith
  nlinarith

end GlobalTheory.LamSize
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulusOfNormEqAbs
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ModuAdele

open scoped Pointwise

theorem distribHaarChar_adeleRing (K : Type) [Field K] [NumberField K] (a : (AdeleRing (𝓞 K) K)ˣ) :
    (distribHaarChar (AdeleRing (𝓞 K) K) a : ℝ) = (GroundTheory.Global.IdeleGroup.ideleModule K a : ℝ) := by
  letI : MeasurableSpace (AdeleRing (𝓞 K) K) := GroundTheory.Global.measurableSpace_adeleRing K
  obtain ⟨s, hsc, hs0⟩ : ∃ s : Set (AdeleRing (𝓞 K) K), IsCompact s ∧ s ∈ nhds (0 : AdeleRing (𝓞 K) K) :=
    exists_compact_mem_nhds 0
  have hpos : 0 ≤ (GroundTheory.Global.IdeleGroup.ideleModule K a : ℝ) := (GroundTheory.Global.IdeleGroup.ideleModule K a).2.le
  set r : NNReal := ⟨_, hpos⟩ with hr
  set μ := GroundTheory.Global.adeleMeasure K with hμ
  set ν : Measure (AdeleRing (𝓞 K) K) := Measure.addHaar with hν
  have e1 := Measure.measure_isAddInvariant_eq_smul_of_isCompact_closure μ ν hsc.closure
  have e2 := Measure.measure_isAddInvariant_eq_smul_of_isCompact_closure μ ν (hsc.smul a).closure
  have hm := GroundTheory.Global.adeleMeasure_smul a s
  set c := μ.addHaarScalarFactor ν
  have hμs : μ s ≠ 0 := (Measure.measure_pos_of_mem_nhds _ hs0).ne'
  have hνs : ν s ≠ 0 := (Measure.measure_pos_of_mem_nhds _ hs0).ne'
  have hνs' : ν s ≠ ⊤ := hsc.measure_lt_top.ne
  have hc : (c : ENNReal) ≠ 0 := by
    intro h0
    apply hμs
    rw [e1, ENNReal.smul_def, smul_eq_mul, h0, zero_mul]
  have h := distribHaarChar_eq_of_measure_smul_eq_mul (g := a) (μ := ν) (s := s) hνs hνs'
    (r := r) (by
      rw [e1, e2, ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul,
        ENNReal.ofReal_eq_coe_nnreal hpos] at hm
      have hm' : (c : ENNReal) * ν (a • s) = (c : ENNReal) * ((r : ENNReal) * ν s) := by
        calc (c : ENNReal) * ν (a • s) = (r : ENNReal) * ((c : ENNReal) * ν s) := hm
          _ = (c : ENNReal) * ((r : ENNReal) * ν s) := by ring
      exact (ENNReal.mul_right_inj hc ENNReal.coe_ne_top).1 hm')
  rw [h]
  rfl

end GlobalTheory.ModuAdele

theorem GlobalTheory.ModuAdele.modu_norm_eq_absE : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (x : (AE F E)ˣ),
    (adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F) x) = absE F E x := by
  intro F E _ _ _ _ _ x
  have hf : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      ‖evFin F v (Algebra.norm (AF F) x.1)‖₊).Finite := by
    simpa only [GlobalTheory.Doubling.absEv_unitFin] using GlobalTheory.Doubling.finite_mulSupport_absEv x
  apply NNReal.eq
  change (distribHaarChar (AdeleRing (𝓞 F) F) (Units.map (Algebra.norm (AF F) : AE F E →* AF F) x) : ℝ) = _
  rw [GlobalTheory.ModuAdele.distribHaarChar_adeleRing, GroundTheory.Global.IdeleGroup.ideleModule_eq, GlobalTheory.Doubling.absE_apply]
  simp only [GlobalTheory.Doubling.absEv_unitFin, GlobalTheory.Doubling.absEw_unitInf]
  rw [NNReal.coe_mul, NNReal.coe_prod]
  congr 1
  rw [show ((∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖evFin F v (Algebra.norm (AF F) x.1)‖₊ : ℝ≥0) : ℝ) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 F), ((‖evFin F v (Algebra.norm (AF F) x.1)‖₊ : ℝ≥0) : ℝ) from
      NNReal.toRealHom.toMonoidHom.map_finprod hf]
  rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NmatMulVec
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.UnipMass

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def hA (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v w : Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) :=
  v ⬝ᵥ (incM F J *ᵥ fun i => cA σ (w i))

def nmat (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x u : Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (c : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
  1 - Matrix.vecMulVec (u + c • x) (incM F J *ᵥ fun i => cA σ (x i)) -
    Matrix.vecMulVec x (incM F J *ᵥ fun i => cA σ (u i))

theorem nmat_mulVec (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x u : Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (c : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))
    (v : Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) : nmat σ J x u c *ᵥ v = v - hA σ J v x • (u + c • x) - hA σ J v u • x := by
  ext i
  simp only [nmat, hA, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, Matrix.vecMulVec_mulVec, Pi.smul_apply,
    smul_eq_mul, op_smul_eq_mul]
  rw [dotProduct_comm v, dotProduct_comm v]
  ring

end GlobalTheory.UnipMass
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NumConsEqMulOfEffectiveDivisorSuppSectionStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.num_cons_eq_mul_of_effective_divisor_supp_section : ∀ (F : Type) [Field F] (Y : Var F) (W : Dbl Y), W.Small → ∀ Θ : CartierDiv W.Z, Θ.Eff → (Θ.supp : Set W.Z) = Set.range W.δ → ∃ μ : ℤ, μ ≠ 0 ∧ ∀ y : Fin Y.dim → CartierDiv W.Z, letI := algebraΓOfHom (W.p₁ ≫ Y.str); W.num (Fin.cons Θ y : Fin (Y.dim + 1) → CartierDiv W.Z) = μ * interNumRed F (⟨closure {W.δ (genericPoint Y.X)}, isClosed_closure⟩ : Closeds W.Z) fun i => toLB (y i) := by
  first | exact @GlobalTheory.FlagPush.Dbl.num_cons_eq_mul_of_supp_eq_range | exact GlobalTheory.FlagPush.Dbl.num_cons_eq_mul_of_supp_eq_range | (intros; apply GlobalTheory.FlagPush.Dbl.num_cons_eq_mul_of_supp_eq_range <;> assumption)
end

